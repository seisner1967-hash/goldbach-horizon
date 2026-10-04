"""Supplementary exact filter for Agent 1's mixed-product differences.

This creates a separate receipt and preserves the main multifibre receipt.
"""
import sys
sys.dont_write_bytecode = True
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
from math import gcd

from multifibre_checks import N, ALPHA, ROOT, actual_term, factor, mu, sign_certificate, vector_add


def linear(vector):
    return {int(p):Fraction(c) for p,c in vector.items()}


def linear_add(target,source,scale=1):
    for p,c in source.items():
        target[p] = target.get(p,Fraction(0))+scale*c
        if target[p] == 0:
            del target[p]


def mixed_difference(vectors):
    out = {}
    for scale,vector in zip((1,-1,-1,1),vectors):
        linear_add(out,vector,scale)
    return out


def difference(left,right):
    out = dict(left)
    linear_add(out,right,-1)
    return out


def product(left,right):
    out = {}
    for p,c in left.items():
        for q,d in right.items():
            key = tuple(sorted((p,q)))
            out[key] = out.get(key,Fraction(0))+c*d
    return {key:c for key,c in out.items() if c}


def mangoldt_vector(n):
    fs = factor(n)
    return {fs[0][0]:Fraction(1)} if len(fs) == 1 else {}


def log_vector(n):
    return {p:Fraction(e) for p,e in factor(n)}


def check(base,p,q):
    multipliers = (1,p,q,p*q)
    metadata = [actual_term(base*d)[0] for d in multipliers]
    f = [linear(row['fII']) for row in metadata]
    B = [linear(row['D_minus_W']) for row in metadata]
    direct = {}
    for scale,fi,Bi in zip((1,-1,-1,1),f,B):
        vector_add(direct,product(fi,Bi),scale)
    rhs = product(B[0],mixed_difference(f))
    vector_add(rhs,product(f[3],mixed_difference(B)))
    vector_add(rhs,product(difference(f[3],f[1]),difference(B[1],B[0])))
    vector_add(rhs,product(difference(f[3],f[2]),difference(B[2],B[0])))
    assert direct == rhs
    n = tuple(N-base*d for d in multipliers)
    delta_lambda = mixed_difference([mangoldt_vector(ni) for ni in n])
    curvature_log = mixed_difference([log_vector(ni) for ni in n])
    curvature_log = {p:-c for p,c in curvature_log.items()}
    f_rhs = dict(delta_lambda)
    linear_add(f_rhs,curvature_log)
    assert mixed_difference(f) == f_rhs
    numerator,denominator = n[1]*n[2],n[0]*n[3]
    assert numerator-denominator == N*base*(p-1)*(q-1) > 0
    return direct,Fraction(numerator,denominator)


def run():
    main = ROOT/'multifibre_checks.py'
    receipt = ROOT/'multifibre.json'
    main_hash,receipt_hash = sha256(main.read_bytes()).hexdigest(),sha256(receipt.read_bytes()).hexdigest()
    p,q,cap = 3,7,20000
    counts = Counter()
    for base in range(1,cap//(p*q)+1):
        if gcd(base,N*p*q) != 1 or mu(base) == 0:
            continue
        if any(mu(N-base*d) == 0 for d in (1,p,q,p*q)):
            continue
        check(base,p,q)
        counts['actual_mixed_product_difference'] += 1
        counts['actual_fII_curvature_identity'] += 1
    direct,ratio = check(101,p,q)
    counts['complete_four_site_101_product_difference'] += 1
    # Actual block = mu(base)*Delta(fB). mu(101)=-1.
    block = {key:mu(101)*c for key,c in direct.items()}
    cert = sign_certificate(block)
    assert cert['sign'] == 'NEGATIVE'
    assert sha256(main.read_bytes()).hexdigest() == main_hash
    assert sha256(receipt.read_bytes()).hexdigest() == receipt_hash
    result = dict(status='PASS',N=N,alpha=ALPHA,p=p,q=q,cap=cap,checks=dict(counts),
                  domain='All 1<=base<=floor(20000/21) with gcd(base,N*21)=1, mu(base)!=0 and all four first axes squarefree',
                  E5='Delta(fB)=B1 Delta f+fpq Delta B+(fpq-fp)(Bp-B1)+(fpq-fq)(Bq-B1)',
                  E6='Delta fII=Delta Lambda+log((N-pb)(N-qb)/((N-b)(N-pqb)))',
                  curvature='Strictly positive smooth-log ratio by exact numerator-denominator = N*b*(p-1)*(q-1)>0',
                  base101_ratio=f'{ratio.numerator}/{ratio.denominator}',
                  base101_actual_block_certificate=cert,
                  main_script_sha256=main_hash,main_receipt_sha256=receipt_hash,
                  main_artifacts_preserved=True,
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Exact finite identities; all mixed terms are retained; no D_N estimate')
    (ROOT/'mixed_difference.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    run()
