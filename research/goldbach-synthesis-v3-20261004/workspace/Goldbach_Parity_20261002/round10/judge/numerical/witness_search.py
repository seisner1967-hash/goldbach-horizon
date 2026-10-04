"""Deterministic new round10 witnesses, with verified actual prime first axis."""
import sys
sys.dont_write_bytecode = True
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
from hashlib import sha256
from math import gcd
import json

ROOT = Path(__file__).resolve().parent
spec = spec_from_file_location('round10_shared_search', ROOT/'shared.py')
shared = module_from_spec(spec)
spec.loader.exec_module(shared)
N, A, Q = shared.N, 3163, 999999


def prime(n):
    return shared.factor(n) == ((n,1),)


def row(m, attempted, parameters):
    n = N-m
    assert 1<n<N and gcd(n,N)==1 and prime(n)
    return dict(m=m,n=n,m_factors=shared.factor(m),n_factors=shared.factor(n),
                mu_m=shared.mu(m),attempted=attempted,parameters=parameters)


def search():
    result = {}
    count=0
    for p in range(1000001,1100001,2):
        count += 1
        if prime(p) and prime(N-p):
            result['rough_prime_bulk']=row(p,count,dict(p=p,domain='odd p in [1000001,1099999]'))
            break
    assert 'rough_prime_bulk' in result
    pool=[p for p in shared.parity.PRIMES if p>A]
    p=pool[0]
    for c,key in ((1,'rough_semiprime_bulk'),(3,'small3_two_large_bulk')):
        count=0
        for q in pool[1:]:
            m=c*p*q
            if m>=N-Q:
                continue
            count+=1
            if prime(N-m):
                result[key]=row(m,count,dict(c=c,p=p,q=q,domain=f'q prime in ({p},10000]'))
                break
        assert key in result
    for c,key in ((7,'one_large_small_prime'),(21,'one_large_small_squarefree_plus'),
                  (231,'one_large_small_squarefree_minus'),(9,'one_large_small_nonsquarefree')):
        count=0
        for p in pool:
            m=c*p
            count+=1
            if prime(N-m):
                result[key]=row(m,count,dict(c=c,p=p,domain='p prime in (3163,10000]'))
                break
        assert key in result
    count=0
    for p in pool:
        m=3*p*p
        if m>=N-Q:
            continue
        count+=1
        if prime(N-m):
            result['nonsquarefree_bulk']=row(m,count,dict(c=3,p=p,domain='p prime in (3163,10000], m=3*p^2'))
            break
    assert 'nonsquarefree_bulk' in result
    result['excluded_square_bulk_search']=dict(status='STRUCTURAL_WITNESS_EXCLUSION',
        domain='m=p^2, p prime>3163, n=N-m>Q',
        reason='N mod3=1 and p!=3 imply n mod3=0; n>Q>3 cannot be prime')
    count=0
    for p in pool:
        m=3183*p
        count+=1
        if prime(N-m):
            result['one_large_incomplete_small_fibre']=row(m,count,
                dict(c=3183,p=p,domain='p prime in (3163,10000], c=3*1061>a'))
            break
    assert 'one_large_incomplete_small_fibre' in result
    count=0
    for p in shared.parity.PRIMES:
        if p<23 or p>A or p in (3,7,11,13,17):
            continue
        m=51051*p
        if not 1000000<=m<N-Q:
            continue
        count+=1
        if prime(N-m):
            result['all_small_bulk']=row(m,count,
                dict(c=51051,p=p,domain='p prime in [23,3163], m=3*7*11*13*17*p<N-Q'))
            break
    assert 'all_small_bulk' in result
    count=0
    for c in shared.parity.PRIMES:
        if c>A:
            break
        if c==3 or gcd(c,N)!=1:
            continue
        count+=1
        m=3*c
        if prime(N-m):
            result['small_p_extrapolation']=row(m,count,dict(p=3,c=c,domain='c prime <=3163, unit to N, c!=3'))
            break
    assert 'small_p_extrapolation' in result
    return result


if __name__=='__main__':
    output=shared.output_directory()
    before=shared.verify()
    result=dict(status='VERIFIED_FINITE_WITNESSES_ONLY',N=N,a9=A,Q=Q,
                witnesses=search(),conservation_before=before,
                conservation_after=shared.verify(),imports=shared.IMPORTS,
                script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),victory=False)
    (output/'witnesses.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(result['witnesses'],indent=2))
