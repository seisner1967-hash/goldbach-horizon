"""Exact filter for the true-Omega extension, including repeated primes."""
from collections import Counter
from hashlib import sha256
from math import comb
from pathlib import Path
import json
from parity_checks import factor, PRIMES, N

ROOT = Path(__file__).resolve().parent
alpha = 100
seen = set()
counts = Counter()
examples = []

def check(n, label):
    if n in seen:
        return
    seen.add(n)
    fs = factor(n)
    assert 1 < n < N <= alpha**4
    assert all(p > alpha for p, e in fs)
    omega = sum(e for p, e in fs)
    assert 1 <= omega <= 3
    weight = 3 - 2*omega + comb(omega, 2)
    prime_indicator = int(len(fs) == 1 and fs[0][1] == 1)
    assert weight == prime_indicator
    assert (omega-2)*(omega-3) == 2*weight
    counts[label] += 1
    counts['Omega_' + str(omega)] += 1
    if n in (101, 101**2, 101**3, 101**2*103):
        examples.append(dict(n=n, factorization=fs, Omega=omega,
                             weight=weight, prime_indicator=prime_indicator))

rough_primes = tuple(p for p in PRIMES if p > alpha)
for p in rough_primes:
    check(p, 'single_prime_sample')
    if p*p < N:
        check(p*p, 'all_prime_squares_below_N')
    if p*p*p < N:
        check(p*p*p, 'all_prime_cubes_below_N')
    if p*p*rough_primes[0] >= N:
        continue
    for q in rough_primes:
        n = p*p*q
        if n >= N:
            break
        if q != p:
            check(n, 'all_distinct_p_squared_q_below_N')

outside = dict(n=101**4, Omega=4, weight=3-2*4+comb(4, 2),
               prime_indicator=0, failed_hypothesis='n<N')
assert outside['weight'] != outside['prime_indicator']
nonrough_n = 3*101*103*107
nonrough_fs = factor(nonrough_n)
nonrough_omega = sum(e for p, e in nonrough_fs)
nonrough = dict(n=nonrough_n, r=101*103*107, k=3,
                factorization=nonrough_fs, Omega=nonrough_omega,
                weight=3-2*nonrough_omega+comb(nonrough_omega, 2),
                prime_indicator=0, failed_hypothesis='all prime divisors of n exceed alpha')
assert nonrough_n < N and nonrough['weight'] != 0
receipt = dict(status='PASS', N=N, alpha=alpha, case_count=len(seen),
               counts=dict(counts), examples=examples,
               domain='All p^2, p^3 and p^2 q with 100<p,q prime and n<N; primes sampled through 10000',
               Omega='sum of factor exponents, including multiplicity',
               squarefree_assumption=False,
               outside_counterexample=outside,
               rough_cofactor_only_counterexample=nonrough,
               script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
               scope='Finite exact filter only; no signed aggregate or D_N estimate')
out = ROOT/'chen_multiplicity.json'
out.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
print(json.dumps(receipt, indent=2))
