"""Finite integer checks for a written HH sector estimate.

These are diagnostic checks, not Lean proofs or asymptotic evidence.
No floating-point transcendental evaluator is used.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import comb, gcd, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


@lru_cache(None)
def factor(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


@lru_cache(None)
def divisors(n):
    result = [1]
    for p, e in factor(n):
        result = [d * p**j for d in result for j in range(e + 1)]
    return tuple(sorted(result))


def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)


def dj(n, j):
    return prod(comb(e + j - 1, j - 1) for _, e in factor(n))


@lru_cache(None)
def long_pairs(n, y):
    return sum(1 for u in divisors(n) if u > y and n // u > y)


@lru_cache(None)
def HU(n, y):
    h = unsigned = 0
    for u in divisors(n):
        if u <= y:
            continue
        for v in divisors(n // u):
            if v > y:
                h += mu(u) * mu(v)
                unsigned += 1
    return h, unsigned


counts = Counter()

# Squarefree carrier identity and the unsigned triple count.
for y in range(1, 13):
    for n in range(1, 3001):
        h, u = HU(n, y)
        assert u == sum(long_pairs(d, y) for d in divisors(n))
        assert abs(h) <= u <= dj(n, 3)
        counts['unsigned_triple_and_absolute_bound'] += 1
        if mu(n):
            assert h == sum(mu(d) * long_pairs(d, y) for d in divisors(n))
            counts['squarefree_carrier_identity'] += 1

# A whole rough n-fibre is bounded by d4(n), without cancellation.
for y in range(1, 9):
    for n in range(1, 1801):
        assert sum(abs(HU(a, y)[0]) for a in divisors(n)) <= dj(n, 4)
        assert sum(dj(a, 3) for a in divisors(n)) == dj(n, 4)
        counts['four_divisor_fibre_bound'] += 1

# Restricted ordinary cofactor: r = s*t*zeta, followed by r*k=m.
for y in range(1, 8):
    for Z in [1, 2, 3, 7, 11, 30]:
        for m in range(1, 501):
            literal_abs = 0
            regrouped_abs = 0
            for r in divisors(m):
                for s in divisors(r):
                    if s <= y:
                        continue
                    for t in divisors(r // s):
                        zeta = r // (s * t)
                        if t > y and zeta <= Z:
                            literal_abs += abs(mu(s) * mu(t))
            for zeta in divisors(m):
                if zeta <= Z:
                    for d in divisors(m // zeta):
                        for s in divisors(d):
                            t = d // s
                            if s > y and t > y:
                                regrouped_abs += abs(mu(s) * mu(t))
            envelope = sum(dj(m // zeta, 3) for zeta in divisors(m) if zeta <= Z)
            assert literal_abs == regrouped_abs <= envelope
            counts['short_cofactor_absolute_envelope'] += 1

# CRT density in the exact original threshold convention.
primes = [2, 3, 5, 7, 11]
for N in range(3, 65):
    for q in range(1, 13):
        if gcd(N, q) != 1:
            continue
        for W in [2, 3, 5, 7, 11]:
            pw = prod(p for p in primes if p <= W)
            period = prod(p for p in primes if p <= W and q % p)
            V = prod(Fraction(p - 1, p) for p in primes if p <= W)
            Fq = prod(Fraction(p, p - 1) for p in primes if p <= W and q % p == 0)
            number = sum(gcd(N - q * x, pw) == 1 for x in range(period))
            assert Fraction(number, period) == V * Fq
            counts['exact_active_prime_CRT_density'] += 1

# Largest-factor inequality for the shifted three-divisor moment.
# The d <= (N/q)^(2/3) condition is checked as d^3*q^2 <= N^2.
for N in range(3, 121):
    for q in range(1, min(11, N)):
        if gcd(N, q) != 1:
            continue
        for W in [2, 3, 5]:
            pw = prod(p for p in primes if p <= W)
            lhs = sum(dj(v, 3) for v in range(1, (N-1)//q+1)
                      if gcd(v,N) == 1 and gcd(N-q*v,pw) == 1)
            rhs = 0
            for d in range(1, (N-1)//q+1):
                if d**3*q*q <= N*N and gcd(d,N) == 1:
                    rhs += 3*dj(d,2)*sum(gcd(N-q*d*x,pw) == 1
                              for x in range(1,(N-1)//(q*d)+1))
            assert lhs <= rhs
            counts['shifted_three_divisor_hyperbola_inequality'] += 1


def parity_ledger(a, r, y):
    assert mu(a) and mu(r) and gcd(a, r) == 1
    pos = neg = 0
    for da in divisors(a):
        for dr in divisors(r):
            weight = long_pairs(da, y) * long_pairs(dr, y)
            if mu(da * dr) == 1:
                pos += weight
            else:
                neg += weight
    ha, ua = HU(a, y)
    hr, ur = HU(r, y)
    assert pos - neg == ha * hr
    assert pos + neg == ua * ur
    assert 2 * min(pos, neg) == ua * ur - abs(ha * hr)
    return dict(a=a, r=r, y=y, H_a=ha, H_r=hr,
                U_a=ua, U_r=ur, positive=pos, negative=neg,
                net=pos-neg, maximum_internal_cancellation=min(pos, neg))


for y in range(1, 9):
    for a in range(1, 121):
        for r in range(1, 121):
            if mu(a) and mu(r) and gcd(a, r) == 1:
                parity_ledger(a, r, y)
                counts['same_root_parity_ledger'] += 1

examples = []
for a,b,r,k,y,W in [(15,13,77,17,2,2), (105,19,2431,23,2,2),
                       (105,17,143,19,6,2)]:
    N = a*b + r*k
    n, m = a*b, r*k
    assert gcd(n,N) == 1 and mu(n) and mu(m)
    assert all(p>W for p,_ in factor(n))
    assert a <= m and b <= m and r > 1
    assert n % a == 0 and (n-N) % r == 0
    e = parity_ledger(a,r,y)
    e.update(N=N,b=b,k=k,n=n,m=m,W=W,CRT_modulus=a*r,
             scope='Exact finite unit/squarefree/core tuple; not an asymptotic family test')
    examples.append(e)

result = {
    'status': 'PASS',
    'scope': 'Finite exact integer and rational diagnostics only; no Lean compilation and no asymptotic inference',
    'checks': dict(counts),
    'total_finite_cases': sum(counts.values()),
    'examples': examples,
    'asymptotic_sector_bound': 'WRITTEN_DEDUCTION_FROM_DECLARED_ROSSER_INPUT',
    'signed_global_estimate': 'NOT_OBTAINED',
    'positive_prime_pair_margin': 'NOT_OBTAINED',
    'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
}
(ROOT / 'EXACT_CHECKS.json').write_text(json.dumps(result, indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
