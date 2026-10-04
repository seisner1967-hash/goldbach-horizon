"""Strict, reproducible integer diagnostics for the Goldbach parity ledger.

These finite checks do not certify D_N, logarithmic estimates, an asymptotic
theorem, or a Lean proof.  They use N=100000000 as a real additive constraint.
No floating-point logarithms enter any arithmetic identity tested here.
"""
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from math import comb, gcd, isqrt, prod
from pathlib import Path
from time import perf_counter
import argparse
import json

ROOT = Path(__file__).resolve().parent
N = 100_000_000


def prime_list(limit):
    marked = bytearray(b"\x01") * (limit + 1)
    marked[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if marked[p]:
            marked[p*p:limit+1:p] = b"\x00" * (((limit-p*p)//p)+1)
    return tuple(p for p in range(2, limit + 1) if marked[p])


PRIMES = prime_list(isqrt(N))


@lru_cache(None)
def factor(n):
    assert 1 <= n <= N
    remainder, result = n, []
    for p in PRIMES:
        if p*p > remainder:
            break
        if remainder % p == 0:
            exponent = 0
            while remainder % p == 0:
                remainder //= p
                exponent += 1
            result.append((p, exponent))
    if remainder > 1:
        result.append((remainder, 1))
    assert prod(p**e for p, e in result) == n
    return tuple(result)


@lru_cache(None)
def divisors(n):
    out = [1]
    for p, exponent in factor(n):
        out = [d*p**j for d in out for j in range(exponent + 1)]
    result = tuple(sorted(out))
    assert result[0] == 1 and result[-1] == n
    assert all(n % d == 0 for d in result)
    return result


@lru_cache(None)
def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for _, e in fs) else (-1)**len(fs)


def dj(n, j):
    assert j >= 1
    return prod(comb(e+j-1, j-1) for _, e in factor(n))


@lru_cache(None)
def long_pairs(n, y):
    return sum(u > y and n//u > y for u in divisors(n))


@lru_cache(None)
def direct_HU(n, y):
    """Literal signed/unsigned u*v*w=n expansion, with u,v>y."""
    signed = unsigned = 0
    for u in divisors(n):
        if u > y:
            for v in divisors(n//u):
                if v > y:
                    signed += mu(u)*mu(v)
                    unsigned += 1
    return signed, unsigned


@lru_cache(None)
def regrouped_H(n, y):
    """Independent u*v=d then d*w=n regrouping, valid also nonsquarefree."""
    return sum(sum(mu(u)*mu(d//u) for u in divisors(d)
                   if u > y and d//u > y) for d in divisors(n))


def rough(n, y):
    return all(p > y for p, _ in factor(n))


def odd_even_weights(n):
    mn = mu(n)
    odd, even = (mn*mn-mn)//2, (mn*mn+mn)//2
    assert odd in (0, 1) and even in (0, 1)
    return odd, even


def mobius_of_certified_product(a, b):
    if a*b <= N:
        return mu(a*b)
    # Both factors are within the certified sieve domain. The product may
    # exceed N, but the combined prime-exponent table factors it exactly.
    prime_exponents = Counter(dict(factor(a)))
    prime_exponents.update(dict(factor(b)))
    assert prod(p**e for p,e in prime_exponents.items()) == a*b
    return 0 if any(e > 1 for e in prime_exponents.values()) else (-1)**len(prime_exponents)


def xor_parity_check(a, r, counts):
    assert gcd(a, r) == 1
    oa, ea = odd_even_weights(a)
    or_, er = odd_even_weights(r)
    mar = mobius_of_certified_product(a, r)
    oar, ear = (mar*mar-mar)//2, (mar*mar+mar)//2
    assert oar == oa*er+ea*or_
    assert ear == ea*er+oa*or_
    counts['coprime_parity_XOR_identity'] += 1


def prime_detector(n):
    return int(len(factor(n)) == 1 and factor(n)[0][1] == 1)


def triprime_count(n, alpha):
    """Exact sorted p<q<r divisor enumeration, independent of Omega shortcut."""
    prime_divisors = tuple(d for d in divisors(n) if d > alpha and prime_detector(d))
    return sum(p*q*r == n for i, p in enumerate(prime_divisors)
               for j, q in enumerate(prime_divisors[i+1:], i+1)
               for r in prime_divisors[j+1:])


def triprime_identity_check(m, alpha, N_bound, counts):
    assert m > 1 and m < N_bound and N_bound <= alpha**4
    assert mu(m) != 0 and rough(m, alpha)
    omega = len(factor(m))
    assert omega <= 3
    odd, _ = odd_even_weights(m)
    t3 = triprime_count(m, alpha)
    assert t3 in (0, 1)
    assert prime_detector(m) == odd-t3
    counts['alpha_rough_prime_detection_minus_triprime'] += 1
    chen_weight = 3-2*omega+omega*(omega-1)//2
    assert prime_detector(m) == chen_weight
    counts['bounded_Omega_prime_detection_weight'] += 1
    return dict(m=m, alpha=alpha, factorization=factor(m), Omega=omega,
                prime_detector=prime_detector(m), odd_weight=odd, T3=t3,
                bounded_Omega_weight=chen_weight)


@lru_cache(None)
def truncated_mobius_power(n, alpha, exponent):
    assert exponent >= 1
    if n > alpha**exponent:
        return 0
    if exponent == 1:
        return mu(n) if n <= alpha else 0
    return sum(mu(d)*truncated_mobius_power(n//d, alpha, exponent-1)
               for d in divisors(n) if d <= alpha)


def HB_incidence(n, alpha, j):
    if j == 1:
        return truncated_mobius_power(n, alpha, 1)
    return sum(truncated_mobius_power(d, alpha, j)*dj(n//d, j-1)
               for d in divisors(n))


def HB_identity_check(n, alpha, counts):
    assert 1 <= n < alpha**4
    incidences = tuple(HB_incidence(n, alpha, j) for j in (1, 2, 3, 4))
    reconstructed = sum(c*t for c,t in zip((4, -6, 4, -1), incidences))
    assert reconstructed == mu(n), (n, alpha, incidences, reconstructed, mu(n))
    counts['fourfold_truncated_HeathBrown_Mobius_identity'] += 1
    return dict(n=n, alpha=alpha, mu=mu(n), incidences_j1_to_j4=incidences,
                reconstructed=reconstructed)


@lru_cache(None)
def long_mobius_power(n, alpha, exponent):
    assert exponent >= 1
    if n < (alpha+1)**exponent:
        return 0
    if exponent == 1:
        return mu(n) if n > alpha else 0
    return sum(mu(d)*long_mobius_power(n//d, alpha, exponent-1)
               for d in divisors(n) if d > alpha)


def HB_with_remainder_check(n, alpha, counts):
    incidences = tuple(HB_incidence(n, alpha, j) for j in (1, 2, 3, 4))
    polynomial = sum(c*t for c,t in zip((4, -6, 4, -1), incidences))
    remainder = sum(long_mobius_power(d, alpha, 4)*dj(n//d, 3)
                    for d in divisors(n))
    assert mu(n) == polynomial+remainder
    if n < (alpha+1)**4:
        assert remainder == 0
    counts['full_HeathBrown_identity_with_remainder'] += 1
    return dict(n=n, alpha=alpha, mu=mu(n), incidences_j1_to_j4=incidences,
                polynomial=polynomial, remainder=remainder)


def parity_ledger(a, r, y):
    assert mu(a) != 0 and mu(r) != 0 and gcd(a, r) == 1
    positive = negative = 0
    for da in divisors(a):
        for dr in divisors(r):
            amplitude = long_pairs(da, y)*long_pairs(dr, y)
            sign = mobius_of_certified_product(da, dr)
            if sign == 1:
                positive += amplitude
            else:
                assert sign == -1
                negative += amplitude
    ha, ua = direct_HU(a, y)
    hr, ur = direct_HU(r, y)
    assert positive-negative == ha*hr
    assert positive+negative == ua*ur
    assert 2*min(positive, negative) == ua*ur-abs(ha*hr)
    return dict(a=a, r=r, y=y, H_a=ha, H_r=hr, U_a=ua, U_r=ur,
                positive=positive, negative=negative, net=positive-negative,
                maximum_internal_cancellation=min(positive, negative))


def ceil_root(n, degree):
    """Integer-only ceiling of n**(1/degree)."""
    lo, hi = 0, n
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid**degree >= n:
            hi = mid
        else:
            lo = mid
    assert (hi-1)**degree < n <= hi**degree
    return hi


def check_coefficients(n, y, counts):
    h, u = direct_HU(n, y)
    assert h == regrouped_H(n, y)
    assert u == sum(long_pairs(d, y) for d in divisors(n))
    assert abs(h) <= u <= dj(n, 3)
    counts['literal_convolution_identity'] += 1
    if mu(n) != 0:
        assert h == sum(mu(d)*long_pairs(d, y) for d in divisors(n))
        counts['squarefree_carrier_identity'] += 1
    if rough(n, y):
        expected = 0 if n == 1 else 1+mu(n)
        assert h == expected
        counts['rough_complete_parity_identity'] += 1
        # On squarefree nonunit support these weights detect parity exactly.
        if mu(n) != 0 and n != 1:
            assert expected in (0, 2)
            assert expected//2 == (len(factor(n)) % 2 == 0)
            counts['rough_squarefree_parity_weight'] += 1


def run(sample_count):
    started = perf_counter()
    counts = Counter()
    for y in (1, 2, 6, 10, 100):
        for n in range(1, 3001):
            check_coefficients(n, y, counts)
    for y in (1, 2, 6, 10):
        for a in range(1, 81):
            for r in range(1, 81):
                if mu(a) != 0 and mu(r) != 0 and gcd(a, r) == 1:
                    parity_ledger(a, r, y)
                    counts['small_bilinear_parity_ledger'] += 1
    for a in range(1, 81):
        for r in range(1, 81):
            if gcd(a, r) == 1:
                xor_parity_check(a, r, counts)

    alpha_quarter = ceil_root(N, 4)
    alpha_eighth = ceil_root(N, 8)
    q_quarter = (N-1)//alpha_quarter
    q_eighth = (N-1)//alpha_eighth
    assert alpha_quarter == 100 and alpha_eighth == 10
    assert q_quarter >= alpha_quarter and q_quarter*(alpha_quarter+1) > N-1
    assert q_eighth >= alpha_eighth and q_eighth*(alpha_eighth+1) > N-1
    assert 101*103*107*109 > N
    candidate_C_examples = []
    for alpha in (2, 3, 4, 5, 6, 7, 8, 100):
        for n in range(1, min(3000, alpha**4-1)+1):
            HB_identity_check(n, alpha, counts)
    for n in (1, 101, 101*103, 101*103*107, N-1):
        candidate_C_examples.append(HB_identity_check(n, alpha_quarter, counts))
    for alpha in (2, 3, 4, 5):
        for n in range(1, 3001):
            HB_with_remainder_check(n, alpha, counts)
    sharp_HB_failure = HB_with_remainder_check(81, 2, counts)
    assert sharp_HB_failure['polynomial'] == -1 and sharp_HB_failure['mu'] == 0
    assert sharp_HB_failure['remainder'] == 1
    candidate_A_examples = {}
    for m in range(2, 30001):
        if mu(m) != 0 and rough(m, alpha_quarter):
            item = triprime_identity_check(m, alpha_quarter, N, counts)
            candidate_A_examples.setdefault(str(item['Omega']), item)
    # Enumerate all alpha-rough squarefree triprimes m<N exactly.
    # The maximal third prime is (N-1)//(101*103)<10000, so PRIMES suffice.
    eligible_primes = tuple(p for p in PRIMES if p > alpha_quarter)
    exhaustive_triples = []
    for i, p in enumerate(eligible_primes):
        if p**3 >= N:
            break
        for j in range(i+1, len(eligible_primes)):
            q = eligible_primes[j]
            if p*q*q >= N:
                break
            for r in eligible_primes[j+1:]:
                m = p*q*r
                if m >= N:
                    break
                item = triprime_identity_check(m, alpha_quarter, N, counts)
                assert item['Omega'] == 3 and item['odd_weight'] == item['T3'] == 1
                assert item['prime_detector'] == 0
                candidate_A_examples.setdefault('3', item)
                exhaustive_triples.append(m)
                counts['all_N_100000000_alpha100_triprimes'] += 1
    assert len(set(exhaustive_triples)) == len(exhaustive_triples)
    assert min(exhaustive_triples) == 101*103*107

    # Deterministic arithmetic sample. Every sampled n really satisfies n+m=N.
    # This sample is not an exhaustive sum over N or over the original selectors.
    sampled_n = tuple(3 + (i*104729 + 7919) % (N//2-3)
                      for i in range(sample_count))
    assert len(set(sampled_n)) == sample_count
    admissible = 0
    sign_histograms = {str(y): Counter() for y in (2, 6, 10, 100)}
    first_by_sign = {}
    for n in sampled_n:
        m = N-n
        assert 1 <= n < N and 1 <= m < N and n+m == N
        HB_identity_check(n, alpha_quarter, counts)
        HB_identity_check(m, alpha_quarter, counts)
        for y in (2, 6, 10, 100):
            check_coefficients(n, y, counts)
            check_coefficients(m, y, counts)
        if m > 1 and mu(m) != 0 and rough(m, alpha_quarter):
            item = triprime_identity_check(m, alpha_quarter, N, counts)
            candidate_A_examples.setdefault(str(item['Omega']), item)
        if gcd(n, N) != 1 or mu(n) == 0 or mu(m) == 0:
            continue
        fs = factor(n)
        if len(fs) < 2:
            continue
        b = fs[0][0]
        a, r, k = n//b, m, 1
        assert a*b+r*k == N and a*b == n and r*k == m
        assert b > 1 and a <= m and b <= m and r > alpha_quarter
        assert mu(a) and mu(r) and gcd(a, r) == 1
        assert rough(n, 2)
        xor_parity_check(a, r, counts)
        admissible += 1
        for y in (2, 6, 10, 100):
            ledger = parity_ledger(a, r, y)
            counts['N_100000000_admissible_bilinear_ledger'] += 1
            sign = 'positive' if ledger['net'] > 0 else 'negative' if ledger['net'] < 0 else 'zero'
            sign_histograms[str(y)][sign] += 1
            key = f'y={y}:{sign}'
            if key not in first_by_sign:
                ledger.update(N=N, n=n, m=m, b=b, k=k, alpha=alpha_quarter,
                              W=2, CRT_modulus=a*r, factor_a=factor(a), factor_r=factor(r))
                first_by_sign[key] = ledger

    # A deterministic targeted search at actual N, with nonzero log b*log r
    # because b,r>1. It tests the finite proposed cancellation mechanism.
    fixed_root_counterexample = None
    a = 21
    for b in PRIMES:
        n, m = a*b, N-a*b
        if n >= N or gcd(n, N) != 1 or mu(n) == 0 or mu(m) == 0:
            continue
        r, k = m, 1
        ledger = parity_ledger(a, r, 2)
        if ledger['positive'] > 0 and ledger['negative'] == 0:
            assert a <= m and b <= m and r > alpha_quarter and rough(n, 2)
            ledger.update(N=N, n=n, m=m, b=b, k=k, alpha=alpha_quarter, W=2,
                          CRT_modulus=a*r, factor_a=factor(a), factor_r=factor(r))
            fixed_root_counterexample = ledger
            break
    assert fixed_root_counterexample is not None, 'Targeted finite cancellation test inconclusive'

    omitted_T3 = triprime_identity_check(101*103*107, 100, N, counts)
    assert omitted_T3['prime_detector'] != omitted_T3['odd_weight']
    incomplete_rough_m = 3*101*103
    assert rough(101*103, 100) and not rough(incomplete_rough_m, 100)
    assert mu(incomplete_rough_m) != 0
    assert prime_detector(incomplete_rough_m) != odd_even_weights(incomplete_rough_m)[0]-triprime_count(incomplete_rough_m, 100)

    result = dict(
        status='PASS', N=N,
        scope='Exact finite integer diagnostics; no Lean theorem, no global D_N bound, no asymptotic inference',
        profiles=dict(alpha_quarter=alpha_quarter, Q_quarter=q_quarter,
                      alpha_eighth=alpha_eighth, Q_eighth=q_eighth),
        finite_domains=dict(coefficient_n_inclusive=[1, 3000], coefficient_y=[1, 2, 6, 10, 100],
                            ledger_a_r_inclusive=[1, 80], ledger_y=[1, 2, 6, 10],
                            large_N_sample_count=sample_count,
                            large_N_sample_formula='n_i=3+(i*104729+7919) mod (N//2-3), i=0..sample_count-1',
                            large_N_admissible_tuples=admissible,
                            all_alpha100_rough_squarefree_triprimes_below_N=len(exhaustive_triples),
                            triprime_domain='Every prime triple 100<p<q<r and p*q*r<100000000; exact enumeration',
                            large_N_tuple_rule='b=least prime factor(n), a=n/b, r=N-n, k=1; retain mu(n)mu(m)!=0, gcd(n,N)=1, Omega(n)>=2'),
        checks=dict(counts), total_cases=sum(counts.values()),
        sign_histograms={y:dict(c) for y,c in sign_histograms.items()},
        first_examples_by_sign=first_by_sign,
        killed_candidate=dict(name='automatic complete internal positive-negative cancellation at a fixed CRT root',
                              verdict='FALSE', counterexample=fixed_root_counterexample),
        candidate_A=dict(name='rough squarefree prime detector = odd parity detector - T3',
                         status='PASS_ON_TESTED_DOMAIN', examples_by_Omega=candidate_A_examples,
                         exhaustive_triprimes_count=len(exhaustive_triples),
                         exhaustive_triprimes_sha256=sha256(json.dumps(exhaustive_triples,separators=(',',':')).encode()).hexdigest(),
                         omitted_T3_counterexample=omitted_T3,
                         insufficient_rough_r_counterexample=dict(r=101*103,k=3,m=incomplete_rough_m,
                                                                 factorization=factor(incomplete_rough_m))),
        candidate_B=dict(name='bounded-Omega weight 3-2*Omega+binom(Omega,2)',
                         status='PASS_ON_TESTED_ROUGH_SQUAREFREE_OMEGA_1_TO_3_DOMAIN',
                         outside_support_counterexample=dict(m=101*103*107*109,
                                                             factorization=[101,103,107,109],
                                                             Omega=4, prime_detector=0, weight=1,
                                                             failed_hypothesis='m<N=100000000')),
        candidate_C=dict(name='fourfold finite truncated Heath-Brown identity for Mobius',
                         status='PASS_ON_TESTED_DOMAIN',
                         formula='mu=4M-6(M*M*zeta)+4(M*M*M*zeta*zeta)-(M*M*M*M*zeta*zeta*zeta)',
                         support='1<=n<alpha^4, M(n)=mu(n) for n<=alpha, zero otherwise',
                         examples=candidate_C_examples,
                         small_alpha=[2,3,4,5,6,7,8,100],
                         small_n_max='min(3000,alpha^4-1)',
                         large_N_n_and_complements=2*sample_count,
                         full_remainder_domain='n=1..3000, alpha=2,3,4,5',
                         omitted_remainder_counterexample=sharp_HB_failure,
                         analogous_alpha100_sharp_boundary=dict(n=101**4,alpha=100,
                                                               certified_factors=[101,101,101,101],
                                                               incidences_j1_to_j4=[0,1,5,15],
                                                               polynomial=-1,mu=0,remainder=1,
                                                               scope='Direct integer prime-power computation; outside N=100000000')),
        surviving_candidates=['literal H convolution regrouping', 'P-Q=H_y(a)H_y(r)',
                              'P+Q=U_y(a)U_y(r)', 'rough H_y(t)=1+mu(t) for t>1'],
        analytic_target='NOT_TESTED: D_N requires signed aggregate and covered bridge; N=1e8 is below exp(1024) onset',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        harness_repair='Two preliminary runs hit intentional factor(n)<=N guard at CRT products a*r and da*dr>N. Fixed both by reconstruction from certified factor lists; no mathematical identity failed.',
        elapsed_seconds=round(perf_counter()-started, 3))
    (ROOT/'numerical.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:result[k] for k in ('status','N','profiles','finite_domains','checks',
                                         'sign_histograms','killed_candidate','script_sha256','elapsed_seconds')}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--samples', type=int, default=4096)
    args = parser.parse_args()
    assert 1 <= args.samples <= 200000
    run(args.samples)
