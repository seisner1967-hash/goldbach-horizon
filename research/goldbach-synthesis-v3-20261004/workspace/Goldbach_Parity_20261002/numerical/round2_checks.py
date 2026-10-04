"""Round 2 exact diagnostics; previous scripts and receipts are read-only.

Arithmetic coefficients are integers or Fraction. Symbolic logs are maps from
prime p to the coefficient of log(p). No approximate logarithm is evaluated.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import gcd, prod
from pathlib import Path
from time import perf_counter
import json

from parity_checks import N, PRIMES, divisors, factor, mu, rough

ROOT = Path(__file__).resolve().parent
ALPHA = 100
Q = (N-1)//ALPHA
OLD_SCRIPT_SHA256 = '6f201c898eb6bfc4e05703d02cdca4e211d1a7311cb11a0644192c90990cb8b2'


def omega(n):
    return sum(e for _, e in factor(n))


def prime_indicator(n):
    fs = factor(n)
    return int(len(fs) == 1 and fs[0][1] == 1)


def chen_check(n, alpha, counts):
    assert 1 < n < (alpha+1)**4 and rough(n, alpha)
    om = omega(n)
    assert 1 <= om <= 3
    twice_weight = (om-2)*(om-3)
    assert twice_weight % 2 == 0
    weight = twice_weight//2
    assert prime_indicator(n) == weight
    counts['rough_prime_detection_multiplicity_weight'] += 1
    counts[f'Omega_{om}'] += 1
    if any(e > 1 for _, e in factor(n)):
        counts['nonsquarefree_weight_cases'] += 1
    return dict(n=n, alpha=alpha, factorization=factor(n),
                Omega_with_multiplicity=om, weight=weight,
                prime_indicator=prime_indicator(n))


def normalize(vector):
    return {p: c for p, c in vector.items() if c}


def add_scaled(target, source, scale):
    for p, c in source.items():
        target[p] = target.get(p, Fraction(0))+scale*c


def log_vector(n):
    return {p: Fraction(e) for p, e in factor(n)}


def log_ratio_vector(k, m):
    out = log_vector(k)
    add_scaled(out, log_vector(m), Fraction(-1))
    return normalize(out)


def phi(n):
    return prod(p**(e-1)*(p-1) for p, e in factor(n))


def divisor_kernel(alpha, q, m):
    out, admitted = {}, []
    for k in divisors(m):
        if k <= q and alpha*k < m:
            add_scaled(out, log_ratio_vector(k, m), Fraction(mu(k)))
            admitted.append(k)
    return normalize(out), admitted


def harmonic_kernel(N_bound, alpha, q, n, m):
    assert n+m == N_bound
    prefix = min(q, (m-1)//alpha)
    out, admitted, excluded = {}, [], []
    for k in range(1, prefix+1):
        assert alpha*k < m
        if gcd(k, N_bound) == 1 and gcd(k, n) == 1:
            add_scaled(out, log_ratio_vector(k, m), Fraction(mu(k), phi(k)))
            admitted.append(k)
        else:
            excluded.append(k)
    return normalize(out), prefix, admitted, excluded


def serialize_vector(vector):
    return {str(p): f'{c.numerator}/{c.denominator}'
            for p, c in sorted(vector.items())}


def local_term(m):
    n = N-m
    assert 1 < n < N and 1 < m < N and gcd(n, N) == 1
    D, divisor_admitted = divisor_kernel(ALPHA, Q, m)
    W, prefix, harmonic_admitted, excluded = harmonic_kernel(N, ALPHA, Q, n, m)
    delta = dict(D)
    add_scaled(delta, W, Fraction(-1))
    delta = normalize(delta)
    literal = {p: Fraction(mu(m))*c for p,c in delta.items()}
    fs = factor(n)
    von_mangoldt = {fs[0][0]: Fraction(1)} if len(fs) == 1 else {}
    fII = dict(von_mangoldt)
    add_scaled(fII, log_vector(n), Fraction(-1))
    fII = normalize(fII)
    quadratic = {}
    for p, c in fII.items():
        for r, d in literal.items():
            key = tuple(sorted((p, r)))
            quadratic[key] = quadratic.get(key, Fraction(0))+c*d
    quadratic = normalize(quadratic)
    return dict(n=n, m=m, factor_n=fs, factor_m=factor(m), mu_m=mu(m),
                alpha=ALPHA, Q=Q, prefix=prefix,
                admitted_divisors=divisor_admitted,
                admitted_harmonic_k=harmonic_admitted, unit_excluded_k=excluded,
                D=serialize_vector(D), W=serialize_vector(W),
                D_minus_W=serialize_vector(delta),
                literal_kernel=serialize_vector(literal), fII=serialize_vector(fII),
                Sfull_log_product_coefficients={f'{p},{r}': f'{c.numerator}/{c.denominator}'
                                               for (p,r),c in sorted(quadratic.items())}), quadratic


def run():
    started = perf_counter()
    old_script = ROOT/'parity_checks.py'
    old_receipt = ROOT/'numerical.json'
    old_script_hash = sha256(old_script.read_bytes()).hexdigest()
    old_receipt_hash = sha256(old_receipt.read_bytes()).hexdigest()
    assert old_script_hash == OLD_SCRIPT_SHA256
    counts = Counter()
    examples = []
    for p in (101, 103, 107, 109, 127, 131, 137, 139):
        assert prime_indicator(p) == 1
        for exponent in (1, 2, 3):
            n = p**exponent
            assert n < N
            examples.append(chen_check(n, ALPHA, counts))
        for q in (101, 103, 107, 109, 127):
            n = p*p*q
            assert n < N
            examples.append(chen_check(n, ALPHA, counts))
    for n in range(2, 3001):
        if rough(n, ALPHA):
            chen_check(n, ALPHA, counts)
    sampled_n = tuple(3 + (i*104729+7919) % (N//2-3) for i in range(4096))
    for n in sampled_n:
        for axis in (n, N-n):
            if rough(axis, ALPHA):
                chen_check(axis, ALPHA, counts)
    # All rough proper squares/cubes and all mixed repeated triprimes below N.
    # p^2*q<N, p,q>100 implies p<sqrt(N/101), q<N/101^2<10000.
    eligible = tuple(p for p in PRIMES if p > ALPHA)
    repeated_n = set()
    for p in eligible:
        if p*p >= N:
            break
        chen_check(p*p, ALPHA, counts)
        repeated_n.add(p*p)
        counts['all_rough_prime_squares_below_N'] += 1
        if p**3 < N:
            chen_check(p**3, ALPHA, counts)
            repeated_n.add(p**3)
            counts['all_rough_prime_cubes_below_N'] += 1
        for q in eligible:
            n = p*p*q
            if n >= N:
                break
            if q != p:
                chen_check(n, ALPHA, counts)
                assert n not in repeated_n
                repeated_n.add(n)
                counts['all_rough_mixed_p_squared_q_below_N'] += 1

    bad, bad_quadratic = local_term(303)
    partner, partner_quadratic = local_term(101)
    assert bad['factor_n'] == ((7, 1), (41, 1), (348431, 1))
    assert 14285671 == 41*348431
    assert bad['factor_m'] == ((3, 1), (101, 1))
    assert bad['D'] == {'3': '-1/1'}
    assert bad['W'] == {'3': '-1/1', '101': '-1/2'}
    assert bad['D_minus_W'] == bad['literal_kernel'] == {'101': '1/2'}
    assert bad['fII'] == {'7': '-1/1', '41': '-1/1', '348431': '-1/1'}
    assert len(bad_quadratic) == 3 and all(c < 0 for c in bad_quadratic.values())
    assert partner['literal_kernel'] == {} and partner_quadratic == {}
    counts['symbolic_local_switch_counterexample'] += 1
    incomplete_rough_r = 101*103*107
    incomplete_rough_m = 3*incomplete_rough_r
    assert rough(incomplete_rough_r, ALPHA)
    assert not rough(incomplete_rough_m, ALPHA)
    incomplete_omega = omega(incomplete_rough_m)
    incomplete_weight = (incomplete_omega-2)*(incomplete_omega-3)//2
    assert incomplete_omega == 4 and incomplete_weight == 1
    assert prime_indicator(incomplete_rough_m) == 0
    counts['rough_r_only_weight_counterexample'] += 1
    assert sha256(old_script.read_bytes()).hexdigest() == old_script_hash
    assert sha256(old_receipt.read_bytes()).hexdigest() == old_receipt_hash
    result = dict(status='PASS', N=N, alpha=ALPHA, Q=Q,
                  arithmetic='Integers and exact Fraction coefficients of symbolic logs',
                  checks=dict(counts), total_cases=sum(counts.values()),
                  chen_domain='1<n<(alpha+1)^4, every prime divisor of n>alpha, Omega counts multiplicities',
                  finite_domains=dict(tiny_n_inclusive=[2,3000], deterministic_additive_samples=4096,
                                      candidate_axes=8192,
                                      exhaustive_repeated_support='all p^2,p^3,p^2*q<N with primes p,q>100 and p!=q'),
                  selected_repeated_prime_examples=examples,
                  chen_filter='PASS under complete roughness; no squarefree assumption required',
                  local_switch_counterexample=bad,
                  switched_prime_partner=partner,
                  incomplete_roughness_counterexample=dict(r=incomplete_rough_r,k=3,m=incomplete_rough_m,
                                                          factor_m=factor(incomplete_rough_m),
                                                          Omega=incomplete_omega,weight=incomplete_weight,
                                                          prime_indicator=0),
                  falsified_claim='Uniform zero or favorable pointwise diagonal after switching m=3*101 to m=101 at fixed N',
                  diagnostic_scope='One strictly negative Sfull term survives at r>alpha; no contradiction of a future global D_N bound',
                  previous_script_sha256=old_script_hash,
                  previous_numerical_receipt_sha256=old_receipt_hash,
                  previous_artifacts_preserved=True,
                  harness_repair='Preliminary run rejected an expected prime-factor oracle treating cofactor 14285671 as prime. Actual factorization is 7*41*348431; corrected oracle. Counterexample sign unchanged.',
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=round(perf_counter()-started, 3))
    (ROOT/'round2.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ('status','N','alpha','Q','checks','total_cases',
                                         'local_switch_counterexample','switched_prime_partner',
                                         'previous_artifacts_preserved','script_sha256','elapsed_seconds')},indent=2))


if __name__ == '__main__':
    run()
