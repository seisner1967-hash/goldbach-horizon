"""New SS helpers; imports only frozen inert round18 strict arithmetic."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from fractions import Fraction
from functools import lru_cache
from math import gcd
import strict as s

MU_TABLE, PHI_TABLE, TABLE_CAP = None, None, 0


def prepare_short_tables(cap):
    global MU_TABLE, PHI_TABLE, TABLE_CAP
    assert cap >= 1 and cap <= s.Q
    MU_TABLE, PHI_TABLE = [1] * (cap + 1), list(range(cap + 1))
    MU_TABLE[0], PHI_TABLE[0] = 0, 0
    for p in s.primes_through(cap):
        for k in range(p, cap + 1, p):
            MU_TABLE[k] = -MU_TABLE[k]
            PHI_TABLE[k] -= PHI_TABLE[k] // p
        for k in range(p * p, cap + 1, p * p):
            MU_TABLE[k] = 0
    TABLE_CAP = cap
    assert MU_TABLE[1] == PHI_TABLE[1] == 1


def mu(n):
    f = s.factor(n)
    return 0 if any(e > 1 for _, e in f) else (-1) ** len(f)


def phi(n):
    result = n
    for p, _ in s.factor(n):
        result = result // p * (p - 1)
    return result


@lru_cache(maxsize=None)
def divisors(n):
    result = [1]
    for p, exponent in s.factor(n):
        before = list(result)
        for power in range(1, exponent + 1):
            result.extend(value * p ** power for value in before)
    return tuple(sorted(result))


def log_vector(n):
    return {p: Fraction(e) for p, e in s.factor(n)}


def Lambda(n):
    f = s.factor(n)
    return {f[0][0]: Fraction(1)} if len(f) == 1 else {}


def serialize(vector):
    return [[p, str(value)] for p, value in sorted(vector.items())]


def prefix(n, limit):
    result = {}
    for d in divisors(n):
        if d <= limit and mu(d):
            s.add(result, log_vector(d), mu(d))
    return result


@lru_cache(maxsize=None)
def kernel(m):
    """Only explicitly selected new physical vertices; true original Q and strict cutoff."""
    n = s.N - m
    assert 0 < m <= s.N - 2 and gcd(m, s.N) == gcd(n, s.N) == 1
    cutoff = min(s.Q, (m - 1) // s.A)
    assert 1 <= cutoff <= TABLE_CAP and s.A * cutoff < m
    assert cutoff == s.Q or m <= s.A * (cutoff + 1)
    logm = log_vector(m)
    D, W, total_coefficient = {}, {}, Fraction(0)
    short_divisors = []
    for k in divisors(m):
        if k <= s.Q and s.A * k < m:
            short_divisors.append(k)
            if mu(k):
                s.add(D, s.difference(log_vector(k), logm), mu(k))
    included = 0
    for k in range(1, cutoff + 1):
        if MU_TABLE[k] and gcd(k, n * s.N) == 1:
            assert PHI_TABLE[k] == phi(k)
            coefficient = Fraction(MU_TABLE[k], PHI_TABLE[k])
            s.add(W, log_vector(k), coefficient)
            total_coefficient += coefficient
            included += 1
    s.add(W, logm, -total_coefficient)
    C = s.scaled(s.difference(D, W), -mu(m))
    U, low = prefix(m, s.A), prefix(m, s.ALPHA)
    expected = s.scaled(s.difference(s.scaled(Lambda(m), -1), U), mu(m) ** 2)
    s.add(expected, W, mu(m))
    assert C == expected
    info = {'m': m, 'n': n, 'mu_m': mu(m), 'factorization_m': s.factor(m),
            'R': cutoff, 'original_Q': s.Q, 'strict_a_k_less_m': True,
            'short_divisors_original_Q_and_strict_front': short_divisors,
            'W_squarefree_unit_k_count': included, 'D_exact': serialize(D),
            'W_kernel_exact': serialize(W), 'C_exact': serialize(C),
            'whole_U_a': serialize(U), 'U_alpha': serialize(low),
            'annulus': serialize(s.difference(U, low)),
            'k1_D_and_W_term': serialize(s.scaled(logm, -1)),
            'mu1_phi1_equal1': True, 'k1_joint_cancels': True,
            'physical_divisor_identity_verified': True, 'old_vertex_or_kernel_replayed': False}
    return info, C, W


def poly_add(target, polynomial, scale=Fraction(1)):
    for key, value in polynomial.items():
        updated = target.get(key, Fraction(0)) + value * scale
        if updated:
            target[key] = updated
        else:
            target.pop(key, None)


def multiply(left, right):
    result = {}
    for p, value in left.items():
        for q, coefficient in right.items():
            key = tuple(sorted((p, q)))
            result[key] = result.get(key, Fraction(0)) + value * coefficient
    return {key: value for key, value in result.items() if value}


def polynomial_certificate(polynomial):
    lower = upper = Fraction(0)
    for key, coefficient in polynomial.items():
        lo = hi = Fraction(1)
        for p in key:
            a, b = s.log_bounds(p)
            assert a >= 0
            lo *= a
            hi *= b
        if coefficient >= 0:
            lower += coefficient * lo
            upper += coefficient * hi
        else:
            lower += coefficient * hi
            upper += coefficient * lo
    return s.certify_bounds(lower, upper)


def poly_summary(polynomial, expression):
    return {'exact_expression': expression, 'nonzero_monomials': len(polynomial),
            'sign_certificate': polynomial_certificate(polynomial)}


def eval_form(form, x):
    a, b = form
    return a * x + b


def product_form(forms, x):
    return s.product(eval_form(form, x) for form in forms)


def local_selberg(forms, low, high, rho, level=3):
    """Fresh exact finite square at T=3, with independent actual roots of divided forms."""
    assert level == 3
    primes = (2, 3)
    size = max(0, high - low + 1)
    saturated = [p for p in primes if rho[p] == p]
    if saturated:
        p = saturated[0]
        assert all(product_form(forms, x) % p == 0 for x in range(low, high + 1))
        return {'status': 'SATURATED_EMPTY_FINITE_ROUGH_CELL', 'saturated_prime': p,
                'finite_x_count': size, 'rough_count': 0, 'no_zero_denominator_constructed': True}
    g = {p: Fraction(rho[p], p) for p in primes}
    h = {p: g[p] / (1 - g[p]) for p in primes}
    G = 1 + h[2] + h[3]
    weights = {1: Fraction(1), 2: -1 / ((1 - g[2]) * G), 3: -1 / ((1 - g[3]) * G)}
    assert G > 0 and all(abs(value) <= 1 for value in weights.values())
    def density(d):
        return s.product(g[p] for p in primes if d % p == 0)
    principal = sum((weights[d] * weights[t] * density(d * t // gcd(d, t))
                     for d in weights for t in weights), Fraction(0))
    assert principal == 1 / G
    remainder, classes = {}, {}
    for d in (1, 2, 3, 6):
        roots = [a for a in range(d) if product_form(forms, a) % d == 0]
        assert Fraction(len(roots), d) == density(d)
        counts = []
        for a in roots:
            first = low + (a - low) % d
            count = 0 if first > high else (high - first) // d + 1
            error = Fraction(count) - Fraction(size, d)
            assert abs(error) <= 1
            counts.append({'residue': a, 'count': count, 'error_exact': str(error), 'CRT_plus1_kept': True})
        actual = sum(product_form(forms, x) % d == 0 for x in range(low, high + 1))
        assert actual == sum(row['count'] for row in counts)
        rem = Fraction(actual) - size * density(d)
        assert abs(rem) <= len(roots)
        remainder[d] = rem
        classes[str(d)] = {'actual_roots': roots, 'class_counts_and_errors': counts,
                           'rho_d': len(roots), 'actual_count': actual, 'remainder_exact': str(rem)}
    square, rough_count, histogram = Fraction(0), 0, {}
    for x in range(low, high + 1):
        F = product_form(forms, x)
        weight = sum((value for d, value in weights.items() if F % d == 0), Fraction(0))
        rough = all(F % p for p in primes)
        assert weight ** 2 >= int(rough)
        square += weight ** 2
        rough_count += rough
        histogram[str(weight)] = histogram.get(str(weight), 0) + 1
    paired_error = sum((weights[d] * weights[t] * remainder[d * t // gcd(d, t)]
                        for d in weights for t in weights), Fraction(0))
    absolute_error = sum((abs(remainder[d * t // gcd(d, t)])
                          for d in weights for t in weights), Fraction(0))
    assert square == size / G + paired_error
    assert rough_count <= square <= size / G + absolute_error
    return {'status': 'PASS_EXACT_NEW_DIVIDED_FORM_SELBERG_T3', 'G_exact': str(G),
            'g_exact': {str(p): str(v) for p, v in g.items()}, 'h_exact': {str(p): str(v) for p, v in h.items()},
            'support_natural_d': [1, 2, 3], 'weights_exact': {str(d): str(v) for d, v in weights.items()},
            'lambda1_equal1_norm_at_most1': True, 'principal_exact': str(principal),
            'principal_equal_inverse_G': True, 'CRT_classes': classes, 'finite_x_count': size,
            'rough_count': rough_count, 'all_pointwise_squares_verified': True,
            'weight_histogram': histogram, 'square_sum_exact': str(square),
            'paired_remainder_exact': str(paired_error), 'absolute_remainder_sum': str(absolute_error),
            'finite_upper_bound_exact': str(size / G + absolute_error),
            'source_G_lower_bound_or_D5_D10_D11_not_applied': True}
