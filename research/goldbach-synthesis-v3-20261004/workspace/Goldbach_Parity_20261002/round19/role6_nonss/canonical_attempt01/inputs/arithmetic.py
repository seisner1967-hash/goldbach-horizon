"""Fresh strict arithmetic and rational log enclosures for the non-SS19 bank.

Importing this file performs no table construction or mathematical check.
"""
from fractions import Fraction
from math import gcd

N = 100_000_000
ALPHA, A, Q, M, P0, Z = 100, 3163, 999999, 1000000, 3, 100
BITS, TERMS = 128, 48
SCALE = 1 << BITS


def floor_div(a, b):
    assert b > 0
    return a // b


def ceil_div(a, b):
    assert b > 0
    return -((-a) // b)


def integer_root(n, degree):
    lo, hi = 0, 1
    while hi ** degree <= n:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** degree <= n:
            lo = mid
        else:
            hi = mid
    assert lo ** degree <= n < (lo + 1) ** degree
    return lo


def add_vector(target, source, scalar=Fraction(1)):
    for p, value in source.items():
        changed = target.get(p, Fraction(0)) + scalar * value
        if changed:
            target[p] = changed
        elif p in target:
            del target[p]


def scaled_vector(source, scalar):
    result = {}
    add_vector(result, source, scalar)
    return result


def serialize_vector(value):
    return {str(p): f"{c.numerator}/{c.denominator}" for p, c in sorted(value.items())}


def serialize_fraction(value):
    return f"{value.numerator}/{value.denominator}"


def mul_bounds(left, right):
    products = [a * b for a in left for b in right]
    return (floor_div(min(products), SCALE), ceil_div(max(products), SCALE))


def sign_bounds(value, exact_zero=False):
    lo, hi = value
    assert lo <= hi
    if exact_zero:
        assert lo == hi == 0
        return "ZERO"
    if lo > 0:
        return "POSITIVE"
    if hi < 0:
        return "NEGATIVE"
    raise AssertionError(f"Unresolved strict sign, no FLOAT or assumed ZERO allowed: {lo},{hi}")


def certificate(bounds, exact_zero=False):
    return {"lower_scaled": str(bounds[0]), "upper_scaled": str(bounds[1]),
            "dyadic_bits": BITS, "sign": sign_bounds(bounds, exact_zero),
            "exact_zero": exact_zero}


class Arithmetic:
    def __init__(self):
        self.limit = max(10000, min(Q, (N - Q - 2) // A))
        self.spf = [0] * (self.limit + 1)
        self.mu_table = [0] * (self.limit + 1)
        self.phi_table = [0] * (self.limit + 1)
        self.mu_table[1] = self.phi_table[1] = 1
        self.primes = []
        for n in range(2, self.limit + 1):
            if self.spf[n] == 0:
                self.spf[n] = n
                self.primes.append(n)
                self.mu_table[n] = -1
                self.phi_table[n] = n - 1
            for p in self.primes:
                if p > self.spf[n] or p * n > self.limit:
                    break
                k = p * n
                self.spf[k] = p
                if n % p == 0:
                    self.mu_table[k] = 0
                    self.phi_table[k] = self.phi_table[n] * p
                else:
                    self.mu_table[k] = -self.mu_table[n]
                    self.phi_table[k] = self.phi_table[n] * (p - 1)
        self.factor_cache = {1: ()}
        self.log_cache = {}
        self.kernels = {}
        self.w_eligible = [k for k in range(1, self.limit + 1)
                           if self.mu_table[k] and gcd(k, N) == 1]
        self.w_small_factors = {k: self.factor(k) for k in self.w_eligible}
        self.log_two_bounds = self._log_direct(Fraction(1, 3))

    @staticmethod
    def _log_direct(z):
        total, power = Fraction(0), z
        for i in range(TERMS):
            total += 2 * power / (2 * i + 1)
            power *= z * z
        tail = 2 * power / ((2 * TERMS + 1) * (1 - z * z))
        assert 0 <= z <= Fraction(1, 3) and tail >= 0
        return total, total + tail

    def factor(self, n):
        assert 1 <= n <= N
        if n in self.factor_cache:
            return self.factor_cache[n]
        original, result = n, []
        if n <= self.limit:
            while n > 1:
                p = self.spf[n]
                result.append(p)
                n //= p
        else:
            for p in self.primes:
                if p * p > n:
                    break
                while n % p == 0:
                    result.append(p)
                    n //= p
            if n > 1:
                result.append(n)
        product = 1
        for p in result:
            product *= p
        assert product == original and result == sorted(result)
        value = tuple(result)
        self.factor_cache[original] = value
        return value

    def prime(self, n):
        return n >= 2 and self.factor(n) == (n,)

    def mu(self, n):
        f = self.factor(n)
        return 0 if len(set(f)) != len(f) else (-1 if len(f) % 2 else 1)

    def max_prime(self, n):
        factors = self.factor(n)
        return factors[-1] if factors else 1

    def divisors(self, n):
        result = [1]
        for p in sorted(set(self.factor(n))):
            count = self.factor(n).count(p)
            old = result[:]
            power = 1
            for _ in range(count):
                power *= p
                result.extend(d * power for d in old)
        result.sort()
        assert len(result) == len(set(result)) and all(n % d == 0 for d in result)
        return result

    def log_vector(self, n):
        result = {}
        for p in self.factor(n):
            result[p] = result.get(p, Fraction(0)) + 1
        return result

    def mangoldt_vector(self, n):
        factors = self.factor(n)
        return {factors[0]: Fraction(1)} if factors and len(set(factors)) == 1 else {}

    def log_bounds(self, n):
        assert n >= 1
        if n in self.log_cache:
            return self.log_cache[n]["bounds"]
        exponent = n.bit_length() - 1
        two_power = 1 << exponent
        z = Fraction(n - two_power, n + two_power)
        low, high = self._log_direct(z)
        low += exponent * self.log_two_bounds[0]
        high += exponent * self.log_two_bounds[1]
        lo = floor_div(low.numerator * SCALE, low.denominator)
        hi = ceil_div(high.numerator * SCALE, high.denominator)
        self.log_cache[n] = {
            "bounds": (lo, hi), "exponent": exponent,
            "z": serialize_fraction(z), "method": "POSITIVE_ATANH48_WITH_GEOMETRIC_TAIL",
        }
        assert lo <= hi and (n != 1 or lo == hi == 0)
        return lo, hi

    def linear_bounds(self, vector):
        lo_total = hi_total = 0
        for p, c in vector.items():
            lo, hi = self.log_bounds(p)
            low_arg, high_arg = (lo, hi) if c >= 0 else (hi, lo)
            lo_total += floor_div(c.numerator * low_arg, c.denominator)
            hi_total += ceil_div(c.numerator * high_arg, c.denominator)
        assert lo_total <= hi_total
        return lo_total, hi_total

    def kernel(self, m):
        assert 1 <= m < N and self.mu(m) != 0
        if m in self.kernels:
            return self.kernels[m]
        n = N - m
        assert gcd(m, N) == gcd(n, N) == 1
        rcap = min(Q, (m - 1) // A)
        assert rcap <= self.limit
        log_m = self.log_vector(m)
        d_vector, w_vector, ua_vector = {}, {}, {}
        d_divisors, head_divisors = [], []
        for k in self.divisors(m):
            if k <= A:
                head_divisors.append(k)
                add_vector(ua_vector, self.log_vector(k), Fraction(self.mu(k)))
            if k <= Q and A * k < m:
                d_divisors.append(k)
                add_vector(d_vector, self.log_vector(k), Fraction(self.mu(k)))
                add_vector(d_vector, log_m, Fraction(-self.mu(k)))
        coefficient_sum, mask = Fraction(0), 0
        active_k = 0
        for k in self.w_eligible:
            if k > rcap:
                break
            if gcd(k, n) != 1:
                continue
            assert k <= Q and A * k < m and gcd(k, n * N) == 1
            c = Fraction(self.mu_table[k], self.phi_table[k])
            for p in self.w_small_factors[k]:
                w_vector[p] = w_vector.get(p, Fraction(0)) + c
            coefficient_sum += c
            mask |= 1 << (k - 1)
            active_k += 1
        add_vector(w_vector, log_m, -coefficient_sum)
        w_vector = {p: c for p, c in w_vector.items() if c}
        c_vector = scaled_vector(d_vector, Fraction(-self.mu(m)))
        add_vector(c_vector, w_vector, Fraction(self.mu(m)))
        rhs_d = self.mangoldt_vector(m)
        add_vector(rhs_d, ua_vector)
        rhs_d = scaled_vector(rhs_d, Fraction(self.mu(m)))
        assert d_vector == rhs_d
        c_bounds = self.linear_bounds(c_vector)
        w_bounds = self.linear_bounds(w_vector)
        d_bounds = self.linear_bounds(d_vector)
        record = {
            "m": m, "first_axis_n": n, "mu_m": self.mu(m),
            "factor_multiset_m": list(self.factor(m)), "R": rcap,
            "D_short_divisors_original_Q_strict_ak_lt_m": d_divisors,
            "whole_Ua_divisors": head_divisors,
            "D_exact": serialize_vector(d_vector), "W_kernel_exact": serialize_vector(w_vector),
            "C_exact": serialize_vector(c_vector), "whole_Ua_exact": serialize_vector(ua_vector),
            "W_active_k_bithex_index_k_minus_1": hex(mask), "W_active_k_count": active_k,
            "C_certificate": certificate(c_bounds, not c_vector),
            "W_kernel_certificate": certificate(w_bounds, not w_vector),
            "D_certificate": certificate(d_bounds, not d_vector),
            "divisor_identity_verified": True,
            "literal_formula": "C=-mu(m)*(D_a(N-m,m)-W_kernel(N-m,m))",
            "original_Q_k1_units_strict_front_and_whole_Ua_retained": True,
        }
        value = {"record": record, "C": c_vector, "W": w_vector, "D": d_vector,
                 "Ua": ua_vector, "C_bounds": c_bounds}
        self.kernels[m] = value
        return value

    def weighted_bounds(self, m, log_base):
        if self.mu(m) == 0:
            return (0, 0), True
        value = self.kernel(m)
        return mul_bounds(value["C_bounds"], self.log_bounds(log_base)), not value["C"]

    def log_catalog(self):
        return {str(n): {"lower_scaled": str(item["bounds"][0]),
                         "upper_scaled": str(item["bounds"][1]),
                         "dyadic_bits": BITS, "exponent": item["exponent"],
                         "z": item["z"], "terms": TERMS, "method": item["method"]}
                for n, item in sorted(self.log_cache.items())}
