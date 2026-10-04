"""NEW exact friable20 arithmetic and source kernels, no old executable imports."""
from __future__ import annotations

from array import array
from fractions import Fraction
import hashlib
from math import gcd, isqrt, prod

from outward import LogOracle, Iv, absolute_lower, absolute_upper, add, iv_json, mul, scale

N = 100_000_000
ALPHA = 100
Q = 999_999
A = 3163
M = 1_000_000
Z = 100
P0 = 3
D = 10_000
Y_TEST = 4096
QLO = 1_800_100
QHI = 1_801_100


def text(value: Fraction | int) -> str:
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def vector_json(vector: dict[int, Fraction]) -> list:
    return [[p, text(coefficient)] for p, coefficient in sorted(vector.items()) if coefficient]


def add_vector(target: dict[int, Fraction], source: dict[int, Fraction], coefficient: Fraction | int = 1) -> None:
    for p, value in source.items():
        updated = target.get(p, Fraction(0)) + coefficient * value
        if updated:
            target[p] = updated
        elif p in target:
            del target[p]


def strict_certificate(bounds: Iv, exact_zero: bool = False) -> dict:
    if exact_zero:
        assert bounds == (0, 0)
    encoded = iv_json(bounds)
    assert encoded["sign"] != "UNRESOLVED_SIGN_INTERVAL", encoded
    return encoded


def abs_interval(bounds: Iv) -> Iv:
    return absolute_lower(bounds), absolute_upper(bounds)


def nth_root_floor(value: int, degree: int) -> int:
    assert value >= 0 and degree >= 1
    lo, hi = 0, 1 << ((value.bit_length() + degree - 1) // degree)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** degree <= value:
            lo = mid
        else:
            hi = mid
    if hi ** degree <= value:
        lo = hi
    assert lo ** degree <= value < (lo + 1) ** degree
    return lo


def root_interval(value: int, degree: int, bits: int = 128) -> tuple[Iv, dict]:
    unit = 1 << bits
    target = value * unit ** degree
    floor = nth_root_floor(target, degree)
    interval = (Fraction(floor, unit), Fraction(floor + 1, unit))
    return interval, {"value": value, "degree": degree, "bits": bits,
                      "floor_scaled": floor, "power_inequalities_exact": True,
                      "interval": iv_json(interval)}


def exp_interval(bounds: Iv, terms: int = 64) -> Iv:
    assert 0 <= bounds[0] <= bounds[1] < terms + 2
    values = []
    for x in bounds:
        term = total = Fraction(1)
        for k in range(1, terms + 1):
            term = term * x / k
            total += term
        next_term = term * x / (terms + 1)
        tail = next_term / (1 - x / (terms + 2))
        values.append((total, total + tail))
    return values[0][0], values[1][1]


class Arithmetic:
    def __init__(self, oracle: LogOracle):
        self.oracle = oracle
        self.limit = Q
        self.spf = array("I", [0]) * (Q + 1)
        self.phi = array("I", [0]) * (Q + 1)
        self.mu = array("b", [0]) * (Q + 1)
        self.phi[1] = 1
        self.mu[1] = 1
        self.primes = []
        for n in range(2, Q + 1):
            if not self.spf[n]:
                self.spf[n] = n
                self.phi[n] = n - 1
                self.mu[n] = -1
                self.primes.append(n)
            for p in self.primes:
                value = n * p
                if value > Q:
                    break
                self.spf[value] = p
                if n % p == 0:
                    self.phi[value] = self.phi[n] * p
                    self.mu[value] = 0
                    break
                self.phi[value] = self.phi[n] * (p - 1)
                self.mu[value] = -self.mu[n]
        self.factor_cache = {1: ()}
        self.kernel_cache = {}
        self.prefix_cache = {}
        self.prefix_vector = {}
        self.prefix_coefficient = Fraction(0)
        self.prefix_active = []
        self.prefix_mask = 0
        self.prefix_position = 0
        self.tk = [Fraction(0)]
        for k in range(1, (N - 1) // A + 1):
            self.tk.append(self.tk[-1] + Fraction(1, self.phi[k]))

    def factors(self, n: int) -> tuple[tuple[int, int], ...]:
        assert n >= 1
        if n in self.factor_cache:
            return self.factor_cache[n]
        remainder = n
        result = []
        if n <= self.limit:
            while remainder > 1:
                p = self.spf[remainder]
                exponent = 0
                while remainder % p == 0:
                    remainder //= p
                    exponent += 1
                result.append((p, exponent))
        else:
            for p in self.primes:
                if p * p > remainder:
                    break
                exponent = 0
                while remainder % p == 0:
                    remainder //= p
                    exponent += 1
                if exponent:
                    result.append((p, exponent))
            if remainder > 1:
                result.append((remainder, 1))
        assert prod(p ** exponent for p, exponent in result) == n
        answer = tuple(result)
        self.factor_cache[n] = answer
        return answer

    def record(self, n: int) -> dict:
        factors = self.factors(n)
        sf = all(exponent == 1 for _, exponent in factors)
        prime = len(factors) == 1 and factors[0][1] == 1
        multiset = [p for p, exponent in factors for _ in range(exponent)]
        terminal = factors[-1][0] if factors else 0
        return {"n": n, "factors": factors, "factor_multiset": multiset,
                "Omega": len(multiset), "terminalPrime": terminal,
                "cofactor": n // terminal if terminal else 0,
                "squarefree": sf, "mu": (-1) ** len(factors) if sf else 0,
                "tau": prod(exponent + 1 for _, exponent in factors),
                "prime": prime, "properpower": len(factors) == 1 and factors[0][1] > 1,
                "largestPrime": terminal or 1, "unit_N": gcd(n, N) == 1,
                "unit_complement": gcd(n, N - n) == 1 if n < N else None}

    def log_vector(self, n: int) -> dict[int, Fraction]:
        return {p: Fraction(exponent) for p, exponent in self.factors(n)}

    def mu_value(self, n: int) -> int:
        if n <= self.limit:
            return int(self.mu[n])
        factors = self.factors(n)
        return 0 if any(exponent > 1 for _, exponent in factors) else (-1) ** len(factors)

    def phi_value(self, n: int) -> int:
        if n <= self.limit:
            return int(self.phi[n])
        result = n
        for p, _ in self.factors(n):
            result = result // p * (p - 1)
        return result

    def divisors(self, n: int) -> list[int]:
        values = [1]
        for p, exponent in self.factors(n):
            values = [d * p ** e for d in values for e in range(exponent + 1)]
        return sorted(values)

    def prepare_prefixes(self, requested: list[int]) -> None:
        for cap in sorted(set(requested)):
            assert cap <= (N - 1) // A
            while self.prefix_position < cap:
                self.prefix_position += 1
                k = self.prefix_position
                if not self.mu[k] or gcd(k, N) != 1:
                    continue
                coefficient = Fraction(self.mu[k], self.phi[k])
                add_vector(self.prefix_vector, self.log_vector(k), coefficient)
                self.prefix_coefficient += coefficient
                self.prefix_active.append(k)
                self.prefix_mask |= 1 << (k - 1)
            self.prefix_cache[cap] = (self.prefix_vector.copy(), self.prefix_coefficient,
                                      len(self.prefix_active), self.prefix_mask)

    def kernel(self, m: int) -> dict:
        if m in self.kernel_cache:
            return self.kernel_cache[m]
        n = N - m
        assert 1 <= n and gcd(m, N) == gcd(n, N) == 1
        mu_m = self.mu_value(m)
        if mu_m == 0:
            result = {"m": m, "n": n, "mu_m": 0, "C_vector": {}, "C_bounds": (Fraction(0), Fraction(0)),
                      "record": {"m": m, "first_axis_n": n, "mu_m": 0,
                                 "factor_multiset": self.record(m)["factor_multiset"],
                                 "C_exact": [], "C_certificate": strict_certificate((Fraction(0), Fraction(0)), True),
                                 "kernel_not_evaluated": "outer_mu_zero_literal"}}
            self.kernel_cache[m] = result
            return result
        cap = min(Q, (m - 1) // A)
        assert cap in self.prefix_cache
        dvec, uavec = {}, {}
        divisors = []
        short = []
        for k in self.divisors(m):
            if k <= A:
                short.append(k)
                add_vector(uavec, self.log_vector(k), self.mu_value(k))
            if k <= Q and A * k < m and gcd(k, n * N) == 1:
                divisors.append(k)
                add_vector(dvec, self.log_vector(k), self.mu_value(k))
                add_vector(dvec, self.log_vector(m), -self.mu_value(k))
        wvec, coefficient_sum, active_count, active_mask = self.prefix_cache[cap]
        wvec = wvec.copy()
        removed = []
        for k in range(1, cap + 1):
            if self.mu[k] and gcd(k, N) == 1 and gcd(k, n) != 1:
                coefficient = Fraction(self.mu[k], self.phi[k])
                add_vector(wvec, self.log_vector(k), -coefficient)
                coefficient_sum -= coefficient
                active_count -= 1
                active_mask &= ~(1 << (k - 1))
                removed.append(k)
        add_vector(wvec, self.log_vector(m), -coefficient_sum)
        cvec = {}
        add_vector(cvec, dvec, -mu_m)
        add_vector(cvec, wvec, mu_m)
        mangoldt = {self.factors(m)[0][0]: Fraction(1)} if len(self.factors(m)) == 1 else {}
        rhs_d = {}
        add_vector(rhs_d, mangoldt, mu_m)
        add_vector(rhs_d, uavec, mu_m)
        assert dvec == rhs_d
        assert active_count == active_mask.bit_count()
        bounds = self.oracle.vector(cvec)
        dbounds, wbounds = self.oracle.vector(dvec), self.oracle.vector(wvec)
        record = {"m": m, "first_axis_n": n, "mu_m": mu_m, "factor_multiset": self.record(m)["factor_multiset"],
                  "R": cap, "original_Q": Q, "strict_front_zero_k_above_R_count": Q - cap,
                  "D_selected_divisors": divisors, "whole_Ua_selected_divisors": short,
                  "D_exact": vector_json(dvec), "W_exact": vector_json(wvec), "C_exact": vector_json(cvec),
                  "whole_Ua_exact": vector_json(uavec), "D_certificate": strict_certificate(dbounds, not dvec),
                  "W_certificate": strict_certificate(wbounds, not wvec), "C_certificate": strict_certificate(bounds, not cvec),
                  "W_active_k_bithex_index_k_minus_1": hex(active_mask), "W_active_k_count": active_count,
                  "W_n_nonunit_removed_k": removed, "W_coefficient_sum": text(coefficient_sum),
                  "prefix_equivalence": "all k in1..Q: k>R iff strictfront fails; mu0 and nonunits zero; remaining exactmu/phi log(k/m)",
                  "source_divisor_identity_verified": True, "TK_R": text(self.tk[cap])}
        result = {"m": m, "n": n, "mu_m": mu_m, "C_vector": cvec, "C_bounds": bounds,
                  "D_vector": dvec, "W_vector": wvec, "Ua_vector": uavec,
                  "D_bounds": dbounds, "W_bounds": wbounds, "record": record}
        self.kernel_cache[m] = result
        return result

    def arithmetic_metadata(self) -> dict:
        return {"full_Q": Q, "integer_axes": Q, "mu_signed_byte_sha256": hashlib.sha256(self.mu.tobytes()).hexdigest(),
                "phi_uint32_native_bytes_sha256": hashlib.sha256(self.phi.tobytes()).hexdigest(),
                "spf_uint32_native_bytes_sha256": hashlib.sha256(self.spf.tobytes()).hexdigest(),
                "table_integer_endianness": "native Windows little-endian", "mu0_count": self.mu[1:].count(0),
                "all1throughQ_defined": True, "prefixes_only_remove_proven_zero_terms": True}
