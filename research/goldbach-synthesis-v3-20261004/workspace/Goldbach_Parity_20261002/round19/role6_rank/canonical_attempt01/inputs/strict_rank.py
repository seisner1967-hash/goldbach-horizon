"""NEW integer-only all-rank arithmetic; no work occurs on import.

No W/D, kernel, parent resource, old-bank import or singular-series evaluation.
Positive atanh series use outward INTEGER interval arithmetic at every step.
"""
from fractions import Fraction
from math import gcd

N, A, Q, M, H, P = 100000000, 3163, 999999, 1000000, 39, 1771
LEFT, RIGHT, START = 12000000, 24000000, 12000001
BITS, TERMS, SCALE = 128, 48, 1 << 128
S_BOX = (Fraction(2541, 1536), Fraction(11011, 6144))


def ceildiv(a, b):
    assert b > 0
    return -((-a) // b)


def fracstr(value):
    return f"{value.numerator}/{value.denominator}"


def scaled_bounds(value):
    return value.numerator * SCALE // value.denominator, ceildiv(value.numerator * SCALE, value.denominator)


def scale(bounds, value):
    lo, hi = bounds if value >= 0 else (bounds[1], bounds[0])
    return value.numerator * lo // value.denominator, ceildiv(value.numerator * hi, value.denominator)


def mul(a, b):
    products = [x * y for x in a for y in b]
    return min(products) // SCALE, ceildiv(max(products), SCALE)


def cert(bounds, zero=False):
    lo, hi = bounds
    assert lo <= hi
    if zero:
        assert lo == hi == 0
        sign = "ZERO"
    elif lo > 0:
        sign = "POSITIVE"
    elif hi < 0:
        sign = "NEGATIVE"
    else:
        raise AssertionError(f"Unresolved point sign; no float or assumed zero: {lo},{hi}")
    return {"lower_scaled": str(lo), "upper_scaled": str(hi), "dyadic_bits": BITS,
            "exact_zero": zero, "sign": sign}


def interval_data(bounds):
    assert bounds[0] <= bounds[1]
    return {"lower_scaled": str(bounds[0]), "upper_scaled": str(bounds[1]), "dyadic_bits": BITS}


def addvec(target, source, coefficient=Fraction(1)):
    for base, count in source.items():
        value = target.get(base, Fraction(0)) + count * coefficient
        if value:
            target[base] = value
        elif base in target:
            del target[base]


class Strict:
    def __init__(self):
        table = bytearray(b"\x01") * 10001
        table[0:2] = b"\x00\x00"
        for p in range(2, 101):
            if table[p]:
                table[p*p:10001:p] = b"\x00" * (((10000-p*p)//p)+1)
        self.primes = [p for p in range(2, 10001) if table[p]]
        self.prime_set = set(self.primes)
        self.logs = {}
        self.factor_cache = {1: ()}
        self.log2 = self._atanh_interval(1, 3)

    @staticmethod
    def _atanh_interval(numerator, denominator):
        assert 0 <= 3 * numerator <= denominator
        zlo, zhi = numerator * SCALE // denominator, ceildiv(numerator * SCALE, denominator)
        z2lo, z2hi = zlo*zlo//SCALE, ceildiv(zhi*zhi, SCALE)
        plo, phi, lo, hi = zlo, zhi, 0, 0
        for i in range(TERMS):
            lo += (2*plo)//(2*i+1)
            hi += ceildiv(2*phi, 2*i+1)
            plo, phi = plo*z2lo//SCALE, ceildiv(phi*z2hi, SCALE)
        # power encloses z^(2*TERMS+1); denominator uses an UPPER z^2.
        hi += ceildiv(2*phi*SCALE, (2*TERMS+1)*(SCALE-z2hi))
        return lo, hi

    def log(self, n):
        assert n >= 1
        if n not in self.logs:
            exponent = n.bit_length()-1
            power = 1 << exponent
            lo, hi = self._atanh_interval(n-power, n+power)
            self.logs[n] = (lo + exponent*self.log2[0], hi + exponent*self.log2[1])
        return self.logs[n]

    def vector_bounds(self, vector):
        lo = hi = 0
        for p, coefficient in vector.items():
            low, high = scale(self.log(p), coefficient)
            lo += low
            hi += high
        return lo, hi

    def factor_small_product(self, n):
        """Every caller supplies a product of primes from the COMPLETE <=10000 table.

        All such factors are removed.  A leftover is an error, never an
        untested prime promoted from trial division with insufficient depth.
        """
        assert n >= 1
        if n not in self.factor_cache:
            rest, factors = n, []
            for p in self.primes:
                while rest % p == 0:
                    factors.append(p)
                    rest //= p
                if rest == 1:
                    break
            assert rest == 1
            product = 1
            for p in factors:
                product *= p
            assert product == n
            self.factor_cache[n] = tuple(factors)
        return self.factor_cache[n]

    def phi(self, n):
        value = n
        for p in set(self.factor_small_product(n)):
            value = value//p*(p-1)
        return value

    def mu(self, n):
        factors = self.factor_small_product(n)
        return 0 if len(set(factors)) != len(factors) else (-1 if len(factors) % 2 else 1)

    def rad(self, n):
        value = 1
        for p in set(self.factor_small_product(n)):
            value *= p
        return value

    def divisors(self, n):
        factors = self.factor_small_product(n)
        values = [1]
        for p in sorted(set(factors)):
            old, power = values[:], 1
            for _ in range(factors.count(p)):
                power *= p
                values.extend(d*power for d in old)
        values.sort()
        assert len(values) == len(set(values))
        return values

    def unit_ie(self, lo, hi, modulus, face=1):
        assert gcd(modulus,face)==1
        original = self.divisors(modulus)
        entries = [[d, self.mu(d)] for d in original]  # includes ALL mu=0 divisors
        total = sum(mu*(hi//(d*face)-(lo-1)//(d*face)) for d, mu in entries)
        eta = sum(abs(mu) for _, mu in entries)
        delta = Fraction(self.phi(modulus), modulus)
        length = max(0, hi-lo+1)
        assert abs(Fraction(total)-length*delta/face) <= eta
        return total, {"modulus": modulus, "face": face, "delta": fracstr(delta), "eta": eta,
                       "complete_divisors_including_mu0": entries, "integer_count": total,
                       "L": length, "IE_count_error_abs_le_eta": True}

    def candidate_sieve(self):
        width = RIGHT-LEFT
        flags = bytearray(b"\x01")*width
        base = [p for p in self.primes if p*p <= RIGHT]
        for p in base:
            first = max(p*p, ceildiv(START,p)*p)
            if first <= RIGHT:
                flags[first-START:width:p] = b"\x00"*((RIGHT-first)//p+1)
        assert base[-1]*base[-1] <= RIGHT and (4899)**2 > RIGHT
        proper = []
        for p in base:
            value, exponent = p*p, 2
            while value <= RIGHT:
                if value > LEFT:
                    assert not flags[value-START]
                    proper.append([value,p,exponent])
                value *= p
                exponent += 1
        proper.sort()
        assert len({value for value, _, _ in proper}) == len(proper)
        return flags, base, proper
