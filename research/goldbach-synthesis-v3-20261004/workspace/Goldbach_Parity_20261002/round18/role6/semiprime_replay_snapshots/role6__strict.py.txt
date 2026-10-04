"""New self-contained exact arithmetic; no historical producer imports."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from functools import lru_cache
from fractions import Fraction
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json

N, ALPHA, A, Q, M = 100000000, 100, 3163, 999999, 1000000
BITS, TERMS = 128, 48
SCALE = 1 << BITS


def primes_through(limit):
    flag = bytearray(b'\x01') * (limit + 1)
    flag[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flag[p]:
            flag[p * p:limit + 1:p] = b'\x00' * ((limit - p * p) // p + 1)
    return tuple(p for p in range(2, limit + 1) if flag[p])


PRIMES = primes_through(10000)


@lru_cache(maxsize=None)
def factor(n):
    assert isinstance(n, int) and 1 <= n <= N
    left, out = n, []
    for p in PRIMES:
        if p * p > left:
            break
        if left % p == 0:
            exponent = 0
            while left % p == 0:
                exponent += 1
                left //= p
            out.append((p, exponent))
    if left > 1:
        out.append((left, 1))
    assert n == product(p ** exponent for p, exponent in out)
    return tuple(out)


def product(values):
    result = 1
    for value in values:
        result *= value
    return result


def prime(n):
    return n >= 2 and factor(n) == ((n, 1),)


def rad_components(*values):
    return product(sorted({p for n in values for p, _ in factor(n)}))


def digest(path):
    h = sha256()
    with Path(path).open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def ceildiv(a, b):
    return -(-a // b)


def bithex(values):
    output = bytearray((len(values) + 7) // 8)
    for i, value in enumerate(values):
        if value:
            output[i // 8] |= 1 << (i % 8)
    return output.hex()


def factor_column(values):
    return ';'.join('*'.join(str(p) + '^' + str(exponent) for p, exponent in factor(n)) for n in values)


def _atanh_dyadic(a, b):
    """Outward rational bounds for 2 atanh(a/b), 0<=a/b<=1/3."""
    assert 0 <= 3 * a <= b and b > 0
    if a == 0:
        return 0, 0
    ap, bp, lower = a, b, 0
    for i in range(TERMS):
        lower += (2 * ap * SCALE) // ((2 * i + 1) * bp)
        ap *= a * a
        bp *= b * b
    tail = ceildiv(2 * ap * b * b * SCALE, (2 * TERMS + 1) * bp * (b * b - a * a))
    return lower, lower + TERMS + tail


LOG2 = _atanh_dyadic(1, 3)


@lru_cache(maxsize=None)
def log_dyadic(n):
    assert isinstance(n, int) and n >= 1
    k = n.bit_length() - 1
    base = 1 << k
    lo, hi = _atanh_dyadic(n - base, n + base)
    return k * LOG2[0] + lo, k * LOG2[1] + hi


def log_bounds(n):
    lo, hi = log_dyadic(n)
    return Fraction(lo, SCALE), Fraction(hi, SCALE)


def add(target, vector, scale=Fraction(1)):
    for p, value in vector.items():
        updated = target.get(p, Fraction(0)) + value * scale
        if updated:
            target[p] = updated
        else:
            target.pop(p, None)


def scaled(vector, scale):
    return {p: value * scale for p, value in vector.items() if value * scale}


def difference(left, right):
    result = dict(left)
    add(result, right, -1)
    return result


def scalar_certificate(value):
    value = Fraction(value)
    return {'sign': 'POSITIVE' if value > 0 else ('NEGATIVE' if value < 0 else 'ZERO'),
            'lower': str(value), 'upper': str(value), 'rational_exact': True}


def certify_bounds(lower, upper):
    assert lower <= upper
    sign = 'POSITIVE' if lower > 0 else ('NEGATIVE' if upper < 0 else ('ZERO' if lower == upper == 0 else 'UNRESOLVED'))
    assert sign != 'UNRESOLVED', (lower, upper)
    return {'sign': sign, 'lower': str(lower), 'upper': str(upper),
            'strict_rational_bounds': True, 'log_bits': BITS, 'atanh_terms': TERMS}


def vector_certificate(vector, constant=Fraction(0)):
    lower = upper = Fraction(constant)
    for p, coefficient in vector.items():
        lo, hi = log_bounds(p)
        if coefficient >= 0:
            lower += coefficient * lo
            upper += coefficient * hi
        else:
            lower += coefficient * hi
            upper += coefficient * lo
    return certify_bounds(lower, upper)


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n', encoding='utf-8')
