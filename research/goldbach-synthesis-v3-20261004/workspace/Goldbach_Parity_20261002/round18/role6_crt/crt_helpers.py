"""Independent integer/rational helpers for the NEW round18 CRT annex.

No historical producer or sign helper is imported.  There is no logarithm,
W/D kernel, Lean subprocess, float, probabilistic primality test or onset.
"""
from fractions import Fraction
from hashlib import sha256
from math import gcd, prod
from pathlib import Path
import json


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def save_exclusive(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write('\n')


def q(value):
    value = Fraction(value)
    return {'numerator': value.numerator, 'denominator': value.denominator,
            'text': str(value)}


def factor_trial(value):
    """Complete deterministic trial division; quotient is checked exactly."""
    assert isinstance(value, int) and value > 0
    remaining, candidate, factors = value, 2, []
    while candidate * candidate <= remaining:
        exponent = 0
        while remaining % candidate == 0:
            remaining //= candidate
            exponent += 1
        if exponent:
            factors.append((candidate, exponent))
        candidate = 3 if candidate == 2 else candidate + 2
    if remaining > 1:
        factors.append((remaining, 1))
    assert prod(p ** e for p, e in factors) == value
    assert all(is_prime_trial(p) and e > 0 for p, e in factors)
    return factors


def is_prime_trial(value):
    if value < 2:
        return False
    candidate = 2
    while candidate * candidate <= value:
        if value % candidate == 0:
            return False
        candidate = 3 if candidate == 2 else candidate + 2
    return True


def divisors_with_moebius(value, factors):
    entries = [(1, [])]
    for p, exponent in factors:
        entries = [(k * p ** e, powers + [e])
                   for k, powers in entries for e in range(exponent + 1)]
    result = []
    for k, powers in sorted(entries):
        mu = 0 if any(e >= 2 for e in powers) else (-1) ** sum(powers)
        assert k > 0 and value % k == 0
        assert prod(p ** e for (p, _), e in zip(factors, powers)) == k
        result.append({'k': k, 'exponents': powers, 'mu': mu,
                       'squarefree': all(e <= 1 for e in powers)})
    assert len(result) == prod(e + 1 for _, e in factors)
    assert len({entry['k'] for entry in result}) == len(result)
    return result


def inverse_mod(value, modulus):
    """Extended Euclid, with its Bezout and inverse equations checked."""
    assert modulus > 0 and gcd(value, modulus) == 1
    old_r, r, old_s, s, old_t, t = value, modulus, 1, 0, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    assert old_r == 1 and old_s * value + old_t * modulus == 1
    result = old_s % modulus
    assert value * result % modulus == 1 % modulus
    return result


def progression_values(A, B, modulus, residue):
    assert 0 <= A <= B and modulus > 0 and 0 <= residue < modulus
    first = residue + ((A - residue) // modulus + 1) * modulus
    return list(range(first, B + 1, modulus)) if first <= B else []


def progression_floor_count(A, B, modulus, residue):
    assert 0 <= A <= B and modulus > 0 and 0 <= residue < modulus
    return (B - residue) // modulus - (A - residue) // modulus


def arithmetic_data(value):
    factors = factor_trial(value)
    divisors = divisors_with_moebius(value, factors)
    density = sum((Fraction(entry['mu'], entry['k']) for entry in divisors),
                  Fraction(0))
    front = sum(abs(entry['mu']) for entry in divisors)
    phi = value
    for p, _ in factors:
        assert phi % p == 0
        phi = phi // p * (p - 1)
    squarefree_count = sum(entry['squarefree'] for entry in divisors)
    assert density == Fraction(phi, value) > 0
    assert front == squarefree_count == 2 ** len(factors)
    return factors, divisors, density, front, phi


def units_check(A, B, value, divisors, density, front, check_indicators=True):
    """Direct gcd count vs full Mobius IE, with every divisor front retained."""
    L = B - A
    units = [b for b in range(A + 1, B + 1) if gcd(b, value) == 1]
    divisor_counts, inclusion = [], 0
    for entry in divisors:
        k, mu = entry['k'], entry['mu']
        first_multiple = (A // k + 1) * k
        direct_count = len(range(first_multiple, B + 1, k))
        floor_count = B // k - A // k
        error = Fraction(direct_count) - Fraction(L, k)
        assert direct_count == floor_count and abs(error) <= 1
        inclusion += mu * direct_count
        divisor_counts.append({**entry, 'direct_multiple_count': direct_count,
                               'floor_multiple_count': floor_count,
                               'main_term': q(Fraction(L, k)),
                               'signed_front': q(error), 'front_at_most_one': True})
    assert len(units) == inclusion
    if check_indicators:
        nonzero = [(entry['k'], entry['mu']) for entry in divisors if entry['mu']]
        for b in range(A + 1, B + 1):
            indicator = sum(mu for k, mu in nonzero if b % k == 0)
            assert indicator == int(gcd(b, value) == 1)
    error = Fraction(len(units)) - L * density
    assert abs(error) <= front
    return units, {'A_excluded': A, 'B_included': B, 'L': L, 'modulus': value,
                   'direct_gcd_count': len(units), 'full_moebius_IE_count': inclusion,
                   'all_divisor_counts': divisor_counts, 'main_term': q(L * density),
                   'signed_front': q(error), 'front_bound': front,
                   'front_bound_verified': True,
                   'every_integer_indicator_verified': check_indicators}
