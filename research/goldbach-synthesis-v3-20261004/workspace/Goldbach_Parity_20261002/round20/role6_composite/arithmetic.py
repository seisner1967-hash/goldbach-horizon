"""NEW composite20 integer arithmetic; imported only by the gated new producer."""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, lcm, prod

N = 100_000_000
LEFT = 24_000_000
RIGHT = 48_000_000
A = 3163
ALPHA = 100
Q_ORIGINAL = 999_999
M = 1_000_000
H = 39


def ceildiv(n: int, d: int) -> int:
    return -((-n) // d)


def sieve(bound: int) -> tuple[list[int], bytearray]:
    flags = bytearray(b"\x01") * (bound + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, isqrt(bound) + 1):
        if flags[p]:
            start = p * p
            flags[start:bound + 1:p] = b"\x00" * ((bound - start) // p + 1)
    return [p for p in range(2, bound + 1) if flags[p]], flags


def segment(primes: list[int]) -> bytearray:
    start = LEFT + 1
    flags = bytearray(b"\x01") * (RIGHT - LEFT)
    for p in primes:
        if p * p > RIGHT:
            break
        first = max(p * p, ceildiv(start, p) * p)
        if first <= RIGHT:
            flags[first - start:RIGHT - start + 1:p] = b"\x00" * ((RIGHT - first) // p + 1)
    return flags


def factor(n: int, primes: list[int]) -> list[tuple[int, int]]:
    assert n >= 1
    remainder = n
    factors = []
    for p in primes:
        if p * p > remainder:
            break
        exponent = 0
        while remainder % p == 0:
            remainder //= p
            exponent += 1
        if exponent:
            factors.append((p, exponent))
    if remainder > 1:
        factors.append((remainder, 1))
    assert prod(p ** e for p, e in factors) == n
    return factors


def phi(n: int, primes: list[int]) -> int:
    result = n
    for p, _ in factor(n, primes):
        result = result // p * (p - 1)
    return result


def mobius(n: int, primes: list[int]) -> int:
    factors = factor(n, primes)
    return 0 if any(e > 1 for _, e in factors) else (-1) ** len(factors)


def all_divisors(n: int, primes: list[int]) -> list[int]:
    divisors = [1]
    for p, exponent in factor(n, primes):
        divisors = [d * p ** e for d in divisors for e in range(exponent + 1)]
    return sorted(divisors)


def frac(value: Fraction | int) -> str:
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def add_map(target: dict[int, Fraction], source: dict[int, Fraction], coefficient: Fraction | int = 1) -> None:
    for key, value in source.items():
        updated = target.get(key, Fraction(0)) + coefficient * value
        if updated:
            target[key] = updated
        elif key in target:
            del target[key]


def map_json(values: dict[int, Fraction]) -> list[list[int | str]]:
    return [[key, frac(value)] for key, value in sorted(values.items()) if value]


def actual_weights(z: int, t: int, p0: int, primes: list[int]) -> dict:
    original = []
    active = []
    for k in range(1, z + 1):
        mu = mobius(k, primes)
        factors = factor(k, primes)
        admitted = mu != 0 and gcd(k, t * N * p0) == 1
        record = {"k": k, "mu": mu, "prime_factors_with_multiplicity": factors,
                  "squarefree": mu != 0, "unit_tNp0": gcd(k, t * N * p0) == 1,
                  "active": admitted}
        original.append(record)
        if admitted:
            active.append(k)
    r = {e: prod(p - 2 for p, _ in factor(e, primes)) for e in active}
    assert all(value > 0 for value in r.values())
    g = sum((Fraction(1, r[e]) for e in active), Fraction(0))
    lambdas = {k: Fraction(mobius(k, primes) * phi(k, primes), 1) / g
               * sum((Fraction(1, r[e]) for e in active if e % k == 0), Fraction(0))
               for k in active}
    assert lambdas[1] == 1
    quadratic = sum((lambdas[k] * lambdas[l] / phi(lcm(k, l), primes)
                     for k in active for l in active), Fraction(0))
    assert quadratic == 1 / g
    for record in original:
        record["lambda"] = frac(lambdas.get(record["k"], Fraction(0)))
    return {"z": z, "original": original, "active": active, "r": r,
            "G": g, "lambdas": lambdas, "Q": quadratic}


def bonferroni_catalog(p: int, t: int, k_order: int, primes: list[int]) -> dict:
    eligible = [ell for ell in primes if ell < p and gcd(ell, t * N) == 1]
    original = []
    active = []
    for size in range(len(eligible) + 1):
        for subset in combinations(eligible, size):
            h = prod(subset)
            xi = (-1) ** size if size <= 2 * k_order + 1 else 0
            original.append({"h": h, "prime_factors": list(subset), "omega": size, "xi": xi})
            if xi:
                active.append((h, xi))
    return {"p": p, "eligible_primes": eligible, "primorial": prod(eligible),
            "original": sorted(original, key=lambda row: row["h"]), "active": sorted(active)}


def properpowers(primes: list[int]) -> dict[int, tuple[int, int]]:
    result = {}
    for p in primes:
        if p * p > RIGHT:
            break
        exponent = 2
        value = p * p
        while value <= RIGHT:
            if value > LEFT:
                assert value not in result
                result[value] = (p, exponent)
            value *= p
            exponent += 1
    return dict(sorted(result.items()))
