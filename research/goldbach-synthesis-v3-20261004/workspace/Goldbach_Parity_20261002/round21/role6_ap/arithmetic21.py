"""NEW AP21 integer arithmetic and complete candidate factor bitmap."""
from __future__ import annotations

from array import array
from fractions import Fraction
import hashlib
from math import gcd, isqrt, prod
from pathlib import Path

N = 100_000_000
X = 25_000_000
LEFT = 12_500_000
RIGHT = 25_000_000


def ceildiv(n: int, d: int) -> int:
    assert n >= 0 and d > 0
    return (n + d - 1) // d


def floor_power(n: int, numerator: int, denominator: int) -> int:
    target = n ** numerator
    lo, hi = 0, n + 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** denominator <= target:
            lo = mid
        else:
            hi = mid
    assert lo ** denominator <= target < (lo + 1) ** denominator
    return lo


def ceil_power(n: int, numerator: int, denominator: int) -> int:
    lo = floor_power(n, numerator, denominator)
    return lo if lo ** denominator == n ** numerator else lo + 1


def sieve(limit: int) -> tuple[list[int], bytearray]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            start = p * p
            flags[start:limit + 1:p] = b"\x00" * ((limit - start) // p + 1)
    return [p for p in range(2, limit + 1) if flags[p]], flags


def factor(n: int, primes: list[int]) -> list[tuple[int, int]]:
    assert n >= 1
    remaining = n
    result = []
    for p in primes:
        if p * p > remaining:
            break
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        if exponent:
            result.append((p, exponent))
    if remaining > 1:
        result.append((remaining, 1))
    assert prod(p ** e for p, e in result) == n
    return result


def phi(n: int, primes: list[int]) -> int:
    value = n
    for p, _ in factor(n, primes):
        value = value // p * (p - 1)
    return value


def mu(n: int, primes: list[int]) -> int:
    factors = factor(n, primes)
    return 0 if any(e > 1 for _, e in factors) else (-1) ** len(factors)


def canonical_p0(primes: list[int]) -> int:
    p0 = next(p for p in primes if p > 2 and N % p)
    assert all(N % p == 0 for p in primes if 2 < p < p0)
    return p0


def fraction_text(value: Fraction | int) -> str:
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def vector_json(vector: dict[int, Fraction | int]) -> list[list]:
    return [[key, fraction_text(value)] for key, value in sorted(vector.items()) if value]


def add_vector(target: dict, source: dict, coefficient: Fraction | int = 1) -> None:
    for key, value in source.items():
        new = target.get(key, Fraction(0)) + coefficient * value
        if new:
            target[key] = new
        else:
            target.pop(key, None)


def candidate_bitmap(primes: list[int], output: Path) -> tuple[dict, dict]:
    """Factor EVERY integer first; no q, prime, unit or squarefree preselection."""
    count = RIGHT - LEFT
    start = LEFT + 1
    residual = array("I", range(start, RIGHT + 1))
    least = array("I", [0]) * count
    omega_total = bytearray(count)
    omega_distinct = bytearray(count)
    repeated = bytearray(count)
    for p in primes:
        if p * p > RIGHT:
            break
        for j in range(ceildiv(start, p) * p, RIGHT + 1, p):
            i = j - start
            if not least[i]:
                least[i] = p
            exponent = 0
            while residual[i] % p == 0:
                residual[i] //= p
                exponent += 1
            assert exponent >= 1
            omega_total[i] += exponent
            omega_distinct[i] += 1
            repeated[i] |= exponent > 1
    flags = bytearray(count)
    counts = {"all_integers": count, "prime": 0, "unit_N": 0,
              "squarefree": 0, "mu_zero": 0, "properpowers": 0}
    properpowers = {}
    digest = hashlib.sha256()
    for i in range(count):
        j = start + i
        if residual[i] > 1:
            omega_total[i] += 1
            omega_distinct[i] += 1
            if not least[i]:
                least[i] = residual[i]
        assert least[i] >= 2 and 1 <= omega_distinct[i] <= omega_total[i] <= 255
        prime = omega_total[i] == 1
        unit = j % 2 != 0 and j % 5 != 0
        squarefree = not repeated[i]
        power = omega_distinct[i] == 1 and omega_total[i] >= 2
        flags[i] = (int(prime) | (int(unit) << 1) | (int(squarefree) << 2)
                    | (int(power) << 3) | ((omega_distinct[i] & 1) << 4))
        counts["prime"] += prime
        counts["unit_N"] += unit
        counts["squarefree"] += squarefree
        counts["mu_zero"] += not squarefree
        counts["properpowers"] += power
        if power:
            assert least[i] ** omega_total[i] == j
            properpowers[j] = (least[i], omega_total[i])
        digest.update(j.to_bytes(4, "little"))
        digest.update(least[i].to_bytes(4, "little"))
        digest.update(bytes((omega_total[i], omega_distinct[i], flags[i])))
    paths = {}
    for name, data in (("candidate_flags.bin", flags), ("candidate_minfac_u32.bin", least),
                       ("candidate_total_omega.bin", omega_total),
                       ("candidate_distinct_omega.bin", omega_distinct)):
        path = output / name
        with path.open("xb") as handle:
            if isinstance(data, array):
                assert data.itemsize == 4
                data.tofile(handle)
            else:
                handle.write(data)
        paths[name] = str(path)
    independently_generated = {}
    for p in primes:
        if p * p > RIGHT:
            break
        exponent, value = 2, p * p
        while value <= RIGHT:
            if value > LEFT:
                independently_generated[value] = (p, exponent)
            exponent += 1
            value *= p
    assert properpowers == independently_generated
    metadata = {"bounds": [LEFT + 1, RIGHT], "count": count, "counts": counts,
                "files": paths, "per_integer_factor_encoding_sha256": digest.hexdigest(),
                "prime_factor_sieve_bound": isqrt(RIGHT),
                "all_candidates_before_masks": True,
                "factorization_with_multiplicity": True,
                "properpowers": [[j, p, e] for j, (p, e) in sorted(properpowers.items())],
                "properpowers_independent_generation_equal": True,
                "flag_bits": {"prime": 0, "unit_N": 1, "squarefree": 2,
                              "properpower": 3, "omega_distinct_odd": 4}}
    return {"flags": flags, "least": least, "omega": omega_total,
            "distinct": omega_distinct, "properpowers": properpowers}, metadata


def bitmap_observation(j: int, bitmap: dict, primes: list[int]) -> dict:
    assert LEFT < j <= RIGHT
    i = j - LEFT - 1
    factors = factor(j, primes)
    assert bitmap["least"][i] == factors[0][0]
    assert bitmap["omega"][i] == sum(e for _, e in factors)
    assert bitmap["distinct"][i] == len(factors)
    return {"j": j, "prime": bool(bitmap["flags"][i] & 1),
            "unit_N": bool(bitmap["flags"][i] & 2),
            "squarefree": bool(bitmap["flags"][i] & 4),
            "properpower": bool(bitmap["flags"][i] & 8),
            "mu": 0 if not (bitmap["flags"][i] & 4) else (-1) ** len(factors),
            "minfac": factors[0][0], "factors_with_multiplicity": factors}
