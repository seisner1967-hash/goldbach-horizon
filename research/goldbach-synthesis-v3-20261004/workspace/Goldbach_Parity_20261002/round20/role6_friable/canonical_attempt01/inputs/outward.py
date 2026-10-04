"""NEW directed integer log bounds, rational intervals and stored certificates20.

Each atanh term is floored at 2^128. Its upper error is <1 unit.
For a/b <=1/3 the positive remaining series is bounded by
2(a/b)^(2K+1)/((2K+1)(1-(a/b)^2)). No float is used.
"""
from __future__ import annotations

from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path

BITS = 128
SCALE = 1 << BITS
TERMS = 48
Iv = tuple[Fraction, Fraction]


def fraction_text(value: Fraction | int) -> str:
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def iv_json(value: Iv) -> dict:
    assert value[0] <= value[1]
    label = ("ZERO" if value == (0, 0) else "POS" if value[0] > 0
             else "NEG" if value[1] < 0 else "UNRESOLVED_SIGN_INTERVAL")
    return {"lo": fraction_text(value[0]), "hi": fraction_text(value[1]),
            "width": fraction_text(value[1] - value[0]), "sign": label}


def add(a: Iv, b: Iv) -> Iv:
    return a[0] + b[0], a[1] + b[1]


def neg(a: Iv) -> Iv:
    return -a[1], -a[0]


def scale(a: Iv, coefficient: Fraction | int) -> Iv:
    pair = coefficient * a[0], coefficient * a[1]
    return min(pair), max(pair)


def mul(a: Iv, b: Iv) -> Iv:
    values = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(values), max(values)


def absolute_upper(a: Iv) -> Fraction:
    return max(abs(a[0]), abs(a[1]))


def absolute_lower(a: Iv) -> Fraction:
    return a[0] if a[0] > 0 else -a[1] if a[1] < 0 else Fraction(0)


def _atanh_series(a: int, b: int) -> tuple[int, int]:
    assert 0 <= a < b and 3 * a <= b
    if a == 0:
        return 0, 0
    ap, bp = a, b
    lower = 0
    aa, bb = a * a, b * b
    for i in range(TERMS):
        lower += (2 * SCALE * ap) // ((2 * i + 1) * bp)
        ap *= aa
        bp *= bb
    tail_num = 2 * SCALE * ap * bb
    tail_den = (2 * TERMS + 1) * bp * (bb - aa)
    tail_upper = (tail_num + tail_den - 1) // tail_den
    return lower, lower + TERMS + tail_upper


class LogOracle:
    def __init__(self, path: Path):
        self.path = path
        self.raw = path.open("xb")
        self.writer = gzip.GzipFile(fileobj=self.raw, mode="wb", mtime=0)
        self.cache: dict[int | tuple[int, int], tuple[int, int]] = {}
        self.primitive_count = 0
        self.uncompressed_digest = hashlib.sha256()
        self.log2 = _atanh_series(1, 3)

    def scaled(self, x: Fraction | int) -> tuple[int, int]:
        if isinstance(x, int):
            n, d, key = x, 1, x
        else:
            n, d = x.numerator, x.denominator
            key = n if d == 1 else (n, d)
        assert n > 0 and d > 0
        if key in self.cache:
            return self.cache[key]
        exponent = n.bit_length() - d.bit_length()
        if exponent >= 0:
            numerator, denominator = n, d << exponent
        else:
            numerator, denominator = n << -exponent, d
        if numerator < denominator:
            exponent -= 1
            numerator <<= 1
        if numerator >= 2 * denominator:
            exponent += 1
            denominator <<= 1
        assert denominator <= numerator < 2 * denominator
        lo, hi = _atanh_series(numerator - denominator, numerator + denominator)
        if exponent >= 0:
            lo += exponent * self.log2[0]
            hi += exponent * self.log2[1]
        else:
            lo += exponent * self.log2[1]
            hi += exponent * self.log2[0]
        assert lo <= hi
        self.cache[key] = (lo, hi)
        encoded = (json.dumps([n, d, exponent, lo, hi], separators=(",", ":")) + "\n").encode("ascii")
        self.writer.write(encoded)
        self.uncompressed_digest.update(encoded)
        self.primitive_count += 1
        return lo, hi

    def log(self, x: Fraction | int) -> Iv:
        lo, hi = self.scaled(x)
        return Fraction(lo, SCALE), Fraction(hi, SCALE)

    def vector(self, vector: dict[int, Fraction]) -> Iv:
        lo = hi = 0
        for key, coefficient in vector.items():
            pair = self.scaled(key)
            if coefficient >= 0:
                lower_arg, upper_arg = pair
            else:
                upper_arg, lower_arg = pair
            lower_num = coefficient.numerator * lower_arg
            upper_num = coefficient.numerator * upper_arg
            lo += lower_num // coefficient.denominator
            hi += -((-upper_num) // coefficient.denominator)
        return Fraction(lo, SCALE), Fraction(hi, SCALE)

    def close(self) -> dict:
        self.writer.close()
        self.raw.close()
        digest = hashlib.sha256()
        with self.path.open("rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(block)
        return {"path": str(self.path), "bytes": self.path.stat().st_size,
                "sha256": digest.hexdigest(),
                "uncompressed_sha256": self.uncompressed_digest.hexdigest(),
                "primitive_count": self.primitive_count,
                "record_columns": ["numerator", "denominator", "binary_exponent", "lo_scaled", "hi_scaled"],
                "bits": BITS, "terms": TERMS,
                "directed_integer_term_rounding": True,
                "positive_geometric_tail_upper_bound": True,
                "float_operations": 0}


def monotone_integral(oracle: LogOracle, t: int, qlo: int, qhi: int, pieces: int = 128) -> tuple[Iv, dict]:
    if qlo > qhi:
        return (Fraction(0), Fraction(0)), {"empty": True, "qlo": qlo, "qhi": qhi, "pieces": 0}
    from arithmetic import N
    left, right = Fraction(qlo - 1), Fraction(qhi)
    assert left > 1 and N - t * right > 0
    step = (right - left) / pieces
    bounds = []
    for i in range(pieces + 1):
        y = left + step * i
        numerator = oracle.log(N - t * y)
        denominator = oracle.log(y)
        assert numerator[0] > 0 and denominator[0] > 0
        bounds.append((numerator[0] / denominator[1], numerator[1] / denominator[0]))
    lower = step * sum((value[0] for value in bounds[1:]), Fraction(0))
    upper = step * sum((value[1] for value in bounds[:-1]), Fraction(0))
    assert lower <= upper
    return (lower, upper), {"empty": False, "qlo": qlo, "qhi": qhi,
                            "left_endpoint": fraction_text(left), "right_endpoint": fraction_text(right),
                            "pieces": pieces, "mesh_step": fraction_text(step),
                            "method": "decreasing positive log(N-t*y)/log(y), directed lower/right and upper/left sums"}
