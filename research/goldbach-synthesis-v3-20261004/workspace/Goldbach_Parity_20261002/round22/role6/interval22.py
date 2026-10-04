"""Fresh dyadic outward arithmetic for EPSTEIN_UNFOLDING_AUX only.

Source preparation; no old arithmetic library, output, or execution is reused.
Endpoints are integers times 2**(-96).  No floating-point value is used.
"""
from fractions import Fraction
from math import isqrt

BITS = 96
SCALE = 1 << BITS
_sqrt_observer = None
_sqrt_certificate_count = 0


def set_sqrt_observer(observer):
    global _sqrt_observer
    _sqrt_observer = observer


def sqrt_certificate_count():
    return _sqrt_certificate_count


def _floor(x):
    return x.numerator // x.denominator


def _ceil(x):
    return -((-x.numerator) // x.denominator)


class Box:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        if type(lo) is not int or type(hi) is not int or lo > hi:
            raise ValueError("ordered integer endpoints required")
        self.lo, self.hi = lo, hi

    @classmethod
    def rational(cls, x):
        if type(x) is int:
            x = Fraction(x)
        if not isinstance(x, Fraction):
            raise TypeError("exact rational input required")
        return cls(_floor(x * SCALE), _ceil(x * SCALE))

    def lower(self):
        return Fraction(self.lo, SCALE)

    def upper(self):
        return Fraction(self.hi, SCALE)

    def __add__(self, other):
        return Box(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Box(self.lo - other.hi, self.hi - other.lo)

    def __mul__(self, other):
        products = (self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi)
        return Box(min(products) // SCALE,
                   -((-max(products)) // SCALE))

    def __truediv__(self, other):
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("denominator enclosure contains zero")
        ratios = tuple(Fraction(a * SCALE, b)
                       for a in (self.lo, self.hi)
                       for b in (other.lo, other.hi))
        return Box(_floor(min(ratios)), _ceil(max(ratios)))

    def sqrt(self):
        global _sqrt_certificate_count
        if self.lo < 0:
            raise ValueError("nonnegative radicand enclosure required")
        lower_root = isqrt(self.lo * SCALE)
        upper_root = isqrt(self.hi * SCALE)
        if upper_root * upper_root != self.hi * SCALE:
            upper_root += 1
        if not (0 <= lower_root <= upper_root and
                lower_root * lower_root <= self.lo * SCALE and
                self.hi * SCALE <= upper_root * upper_root):
            raise ArithmeticError("integer square enclosure certificate failed")
        _sqrt_certificate_count += 1
        if _sqrt_observer is not None:
            _sqrt_observer({"input_lo_integer": str(self.lo),
                            "input_hi_integer": str(self.hi),
                            "root_lo_integer": str(lower_root),
                            "root_hi_integer": str(upper_root),
                            "denominator": str(SCALE),
                            "integer_square_inequalities_checked": True})
        return Box(lower_root, upper_root)

    def widen_upper(self, nonnegative):
        if nonnegative.lo < 0:
            raise ValueError("nonnegative remainder required")
        return Box(self.lo, self.hi + nonnegative.hi)

    def width(self):
        return Fraction(self.hi - self.lo, SCALE)

    def intersects(self, other):
        return max(self.lo, other.lo) <= min(self.hi, other.hi)

    def max_distance(self, other):
        return Fraction(max(abs(self.lo - other.hi),
                            abs(self.hi - other.lo)), SCALE)

    def as_json(self):
        return {"lo_integer": str(self.lo), "hi_integer": str(self.hi),
                "denominator": str(SCALE)}
