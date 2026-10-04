"""New 768-bit outward profile; SOURCE ONLY until the Gamma bank gate.

Basic integer-endpoint rules adapted from READONLY interval22.py SHA
6e29ec2c7fb5d8e1eba796f3d863fb4c95db5b2bb5cf9671a9fb80d6469df588.
No import, output, certificate or PASS from G0 is reused.
"""
from fractions import Fraction
from math import isqrt

BITS = 768
SCALE = 1 << BITS
EPSILON = Fraction(1, SCALE)
SQRT_OBSERVER = None
COUNTERS = {"sqrt": 0, "exp": 0, "sin_cos": 0, "pi": 0}


def floor(q):
    return q.numerator // q.denominator


def ceil(q):
    return -((-q.numerator) // q.denominator)


class Box:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        if type(lo) is not int or type(hi) is not int or lo > hi:
            raise ValueError("ordered integer endpoints required")
        self.lo, self.hi = lo, hi

    @classmethod
    def rational(cls, q):
        if type(q) is int:
            q = Fraction(q)
        if not isinstance(q, Fraction):
            raise TypeError("exact rational input required")
        return cls(floor(q * SCALE), ceil(q * SCALE))

    def lower(self):
        return Fraction(self.lo, SCALE)

    def upper(self):
        return Fraction(self.hi, SCALE)

    def width(self):
        return Fraction(self.hi - self.lo, SCALE)

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __add__(self, other):
        return Box(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        p = (self.lo * other.lo, self.lo * other.hi,
             self.hi * other.lo, self.hi * other.hi)
        return Box(min(p) // SCALE, -((-max(p)) // SCALE))

    def __truediv__(self, other):
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("denominator enclosure contains zero")
        q = [Fraction(a * SCALE, b) for a in (self.lo, self.hi)
             for b in (other.lo, other.hi)]
        return Box(floor(min(q)), ceil(max(q)))

    def scale(self, q):
        """Exact rational multiplication BEFORE quantization of a small weight."""
        if type(q) is int:
            q = Fraction(q)
        if not isinstance(q, Fraction):
            raise TypeError("exact rational scale required")
        p = (q * self.lo, q * self.hi)
        return Box(floor(min(p)), ceil(max(p)))

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2)
        high = max(self.lo ** 2, self.hi ** 2)
        return Box(low // SCALE, -((-high) // SCALE))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError("nonnegative square-root input required")
        low = isqrt(self.lo * SCALE)
        high = isqrt(self.hi * SCALE)
        if high ** 2 != self.hi * SCALE:
            high += 1
        if not (low ** 2 <= self.lo * SCALE and self.hi * SCALE <= high ** 2):
            raise ArithmeticError("integer square certificate failed")
        COUNTERS["sqrt"] += 1
        if SQRT_OBSERVER is not None:
            SQRT_OBSERVER({"input": self.as_json(), "root_lo_integer": str(low),
                           "root_hi_integer": str(high),
                           "integer_square_inequalities_checked": True})
        return Box(low, high)

    def widen(self, radius):
        if radius < 0:
            raise ValueError("nonnegative exact radius required")
        step = ceil(radius * SCALE)
        return Box(self.lo - step, self.hi + step)

    def intersects(self, other):
        return max(self.lo, other.lo) <= min(self.hi, other.hi)

    def max_distance(self, other):
        return Fraction(max(abs(self.lo - other.hi), abs(self.hi - other.lo)), SCALE)

    def as_json(self):
        return {"lo_integer": str(self.lo), "hi_integer": str(self.hi),
                "denominator": str(SCALE)}


class ComplexBox:
    __slots__ = ("real", "imag")

    def __init__(self, real, imag):
        self.real, self.imag = real, imag

    @classmethod
    def exact(cls, real, imag=0):
        return cls(Box.rational(real), Box.rational(imag))

    def __add__(self, other):
        return ComplexBox(self.real + other.real, self.imag + other.imag)

    def __mul__(self, other):
        return ComplexBox(self.real * other.real - self.imag * other.imag,
                          self.real * other.imag + self.imag * other.real)

    def widen(self, radius):
        return ComplexBox(self.real.widen(radius), self.imag.widen(radius))

    def norm(self):
        return (self.real.square() + self.imag.square()).sqrt()

    def as_json(self):
        return {"real": self.real.as_json(), "imag": self.imag.as_json()}


def primitive_width_guard(result, original):
    bound = (1 << 48) * (original.width() + EPSILON) + Fraction(1, 1 << 300)
    if result.width() > bound:
        raise ArithmeticError("closed primitive width budget exceeded")
    return result


def exp_box(argument):
    """Taylor128 after dyadic reduction to [-1/8,1/8], then squaring."""
    if argument.lower() < -1024 or argument.upper() > 16:
        raise ValueError("exp domain outside frozen [-1024,16]")
    COUNTERS["exp"] += 1
    k = 0
    maximum = max(abs(argument.lower()), abs(argument.upper()))
    # One extra reduction leaves room for outward grid rounding.
    while maximum > Fraction(1, 16):
        maximum /= 2
        k += 1
    base = argument.scale(Fraction(1, 1 << k))
    if base.lower() < Fraction(-1, 8) or base.upper() > Fraction(1, 8):
        raise ArithmeticError("Taylor exp base domain certificate failed")
    one = Box.rational(1)
    value = one
    for j in range(128, 0, -1):
        value = one + (value * base).scale(Fraction(1, j))
    value = value.widen(Fraction(2, 8 ** 129))
    # exp is positive; intersection is a proved range restriction, never a test fit.
    value = Box(max(0, value.lo), value.hi)
    for _ in range(k):
        value = value.square()
    return primitive_width_guard(value, argument)


def pi_box():
    """Machin identity, two exact rational alternating sums with next-term tails."""
    COUNTERS["pi"] += 1
    def atan_inverse(q):
        total = Fraction(0)
        for j in range(256):
            total += Fraction((-1) ** j, (2 * j + 1) * q ** (2 * j + 1))
        return Box.rational(total).widen(Fraction(1, 513 * q ** 513))
    result = atan_inverse(5).scale(16) - atan_inverse(239).scale(4)
    if result.lower() <= 3 or result.upper() >= 4 or result.width() > 128 * EPSILON:
        raise ArithmeticError("Machin range/width certificate failed")
    return result


def sin_cos_box(argument, pi):
    """Exact integer-period reduction; paired Taylor polynomials, explicit tails."""
    if argument.lower() < -4096 or argument.upper() > 4096:
        raise ValueError("sin/cos domain outside frozen [-4096,4096]")
    COUNTERS["sin_cos"] += 1
    midpoint = Fraction(argument.lo + argument.hi, 2 * SCALE)
    pi_midpoint = Fraction(pi.lo + pi.hi, 2 * SCALE)
    turns = floor(midpoint / (2 * pi_midpoint) + Fraction(1, 2))
    reduced = argument - pi.scale(2 * turns)
    if reduced.lower() < -4 or reduced.upper() > 4:
        raise ArithmeticError("period-reduced interval exceeds [-4,4]")
    u = reduced.square()
    one = Box.rational(1)
    cosine = one
    sine = one
    for j in range(127, 0, -1):
        cosine = one - (cosine * u).scale(Fraction(1, (2 * j) * (2 * j - 1)))
        sine = one - (sine * u).scale(Fraction(1, (2 * j + 1) * (2 * j)))
    sine = sine * reduced
    # Both tails bounded by 2*4^257/256!, verified symbolically in paper.
    factorial = 1
    for j in range(1, 257):
        factorial *= j
    tail = Fraction(2 * 4 ** 257, factorial)
    sine, cosine = sine.widen(tail), cosine.widen(tail)
    # The true functions belong to [-1,1].
    sine = Box(max(-SCALE, sine.lo), min(SCALE, sine.hi))
    cosine = Box(max(-SCALE, cosine.lo), min(SCALE, cosine.hi))
    return primitive_width_guard(sine, argument), primitive_width_guard(cosine, argument)
