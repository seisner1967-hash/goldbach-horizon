"""Fresh 512-bit arithmetic for thermal15.3; SOURCE ONLY until a new gate.

Integer-endpoint ground rules are adapted from the READONLY source
dyadic_gamma22.py SHA01c1eb04ad4f0559b181b91c5fb300654d99ee8c16ed0b1d901e05a7604c64b6.
No old module, output, log, certificate, bank or PASS is imported.
The unit-modulus transport uses points and norm radii, not rotated rectangles.
"""
from fractions import Fraction as F
from math import isqrt

BITS = 512
SCALE = 1 << BITS
EPS = F(1, SCALE)
COUNTERS = {"exp": 0, "sin_cos": 0, "pi": 0, "log": 0,
            "atan": 0, "complex_log": 0, "sqrt": 0, "point_product": 0}
SQRT_OBSERVER = None
_PI = None
_LOG2 = None


def exact(q):
    if type(q) is int:
        return F(q)
    if isinstance(q, F):
        return q
    raise TypeError("integer or exact Fraction required; no float")


def floor(q):
    q = exact(q)
    return q.numerator // q.denominator


def ceil(q):
    q = exact(q)
    return -((-q.numerator) // q.denominator)


def pow2(k):
    if type(k) is not int:
        raise TypeError("integer exponent required")
    return F(1 << k) if k >= 0 else F(1, 1 << (-k))


def rational_json(q):
    q = exact(q)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}


class Box:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        if type(lo) is not int or type(hi) is not int or lo > hi:
            raise ValueError("ordered integer endpoints required")
        self.lo, self.hi = lo, hi

    @classmethod
    def rational(cls, q):
        q = exact(q)
        numerator = q.numerator * SCALE
        denominator = q.denominator
        return cls(numerator // denominator, -((-numerator) // denominator))

    def lower(self):
        return F(self.lo, SCALE)

    def upper(self):
        return F(self.hi, SCALE)

    def midpoint(self):
        return F(self.lo + self.hi, 2 * SCALE)

    def width(self):
        return F(self.hi - self.lo, SCALE)

    def abs_upper(self):
        return F(max(abs(self.lo), abs(self.hi)), SCALE)

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __add__(self, other):
        return Box(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        vals = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Box(min(vals) // SCALE, -((-max(vals)) // SCALE))

    def __truediv__(self, other):
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("denominator enclosure contains zero")
        pairs = [(a * SCALE, b) for a in (self.lo, self.hi)
                 for b in (other.lo, other.hi)]
        return Box(min(n // d for n, d in pairs),
                   max(-((-n) // d) for n, d in pairs))

    def scale(self, q):
        q = exact(q)
        vals = (q.numerator * self.lo, q.numerator * self.hi)
        denominator = q.denominator
        return Box(min(vals) // denominator, -((-max(vals)) // denominator))

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2)
        high = max(self.lo ** 2, self.hi ** 2)
        return Box(low // SCALE, -((-high) // SCALE))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError("nonnegative input required")
        low, high = isqrt(self.lo * SCALE), isqrt(self.hi * SCALE)
        if high ** 2 != self.hi * SCALE:
            high += 1
        if low ** 2 > self.lo * SCALE or high ** 2 < self.hi * SCALE:
            raise ArithmeticError("integer square certificate failed")
        COUNTERS["sqrt"] += 1
        if SQRT_OBSERVER is not None:
            SQRT_OBSERVER({"input": self.as_json(), "root_lo": str(low),
                           "root_hi": str(high), "inequalities_checked": True})
        return Box(low, high)

    def widen(self, radius):
        radius = exact(radius)
        if radius < 0:
            raise ValueError("negative radius")
        numerator = radius.numerator * SCALE
        step = -((-numerator) // radius.denominator)
        return Box(self.lo - step, self.hi + step)

    def intersects(self, other):
        return max(self.lo, other.lo) <= min(self.hi, other.hi)

    def max_distance(self, other):
        return F(max(abs(self.lo - other.hi), abs(self.hi - other.lo)), SCALE)

    def as_json(self):
        return {"lo_integer": str(self.lo), "hi_integer": str(self.hi),
                "denominator": str(SCALE)}


class CBox:
    __slots__ = ("real", "imag")

    def __init__(self, real, imag):
        self.real, self.imag = real, imag

    @classmethod
    def exact(cls, real, imag=0):
        return cls(Box.rational(real), Box.rational(imag))

    def __neg__(self):
        return CBox(-self.real, -self.imag)

    def __add__(self, other):
        return CBox(self.real + other.real, self.imag + other.imag)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return CBox(self.real * other.real - self.imag * other.imag,
                    self.real * other.imag + self.imag * other.real)

    def __truediv__(self, other):
        denominator = other.real.square() + other.imag.square()
        if denominator.lo <= 0:
            raise ZeroDivisionError("complex denominator has no positive norm certificate")
        return CBox((self.real * other.real + self.imag * other.imag) / denominator,
                    (self.imag * other.real - self.real * other.imag) / denominator)

    def scale(self, q):
        return CBox(self.real.scale(q), self.imag.scale(q))

    def conjugate(self):
        return CBox(self.real, -self.imag)

    def abs_upper(self):
        return self.real.abs_upper() + self.imag.abs_upper()

    def norm_box(self):
        return (self.real.square() + self.imag.square()).sqrt()

    def widen(self, radius):
        return CBox(self.real.widen(radius), self.imag.widen(radius))

    def as_json(self):
        return {"real": self.real.as_json(), "imag": self.imag.as_json()}


class Point:
    __slots__ = ("real", "imag")

    def __init__(self, real, imag):
        if type(real) is not int or type(imag) is not int:
            raise TypeError("dyadic integer coordinates required")
        self.real, self.imag = real, imag

    @classmethod
    def from_box(cls, value):
        p = cls((value.real.lo + value.real.hi) // 2,
                (value.imag.lo + value.imag.hi) // 2)
        radius = F(max(abs(p.real - value.real.lo), abs(p.real - value.real.hi))
                   + max(abs(p.imag - value.imag.lo), abs(p.imag - value.imag.hi)), SCALE)
        return p, radius

    def box(self):
        return CBox(Box(self.real, self.real), Box(self.imag, self.imag))

    def abs_upper(self):
        return F(abs(self.real) + abs(self.imag), SCALE)

    def __add__(self, other):
        return Point(self.real + other.real, self.imag + other.imag)

    def __neg__(self):
        return Point(-self.real, -self.imag)


def point_product(a, b):
    """Rounded Gaussian-dyadic product with an exact norm error certificate."""
    raw_real = a.real * b.real - a.imag * b.imag
    raw_imag = a.real * b.imag + a.imag * b.real
    p = Point((raw_real + SCALE // 2) // SCALE, (raw_imag + SCALE // 2) // SCALE)
    error = F(abs(raw_real - p.real * SCALE) + abs(raw_imag - p.imag * SCALE),
              SCALE * SCALE)
    if error > 2 * EPS:
        raise ArithmeticError("closed point-product rounding budget failed")
    COUNTERS["point_product"] += 1
    return p, error


class PowerTrack:
    """Transport of a true power with |q|=1, seed and step enclosures checked."""
    __slots__ = ("point", "radius", "step", "step_radius", "U", "index", "closed")

    def __init__(self, seed, step, U):
        self.point, self.radius = Point.from_box(seed)
        self.step, self.step_radius = Point.from_box(step)
        self.U, self.index = exact(U), 0
        if self.U < 0 or self.radius > pow2(-200) or self.step_radius > pow2(-200):
            raise ArithmeticError("fixed recurrence seed/step guard failed")
        self.closed = 2 * self.radius + 1600 * (self.U * self.step_radius + 2 * EPS)

    def box(self):
        return self.point.box().widen(self.radius)

    def advance(self):
        if self.index >= 799:
            raise ValueError("recurrence attempted outside fixed800catalogue")
        self.point, rounding = point_product(self.point, self.step)
        candidate = (1 + self.step_radius) * self.radius + self.U * self.step_radius + rounding
        self.radius = F(ceil(candidate * SCALE), SCALE)
        radius_round = self.radius - candidate
        if not 0 <= radius_round <= EPS or rounding + radius_round > 2 * EPS:
            raise ArithmeticError("actual product/radius round certificate failed")
        self.index += 1
        if self.radius > self.closed:
            raise ArithmeticError("finite geometric transport certificate failed")


def width_guard(result, argument):
    closed = (1 << 48) * (argument.width() + EPS) + pow2(-300)
    if result.width() > closed:
        raise ArithmeticError("constructed primitive width exceeds efficiency guard")
    return result


def exp_box(argument):
    if argument.lower() < -1024 or argument.upper() > 16:
        raise ValueError("fresh exp domain outside[-1024,16]")
    COUNTERS["exp"] += 1
    k, maximum = 0, argument.abs_upper()
    while maximum > F(1, 16):
        maximum /= 2
        k += 1
    base = argument.scale(pow2(-k))
    if base.lower() < F(-1, 8) or base.upper() > F(1, 8):
        raise ArithmeticError("exp reduction domain not certified")
    one, value = Box.rational(1), Box.rational(1)
    for j in range(128, 0, -1):
        value = one + (value * base).scale(F(1, j))
    value = value.widen(F(2, 8 ** 129))
    value = Box(max(0, value.lo), value.hi)
    for _ in range(k):
        value = value.square()
    return width_guard(value, argument)


def pi_box():
    global _PI
    if _PI is not None:
        return _PI
    COUNTERS["pi"] += 1
    def atan_inverse(q):
        value = sum((F((-1) ** j, (2 * j + 1) * q ** (2 * j + 1))
                     for j in range(256)), F(0))
        return Box.rational(value).widen(F(1, 513 * q ** 513))
    value = atan_inverse(5).scale(16) - atan_inverse(239).scale(4)
    if value.lower() <= 3 or value.upper() >= 4 or value.width() > 128 * EPS:
        raise ArithmeticError("new Machin certificate failed")
    _PI = value
    return value


def sin_cos_box(argument):
    if argument.lower() < -4096 or argument.upper() > 4096:
        raise ValueError("fresh trig domain outside[-4096,4096]")
    COUNTERS["sin_cos"] += 1
    pi = pi_box()
    turns = floor(argument.midpoint() / (2 * pi.midpoint()) + F(1, 2))
    reduced = argument - pi.scale(2 * turns)
    if reduced.lower() < -4 or reduced.upper() > 4:
        raise ArithmeticError("integer-period enclosure outside[-4,4]")
    one, u = Box.rational(1), reduced.square()
    sine, cosine = one, one
    for j in range(127, 0, -1):
        cosine = one - (cosine * u).scale(F(1, (2 * j) * (2 * j - 1)))
        sine = one - (sine * u).scale(F(1, (2 * j + 1) * (2 * j)))
    sine = sine * reduced
    fact = 1
    for j in range(1, 257):
        fact *= j
    tail = F(2 * 4 ** 257, fact)
    sine, cosine = sine.widen(tail), cosine.widen(tail)
    sine = Box(max(-SCALE, sine.lo), min(SCALE, sine.hi))
    cosine = Box(max(-SCALE, cosine.lo), min(SCALE, cosine.hi))
    # For the full generic domain, period uncertainty is bounded with2^18,
    # not the2^16 efficiency clause from an older paper. Complete pi intervals
    # are used here, independently of either coarse width estimate.
    return width_guard(sine, argument), width_guard(cosine, argument)


def exp_complex(argument):
    amplitude = exp_box(argument.real)
    sine, cosine = sin_cos_box(argument.imag)
    return CBox(amplitude * cosine, amplitude * sine)


def _log_unit(argument):
    if argument.lower() < F(1, 2) or argument.upper() > 2:
        raise ValueError("log unit outside[1/2,2]")
    one = Box.rational(1)
    z = (argument - one) / (argument + one)
    # The true transformed argument lies in[-1/3,1/3] from the input
    # endpoints. Outward dyadic division may protrude by one EPS at1/3.
    # The Taylor polynomial is evaluated on the complete enclosure; only
    # its analytic remainder uses the true-domain bound1/3.
    if z.abs_upper() > F(1, 3) + EPS:
        raise ArithmeticError("atanh log domain certificate failed")
    z2, series = z.square(), Box.rational(F(1, 511))
    for j in range(254, -1, -1):
        series = Box.rational(F(1, 2 * j + 1)) + z2 * series
    value = (z * series).scale(2)
    tail = F(2, 513 * 3 ** 513) / (1 - F(1, 9))
    return value.widen(tail)


def log2_box():
    global _LOG2
    if _LOG2 is None:
        _LOG2 = _log_unit(Box.rational(2))
    return _LOG2


def log_box(argument):
    if argument.lo <= 0:
        raise ValueError("log input lacks positive lower endpoint")
    COUNTERS["log"] += 1
    mid = argument.midpoint()
    k = mid.numerator.bit_length() - mid.denominator.bit_length()
    if mid < pow2(k):
        k -= 1
    reduced = argument.scale(pow2(-k))
    if reduced.upper() > 2:
        k += 1
        reduced = argument.scale(pow2(-k))
    if reduced.lower() < F(1, 2) or reduced.upper() > 2:
        raise ArithmeticError("full log enclosure not covered by reduction")
    return _log_unit(reduced) + log2_box().scale(k)


def _atan_series(argument):
    if argument.abs_upper() > F(5, 8):
        raise ValueError("atan Taylor domain outside[-5/8,5/8]")
    u = argument.square()
    value = Box.rational(F((-1) ** 511, 1023))
    for j in range(510, -1, -1):
        value = Box.rational(F((-1) ** j, 2 * j + 1)) + u * value
    # The uniform absolute geometric bound covers wide intervals as well.
    tail = F(2, 1025) * F(5, 8) ** 1025
    return (argument * value).widen(tail)


def atan_box(argument):
    if argument.abs_upper() > 2:
        raise ValueError("complex-log atan ratio outside[-2,2]")
    COUNTERS["atan"] += 1
    if argument.abs_upper() <= F(5, 8):
        return _atan_series(argument)
    if argument.lower() >= F(1, 2):
        one = Box.rational(1)
        transformed = (argument - one) / (argument + one)
        if transformed.abs_upper() > F(1, 3) + EPS:
            raise ArithmeticError("atan transformed domain not certified")
        return pi_box().scale(F(1, 4)) + _atan_series(transformed)
    if argument.upper() <= F(-1, 2):
        return -atan_box(-argument)
    raise ArithmeticError("atan enclosure straddles uncovered branches")


def log_complex(argument):
    if argument.real.lo <= 0:
        raise ValueError("principal complex Log requires Re>0")
    COUNTERS["complex_log"] += 1
    modulus_square = argument.real.square() + argument.imag.square()
    real = log_box(modulus_square).scale(F(1, 2))
    imag = atan_box(argument.imag / argument.real)
    return CBox(real, imag)
