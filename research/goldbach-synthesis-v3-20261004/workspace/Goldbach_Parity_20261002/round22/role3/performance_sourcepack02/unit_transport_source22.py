"""Future thermal H1 transport, SOURCE ONLY; no bank invocation is authorized.

This file is outside the frozen revision01 component bindings. A future launcher
must bind and review the readonly dyadic_r01 source bytes before making that
module available. No original component result or partial value is an input.

Readonly dependency proposed, not invoked here:
dyadic_r01.py SHA290d0e708bf30f7cd418a1dc006adcc8c89e9dd1893687ba5d832180f27c6a17.
This transport does not establish Mellin, Euler--Maclaurin, or H1 identities.
"""
from fractions import Fraction as F
from dyadic_r01 import Box, CBox, Point, EPS, SCALE, ceil, exact, pow2
from dyadic_r01 import exp_box, sin_cos_box, log_box, point_product


def radius_grid(candidate):
    candidate = exact(candidate)
    if candidate < 0:
        raise ArithmeticError("negative transport radius")
    outward = F(ceil(candidate * SCALE), SCALE)
    increment = outward - candidate
    if not 0 <= increment <= EPS:
        raise ArithmeticError("radius grid enclosure failed")
    # Store a grid upper bound for the diagnostic too. The exact increment can
    # have an enormous denominator and must never be accumulated for JSON.
    increment_upper = F(ceil(increment * SCALE), SCALE)
    if not 0 <= increment_upper <= EPS:
        raise ArithmeticError("diagnostic grid enclosure failed")
    return outward, increment_upper


def unit_phase(phase):
    sine, cosine = sin_cos_box(phase)
    return CBox(cosine, sine)


class UnitBoundTransport:
    """Center/radius powers of analytically specified unit or contractive steps.

    If the true seed and step have modulus at most one and e_q encloses the step
    error, then e_{j+1} <= (1+e_q)e_j + e_q + e_product. For at most L steps,
    L e_q <= 1/2 implies (1+e_q)^L <= 2: bound the binomial coefficients by L^k
    and then by the infinite geometric sum. Each radius rounding adds <= EPS.
    Thus every actual radius is bounded by 2 e_0 + 2 L(e_q + 2 EPS).

    Only the two constructors below supply seeds. They specify the true objects
    explicitly; an arbitrary supplied enclosure cannot assert a unit modulus.
    """
    __slots__ = ("point", "radius", "step", "step_radius", "count", "index",
                 "closed", "product_round_upper", "radius_round_upper",
                 "kind", "parameter_label")

    def __init__(self, seed, step, count, kind, parameter_label, _internal=False):
        if not _internal or count not in (800, 999999):
            raise ValueError("fixed future catalogue constructor required")
        self.point, self.radius = Point.from_box(seed)
        self.step, self.step_radius = Point.from_box(step)
        if self.radius > pow2(-200) or self.step_radius > pow2(-200):
            raise ArithmeticError("actual primitive seed/step radius too wide")
        if count * self.step_radius > F(1, 2):
            raise ArithmeticError("finite geometric envelope premise failed")
        self.count, self.index = count, 0
        self.closed = 2 * self.radius + 2 * count * (self.step_radius + 2 * EPS)
        self.product_round_upper = self.radius_round_upper = F(0)
        self.kind, self.parameter_label = kind, parameter_label

    def box(self):
        return self.point.box().widen(self.radius)

    def advance(self):
        if self.index + 1 >= self.count:
            raise ValueError("transport beyond complete fixed catalogue")
        self.point, product_round = point_product(self.point, self.step)
        if not 0 <= product_round <= EPS:
            raise ArithmeticError("actual point-product round bound failed")
        candidate = (1 + self.step_radius) * self.radius + self.step_radius + product_round
        self.radius, radius_round_upper = radius_grid(candidate)
        self.product_round_upper += product_round
        self.radius_round_upper += radius_round_upper
        self.index += 1
        if self.radius > self.closed:
            raise ArithmeticError("actual transport exceeds closed envelope")
        if self.radius.denominator.bit_length() > 513:
            raise ArithmeticError("radius left the fixed dyadic grid")
        return self.box()

    def diagnostics(self):
        return {
            "kind": self.kind,
            "parameter": self.parameter_label,
            "represented_values": self.count,
            "actual_advances": self.index,
            "radius": self.radius,
            "closed_radius": self.closed,
            "product_round_upper": self.product_round_upper,
            "radius_round_upper": self.radius_round_upper,
            "old_result_used": False,
        }


def em_unit_sequence(integer_label):
    """800 exact phases exp(i log(n)(1/16+j/8)), j=0..799.

    The canonical real logarithm is newly evaluated here. Modulus one follows
    from that real logarithm, rather than a numerical norm test.
    """
    if type(integer_label) is not int or not 2 <= integer_label <= 128:
        raise ValueError("fixed Euler--Maclaurin integer catalogue required")
    log_integer_box = log_box(Box.rational(integer_label))
    seed = unit_phase(log_integer_box.scale(F(1, 16)))
    step = unit_phase(log_integer_box.scale(F(1, 8)))
    return UnitBoundTransport(seed, step, 800, "EM_UNIT_PHASE",
                              str(integer_label), _internal=True)


def primal_heat_sequence():
    """999999 true values exp(-n/10000), n=2..1000000, no sieve input."""
    seed_real = exp_box(Box.rational(F(-2, 10000)))
    step_real = exp_box(Box.rational(F(-1, 10000)))
    zero = Box.rational(0)
    return UnitBoundTransport(CBox(seed_real, zero), CBox(step_real, zero),
                              999999, "PRIMAL_HEAT_EXP", "Y=10000", _internal=True)
