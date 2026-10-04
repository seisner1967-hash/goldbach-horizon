"""Global H1 fixed catalogue, SOURCE ONLY; never imported/executed in preparation.

Replaces ONLY the unused EM constructor of the older SOURCE transport. The
primal arithmetic source remains readonly. No old result is an input.
True points: a+3/16*omega_j+i*(-799/8+k/4), k=0..799, j=0..127.
The sampled function is evaluated at each dyadic midpoint; the caller pays
8*W*rho for the exact circle-position error, independently of power transport.
"""
from fractions import Fraction as F
from dyadic_r01 import (Box, CBox, Point, EPS, SCALE,
                       exp_complex, COUNTERS as DYADIC_COUNTERS)
from analytic_r01 import logarithm_integer, new_power

_EM_STEPS = {}
_Y_STEP = None


class CatalogueTrack:
    """Only constructors below attach actual analytic seed/step meanings.

    True seed norm <=U; true step norm=1. With step error e_q and initial
    error e_0, e_next <=(1+e_q)e+U*e_q+e_product+e_grid. For L=800,
    L*e_q<=1/2 implies (1+e_q)^L<=2 by the finite binomial/geometric bound.
    Hence every radius <=2e_0+1600*(U*e_q+3*EPS). Product error is checked
    <=2*EPS and the separate outward grid addition <=EPS; none is discarded.
    """
    __slots__ = ("point", "radius_grid", "step", "step_radius_grid", "U", "index",
                 "closed_grid", "label", "product_error_numerator", "radius_round_grid")

    def __init__(self, seed, step, upper, label, internal=False):
        if internal is not True or type(upper) is not int or upper not in (128, 100000000):
            raise ValueError("fixed analytic constructor required")
        self.point = Point((seed.real.lo + seed.real.hi) // 2,
                           (seed.imag.lo + seed.imag.hi) // 2)
        self.radius_grid = (max(abs(self.point.real - seed.real.lo), abs(self.point.real - seed.real.hi))
                            + max(abs(self.point.imag - seed.imag.lo), abs(self.point.imag - seed.imag.hi)))
        self.step = Point((step.real.lo + step.real.hi) // 2,
                          (step.imag.lo + step.imag.hi) // 2)
        self.step_radius_grid = (max(abs(self.step.real - step.real.lo), abs(self.step.real - step.real.hi))
                                 + max(abs(self.step.imag - step.imag.lo), abs(self.step.imag - step.imag.hi)))
        seed_guard_grid = SCALE >> 200
        if self.radius_grid > seed_guard_grid or self.step_radius_grid > seed_guard_grid:
            raise ArithmeticError("actual seed/step radius too wide")
        if 1600 * self.step_radius_grid > SCALE:
            raise ArithmeticError("finite transport geometric premise failed")
        self.U, self.index, self.label = upper, 0, label
        self.closed_grid = 2 * self.radius_grid + 1600 * (upper * self.step_radius_grid + 3)
        self.product_error_numerator = self.radius_round_grid = 0

    @property
    def radius(self):
        return F(self.radius_grid, SCALE)

    @property
    def step_radius(self):
        return F(self.step_radius_grid, SCALE)

    @property
    def closed(self):
        return F(self.closed_grid, SCALE)

    @property
    def product_error(self):
        return F(self.product_error_numerator, SCALE * SCALE)

    @property
    def radius_round_upper(self):
        return F(self.radius_round_grid, SCALE)

    def box(self):
        return CBox(Box(self.point.real - self.radius_grid, self.point.real + self.radius_grid),
                    Box(self.point.imag - self.radius_grid, self.point.imag + self.radius_grid))

    def advance(self):
        if self.index >= 799:
            raise ValueError("transport beyond fixed800 catalogue")
        raw_real = self.point.real * self.step.real - self.point.imag * self.step.imag
        raw_imag = self.point.real * self.step.imag + self.point.imag * self.step.real
        point = Point((raw_real + SCALE // 2) // SCALE,
                      (raw_imag + SCALE // 2) // SCALE)
        product_numerator = (abs(raw_real - point.real * SCALE)
                             + abs(raw_imag - point.imag * SCALE))
        if not 0 <= product_numerator <= 2 * SCALE:
            raise ArithmeticError("complex product error certificate failed")
        DYADIC_COUNTERS["point_product"] += 1
        candidate_numerator = ((SCALE + self.step_radius_grid) * self.radius_grid
                               + self.U * self.step_radius_grid * SCALE + product_numerator)
        radius_grid = -((-candidate_numerator) // SCALE)
        radius_round_numerator = radius_grid * SCALE - candidate_numerator
        if not 0 <= radius_round_numerator <= SCALE or radius_grid > self.closed_grid:
            raise ArithmeticError("outward radius/closed envelope failed")
        self.point, self.radius_grid = point, radius_grid
        self.product_error_numerator += product_numerator
        self.radius_round_grid += 1  # same EPS upper bound per step
        self.index += 1
        # All actual producer callers use advance for its state change only.
        # Avoid a discarded box allocation; the next sample calls box once.

    def diagnostics(self):
        return dict(label=self.label, advances=self.index, U=self.U,
                    radius=self.radius, closed=self.closed,
                    product_error=self.product_error,
                    radius_round_upper=self.radius_round_upper)


def start_point(side, circle_point):
    if side not in (F(3, 2), F(-1, 2)):
        raise ValueError("two fixed vertical sides required")
    circle = circle_point.box()
    if circle.real.abs_upper() > F(3, 16)+EPS or circle.imag.abs_upper() > F(3, 16)+EPS:
        raise ArithmeticError("fixed circle midpoint coordinate domain failed")
    s0 = circle+CBox.exact(side, F(-799, 8))
    if s0.real.lower() <= -1 or s0.real.upper() >= 2:
        raise ArithmeticError("actual rational midpoint outside seed norm domain")
    return s0


def em_power_track(integer_label, s0, side_label, circle_label):
    if type(integer_label) is not int or not 2 <= integer_label <= 128:
        raise ValueError("all127 bases required")
    logarithm = logarithm_integer(integer_label)
    seed = new_power(integer_label, s0)
    # exp(-i*h*log n), h=1/4. The canonical logarithm is real, hence norm=1.
    if integer_label not in _EM_STEPS:
        _EM_STEPS[integer_label] = exp_complex(CBox(logarithm.scale(0), logarithm.scale(F(-1, 4))))
    step = _EM_STEPS[integer_label]
    # -1<Re(s0)<2 implies |n^-s0|<=n<=128 for every transported midpoint.
    return CatalogueTrack(seed, step, 128,
                          f"EM:{side_label}:{circle_label}:{integer_label}", True)


def thermal_y_track(s0, side_label, circle_label):
    global _Y_STEP
    ly = logarithm_integer(10000)
    seed = exp_complex(CBox(s0.real*ly, s0.imag*ly))
    if _Y_STEP is None:
        _Y_STEP = exp_complex(CBox(ly.scale(0), ly.scale(F(1, 4))))
    step = _Y_STEP
    # Re(s0)<2 and Y=10000>=1 imply |Y^s0|<=Y^2.
    return CatalogueTrack(seed, step, 100000000,
                          f"Y_POWER:{side_label}:{circle_label}", True)
