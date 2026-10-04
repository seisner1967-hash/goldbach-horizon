"""Global H1 fixed catalogue, SOURCE ONLY; never imported/executed in preparation.

Replaces ONLY the unused EM constructor of the older SOURCE transport. The
primal arithmetic source remains readonly. No old result is an input.
True points: a+3/16*omega_j+i*(-799/8+k/4), k=0..799, j=0..127.
The sampled function is evaluated at each dyadic midpoint; the caller pays
8*W*rho for the exact circle-position error, independently of power transport.
"""
from fractions import Fraction as F
from dyadic_r01 import (CBox, Point, EPS, SCALE, ceil, pow2,
                       exp_complex, point_product)
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
    __slots__ = ("point", "radius", "step", "step_radius", "U", "index",
                 "closed", "label", "product_error", "radius_round_upper")

    def __init__(self, seed, step, upper, label, internal=False):
        if not internal or upper not in (128, 100000000):
            raise ValueError("fixed analytic constructor required")
        self.point, self.radius = Point.from_box(seed)
        self.step, self.step_radius = Point.from_box(step)
        if self.radius > pow2(-200) or self.step_radius > pow2(-200):
            raise ArithmeticError("actual seed/step radius too wide")
        if 800*self.step_radius > F(1, 2):
            raise ArithmeticError("finite transport geometric premise failed")
        self.U, self.index, self.label = upper, 0, label
        self.closed = 2*self.radius+1600*(upper*self.step_radius+3*EPS)
        self.product_error = self.radius_round_upper = F(0)

    def box(self):
        return self.point.box().widen(self.radius)

    def advance(self):
        if self.index >= 799:
            raise ValueError("transport beyond fixed800 catalogue")
        point, product_error = point_product(self.point, self.step)
        if not 0 <= product_error <= 2*EPS:
            raise ArithmeticError("complex product error certificate failed")
        candidate = (1+self.step_radius)*self.radius+self.U*self.step_radius+product_error
        radius = F(ceil(candidate*SCALE), SCALE)
        if not 0 <= radius-candidate <= EPS or radius > self.closed:
            raise ArithmeticError("outward radius/closed envelope failed")
        self.point, self.radius = point, radius
        self.product_error += product_error
        self.radius_round_upper += EPS  # fixed grid upper bound, not huge denominator
        self.index += 1
        return self.box()

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
