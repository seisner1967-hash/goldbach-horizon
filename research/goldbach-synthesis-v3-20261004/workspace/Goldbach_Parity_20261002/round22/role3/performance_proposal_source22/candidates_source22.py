"""SOURCE ONLY proposal for a DISTINCT future numerical packet.

Never imported, parsed or evaluated here. No result of a closed bank is read.
The helpers below propose identical endpoint arithmetic, not an H1 theorem.
Any integration requires a new reviewed producer, checker, manifest and gate.
"""
from fractions import Fraction as F
from dyadic_r01 import (Box, CBox, floor, pow2, log2_box, log_box,
                       log_complex, exp_box, exp_complex, pi_box)
from analytic_r01 import COUNTERS, stirling_coefficients

_HALF_LOG_TWO_PI_ENDPOINTS = None
_F1_ENDPOINTS = None


def fresh_half_log_two_pi():
    """A fresh new-interpreter primitive enclosure, then integer-only cache.

    Return a new Box object: no caller can mutate the cached endpoints.
    The first construction is EXACTLY the old value-side expression.
    """
    global _HALF_LOG_TWO_PI_ENDPOINTS
    if _HALF_LOG_TWO_PI_ENDPOINTS is None:
        value = log_box(pi_box().scale(2)).scale(F(1, 2))
        _HALF_LOG_TWO_PI_ENDPOINTS = (value.lo, value.hi)
    return Box(*_HALF_LOG_TWO_PI_ENDPOINTS)


def stirling_log_value_only(z):
    """Same value operations and signed B64 remainder; derivative removed.

    This is the original first projection of the pair, not a new Gamma
    approximation. Its derivative projection remains available separately
    for the single Euler-constant construction and for actual psi consumers.
    """
    if z.real.lower() < F(1, 4) or z.real.upper() > 3 or z.imag.abs_upper() > 101:
        raise ValueError("Gamma source domain outside[1/4,3] x[-101,101]")
    w = z + CBox.exact(64)
    logw = log_complex(w)
    inverse = CBox.exact(1) / w
    inverse_square = inverse * inverse
    power = inverse
    value = (w - CBox.exact(F(1, 2))) * logw - w + CBox(
        fresh_half_log_two_pi(), Box.rational(0))
    for coefficient, _ in stirling_coefficients():
        value = value + power.scale(coefficient)
        power = power * inverse_square
    return value.widen(F(4, 63 * 6 ** 64))


def gamma_value_only(z):
    """Original reduction, exp, recurrence denominator and quotient guards."""
    COUNTERS["gamma"] += 1
    logarithm = stirling_log_value_only(z)
    k = floor(logarithm.real.midpoint() / log2_box().midpoint())
    reduced = CBox(logarithm.real - log2_box().scale(k), logarithm.imag)
    if reduced.real.lower() < -2 or reduced.real.upper() > 2:
        raise ArithmeticError("scaled Gamma exp domain not certified")
    numerator = exp_complex(reduced).scale(pow2(k))
    denominator = CBox.exact(1)
    for j in range(64):
        denominator = denominator * (z + CBox.exact(j))
    return numerator / denominator


def fresh_f1():
    """Exactly exp(-1/Y)/Y at the fixed Y=10000, constructed once."""
    global _F1_ENDPOINTS
    if _F1_ENDPOINTS is None:
        value = exp_box(Box.rational(F(-1, 10000))).scale(F(1, 10000))
        _F1_ENDPOINTS = (value.lo, value.hi)
    return Box(*_F1_ENDPOINTS)


def quotient_endpoint_integers(a_lo, a_hi, b_lo, b_hi, scale):
    """Exact replacement of old four-Fraction Box division endpoints.

    Python integer // is floor for either sign of a nonzero denominator.
    min(floor q_i)=floor(min q_i); max(ceil q_i)=ceil(max q_i).
    No approximation and no new numerical error is introduced.
    """
    if any(type(v) is not int for v in (a_lo, a_hi, b_lo, b_hi, scale)):
        raise TypeError("integer endpoints and scale required")
    if a_lo > a_hi or b_lo > b_hi or scale < 1:
        raise ValueError("ordered intervals and positive scale required")
    if b_lo <= 0 <= b_hi:
        raise ZeroDivisionError("denominator enclosure contains zero")
    pairs = [(a * scale, b) for a in (a_lo, a_hi) for b in (b_lo, b_hi)]
    return min(n // d for n, d in pairs), max(-((-n) // d) for n, d in pairs)


def rational_scale_endpoint_integers(lo, hi, numerator, denominator):
    """Same endpoints as Box.scale(F(numerator,denominator)), without gcd.

    The caller extracts a canonical Fraction denominator, which is positive.
    This preserves the existing real interval operation for either sign.
    """
    if any(type(v) is not int for v in (lo, hi, numerator, denominator)):
        raise TypeError("integer endpoints and rational components required")
    if lo > hi or denominator <= 0:
        raise ValueError("ordered interval and positive denominator required")
    values = (numerator * lo, numerator * hi)
    return min(values) // denominator, -((-max(values)) // denominator)


def transport_step_integer_kernel(ar, ai, qr, qi, radius, step_radius,
                                  upper, seed_radius, scale, index):
    """Exact algebraic translation of CatalogueTrack.advance.

    radius=R/scale, step_radius=E/scale, seed_radius=R0/scale.
    Inputs alone do not certify any power: future EM/Y constructors must
    still produce actual primitive seed/step boxes for the true functions.
    This helper proves only equality with the original discrete recurrence.
    """
    values = (ar, ai, qr, qi, radius, step_radius, upper, seed_radius, scale, index)
    if any(type(v) is not int for v in values):
        raise TypeError("integer transport representation required")
    if scale < 2 or scale % 2 or upper not in (128, 100000000):
        raise ValueError("fixed positive even grid and EM/Y upper bound required")
    if not 0 <= index < 799 or min(radius, step_radius, seed_radius) < 0:
        raise ValueError("fixed transport domain required")
    if 1600 * step_radius > scale:
        raise ArithmeticError("800*true step radius <=1/2 guard failed")
    raw_real = ar * qr - ai * qi
    raw_imag = ar * qi + ai * qr
    pr = (raw_real + scale // 2) // scale
    pi = (raw_imag + scale // 2) // scale
    product_numerator = abs(raw_real - pr * scale) + abs(raw_imag - pi * scale)
    if not 0 <= product_numerator <= 2 * scale:
        raise ArithmeticError("same point-product norm error guard failed")
    candidate_numerator = ((scale + step_radius) * radius
                           + upper * step_radius * scale + product_numerator)
    next_radius = -((-candidate_numerator) // scale)
    radius_round_numerator = next_radius * scale - candidate_numerator
    if not 0 <= radius_round_numerator <= scale:
        raise ArithmeticError("same separate outward grid error guard failed")
    closed_grid_radius = 2 * seed_radius + 1600 * (upper * step_radius + 3)
    if next_radius > closed_grid_radius:
        raise ArithmeticError("same closed continuous transport envelope failed")
    return dict(point_real=pr, point_imag=pi, radius_grid=next_radius,
                product_error_numerator=product_numerator,
                product_error_denominator=scale * scale,
                actual_radius_round_numerator=radius_round_numerator,
                actual_radius_round_denominator=scale * scale,
                closed_grid_radius=closed_grid_radius, index=index + 1)
