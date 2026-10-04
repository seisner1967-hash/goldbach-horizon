"""New analytic objects for15.3: SOURCE ONLY, no imports before a new gate.

All complex errors below are absolute norm bounds. Widening both coordinates
by such a bound is a conservative rectangle enclosure, never a point oracle.
There is no numerical import or dependency on any closed bank result.
"""
from fractions import Fraction as F
from math import comb, factorial
from dyadic_r01 import (Box, CBox, EPS, exact, floor, pow2, log_box,
                             log2_box, log_complex, exp_box, exp_complex, pi_box)

COUNTERS = {"em": 0, "gamma": 0, "psi": 0, "arch": 0, "direct_power": 0}
_BERNOULLI = None
_LOGS = {}
_EM_COEFFICIENTS = None
_STIRLING_COEFFICIENTS = None
_HALF_LOG_TWO_PI_ENDPOINTS = None
_F1_ENDPOINTS = None
PERFORMANCE_COUNTERS = {"half_log_two_pi_constructions": 0,
                        "f1_constructions": 0, "gamma_value_only": 0}


def half_log_two_pi_box():
    """Same primitive expression, newly certified once per fresh interpreter."""
    global _HALF_LOG_TWO_PI_ENDPOINTS
    if _HALF_LOG_TWO_PI_ENDPOINTS is None:
        value = log_box(pi_box().scale(2)).scale(F(1, 2))
        _HALF_LOG_TWO_PI_ENDPOINTS = (value.lo, value.hi)
        PERFORMANCE_COUNTERS["half_log_two_pi_constructions"] += 1
    return Box(*_HALF_LOG_TWO_PI_ENDPOINTS)


def f1_box(y=10000):
    """Exact f(1)=exp(-1/Y)/Y; only the fixed original Y is admissible."""
    global _F1_ENDPOINTS
    if type(y) is not int or y != 10000:
        raise ValueError("the performance packet has fixedY10000")
    if _F1_ENDPOINTS is None:
        value = exp_box(Box.rational(F(-1, y))).scale(F(1, y))
        _F1_ENDPOINTS = (value.lo, value.hi)
        PERFORMANCE_COUNTERS["f1_constructions"] += 1
    return Box(*_F1_ENDPOINTS)


def bernoulli_numbers():
    """Fresh rational recurrence, B1=-1/2, through128; no old table."""
    global _BERNOULLI
    if _BERNOULLI is None:
        values = [F(1)]
        for n in range(1, 129):
            total = sum((F(comb(n + 1, k)) * values[k]
                         for k in range(n)), F(0))
            values.append(-total / (n + 1))
        if values[1] != F(-1, 2) or values[2] != F(1, 6):
            raise ArithmeticError("Bernoulli initial recurrence certificate failed")
        if any(values[n] != 0 for n in range(3, 129, 2)):
            raise ArithmeticError("odd Bernoulli recurrence certificate failed")
        _BERNOULLI = tuple(values)
    return _BERNOULLI


def logarithm_integer(n):
    if type(n) is not int or n < 1:
        raise ValueError("positive exact integer log input required")
    if n not in _LOGS:
        _LOGS[n] = log_box(Box.rational(n))
    return _LOGS[n]


def em_coefficients():
    global _EM_COEFFICIENTS
    if _EM_COEFFICIENTS is None:
        b = bernoulli_numbers()
        _EM_COEFFICIENTS = tuple(b[2 * k] / factorial(2 * k) for k in range(1, 65))
    return _EM_COEFFICIENTS


def stirling_coefficients():
    global _STIRLING_COEFFICIENTS
    if _STIRLING_COEFFICIENTS is None:
        b = bernoulli_numbers()
        _STIRLING_COEFFICIENTS = tuple((b[2 * k] / ((2 * k) * (2 * k - 1)),
                                        b[2 * k] / (2 * k)) for k in range(1, 33))
    return _STIRLING_COEFFICIENTS


def new_power(n, s):
    """True exp(-s log n), independently constructed with new primitives."""
    COUNTERS["direct_power"] += 1
    return exp_complex(CBox(-s.real * logarithm_integer(n),
                            -s.imag * logarithm_integer(n)))


def em_zeta_and_derivative(s, powers=None):
    """M128/K64, paired signed remainder and Cauchy derivative remainder.

    powers, when used by the full thermal catalogue, must be enclosures of
    each true n^-s, created by the new PowerTrack recurrence. This interface
    never treats arbitrary data as a power certificate. The producer owns
    the dependency chain and records its seeds, steps and transport radii.
    Component tests use direct new_power and do not pass this argument.
    """
    if (s.real.lower() < F(-7, 8) or s.real.upper() > 2
            or s.imag.abs_upper() > F(401, 4)):
        raise ValueError("EM base domain outside[-7/8,2] x[-401/4,401/4]")
    one = CBox.exact(1)
    sm1 = s - one
    if sm1.real.lo <= 0 <= sm1.real.hi and sm1.imag.lo <= 0 <= sm1.imag.hi:
        raise ValueError("unregularized zeta evaluation meets its pole")
    COUNTERS["em"] += 1
    if powers is None:
        powers = {n: new_power(n, s) for n in range(2, 129)}
    elif set(powers) != set(range(2, 129)):
        raise ValueError("all127 powers2..128 required before any filtering")
    value, derivative = one, CBox.exact(0)
    for n in range(2, 128):
        value = value + powers[n]
        derivative = derivative - CBox(powers[n].real * logarithm_integer(n),
                                       powers[n].imag * logarithm_integer(n))
    bracket = one.scale(128) / sm1 + one.scale(F(1, 2))
    bracket_derivative = -(one.scale(128) / (sm1 * sm1))
    rising, rising_derivative = one, CBox.exact(0)
    coefficients = em_coefficients()
    for j in range(127):
        # Store(s)_length/128^length, rather than a huge Pochhammer followed
        # by cancellation. Its derivative recurrence has the explicit1/128.
        factor = (s + CBox.exact(j)).scale(F(1, 128))
        rising_derivative = rising_derivative * factor + rising.scale(F(1, 128))
        rising = rising * factor
        length = j + 1
        if length % 2 == 1:
            k = (length + 1) // 2
            coefficient = coefficients[k - 1]
            bracket = bracket + rising.scale(coefficient)
            bracket_derivative = bracket_derivative + rising_derivative.scale(coefficient)
    value = value + powers[128] * bracket
    log128 = logarithm_integer(128)
    derivative = derivative + powers[128] * (
        bracket_derivative - CBox(bracket.real * log128, bracket.imag * log128))
    return value.widen(pow2(-182)), derivative.widen(pow2(-178))


def a_log_derivative(s, powers=None):
    zeta, zeta_derivative = em_zeta_and_derivative(s, powers)
    # Both divisions certify their nonzero denominators from their boxes.
    return CBox.exact(1) / (s - CBox.exact(1)) + zeta_derivative / zeta


def _stirling_log_and_derivative(z):
    """Holomorphic logGamma on Re z>0, shifted64, order32.

    After including B64/(64*63*w^63), R is the negative periodic-B64
    integral. On this fixed domain its norm is <=4/(63*6^64).
    The derivative uses a1/16 Cauchy disc, hence16 times that remainder.
    The principal Log(w) is constructed directly in the right half-plane.
    """
    if z.real.lower() < F(1, 4) or z.real.upper() > 3 or z.imag.abs_upper() > 101:
        raise ValueError("Gamma source domain outside[1/4,3] x[-101,101]")
    w = z + CBox.exact(64)
    logw = log_complex(w)
    inverse = CBox.exact(1) / w
    inverse_square = inverse * inverse
    power = inverse
    half_log_two_pi = half_log_two_pi_box()
    value = (w - CBox.exact(F(1, 2))) * logw - w + CBox(half_log_two_pi, Box.rational(0))
    derivative = logw - inverse.scale(F(1, 2))
    for coefficient, derivative_coefficient in stirling_coefficients():
        value = value + power.scale(coefficient)
        derivative = derivative - (power * inverse).scale(derivative_coefficient)
        power = power * inverse_square
    remainder = F(4, 63 * 6 ** 64)
    return value.widen(remainder), derivative.widen(16 * remainder)


def _stirling_log_value_only(z):
    """Original first projection, without the derivative computation.

    All value operations and the B64 remainder are unchanged. The paired
    route remains concrete for psi and the Euler constant.
    """
    if z.real.lower() < F(1, 4) or z.real.upper() > 3 or z.imag.abs_upper() > 101:
        raise ValueError("Gamma source domain outside[1/4,3] x[-101,101]")
    w = z + CBox.exact(64)
    logw = log_complex(w)
    inverse = CBox.exact(1) / w
    inverse_square = inverse * inverse
    power = inverse
    value = (w - CBox.exact(F(1, 2))) * logw - w + CBox(
        half_log_two_pi_box(), Box.rational(0))
    for coefficient, _ in stirling_coefficients():
        value = value + power.scale(coefficient)
        power = power * inverse_square
    return value.widen(F(4, 63 * 6 ** 64))


def gamma_box(z):
    COUNTERS["gamma"] += 1
    PERFORMANCE_COUNTERS["gamma_value_only"] += 1
    logarithm = _stirling_log_value_only(z)
    # Do not feed unreduced logGamma(w), whose real part exceeds16, to exp.
    # The power-of-two rescaling is exact; uncertainty of log2 is retained.
    k = floor(logarithm.real.midpoint() / log2_box().midpoint())
    reduced = CBox(logarithm.real - log2_box().scale(k), logarithm.imag)
    if reduced.real.lower() < -2 or reduced.real.upper() > 2:
        raise ArithmeticError("scaled Gamma exp domain not certified")
    numerator = exp_complex(reduced).scale(pow2(k))
    denominator = CBox.exact(1)
    for j in range(64):
        denominator = denominator * (z + CBox.exact(j))
    return numerator / denominator


def psi_box(z):
    COUNTERS["psi"] += 1
    _, derivative = _stirling_log_and_derivative(z)
    for j in range(64):
        derivative = derivative - CBox.exact(1) / (z + CBox.exact(j))
    return derivative


def euler_constant_box():
    # Exact identity gamma_E=-psi(1), evaluated by this new analytic route.
    return -psi_box(CBox.exact(1)).real


def thermal_g(s, y=10000):
    if type(y) is not int or y != 10000:
        raise ValueError("the first thermal catalogue has fixedY10000")
    ly = logarithm_integer(y)
    y_power = exp_complex(CBox(s.real * ly, s.imag * ly))
    return y_power * gamma_box(s + CBox.exact(1))


def arch_integrand(u, y=10000):
    """Exact B(u) on numeric circle nodes away from0.

    The analytic extension B(0)=f(1)/2 is a separate prerequisite of the
    Cauchy envelope, never silently substituted into a quotient enclosure.
    exp(2u) is obtained by squaring exp(u), respecting the exp domain.
    """
    if type(y) is not int or y != 10000:
        raise ValueError("fixedY10000 required")
    COUNTERS["arch"] += 1
    distance = u.norm_box().lower()
    if distance < F(1, 128):
        raise ArithmeticError("arch quotient node too close to removable endpoint")
    eu, emu = exp_complex(u), exp_complex(-u)
    first = (eu * eu) * exp_complex(eu.scale(F(-1, y)))
    second = emu * exp_complex(emu.scale(F(-1, y)))
    f1 = f1_box(y)
    numerator = (first + second).scale(F(1, y)) - CBox(f1.scale(2), Box.rational(0))
    denominator = eu - emu
    return numerator / denominator
