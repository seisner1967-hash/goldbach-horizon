"""Independent new references for the component bank, SOURCE ONLY.

This module does not import thermal_analytic22 or any old bank. The complex
Gamma reference is the unrotated defining integral, not Stirling, reflection,
recurrence, a copied result, or a magnitude with an unproved phase.
It shares only the freshly reviewed ground arithmetic with the producer.
"""
from fractions import Fraction as F
from math import factorial
from thermal_dyadic22 import (Box, CBox, pow2, exp_box, exp_complex, pi_box,
                             Point, exact, rational_json, log_box)


def gamma_integral_reference(sigma, gamma):
    sigma, gamma = exact(sigma), exact(gamma)
    if not 1 <= sigma <= 2 or abs(gamma) > 23:
        raise ValueError("phase-reference domain sigma1..2,|gamma|<=23")
    s, one, zero = CBox.exact(sigma, gamma), CBox.exact(1), CBox.exact(0)
    degree, half_step, cell_count = 24, F(1, 64), 2240
    # P0=1, P(k+1)=(s-t)Pk+tPk'. These are derivative polynomials,
    # constructed anew; none are copied from the rotated closed bank.
    polynomials = [[one]]
    for k in range(degree):
        previous, following = polynomials[-1], []
        for j in range(k + 2):
            value = (s + CBox.exact(j)) * previous[j] if j <= k else zero
            if j:
                value = value - previous[j - 1]
            following.append(value)
        polynomials.append(following)
    # Finite linearity integrates the polynomial before visiting the grid.
    # Every coefficient is still enclosed; this saves repeated Horner work
    # without changing the degree24 Taylor truncation or its Cauchy remainder.
    integrated_polynomial = [zero for _ in range(degree + 1)]
    for k in range(0, degree + 1, 2):
        coefficient = F(2, factorial(k + 1)) * half_step ** (k + 1)
        for j, value in enumerate(polynomials[k]):
            integrated_polynomial[j] = integrated_polynomial[j] + value.scale(coefficient)
    total = zero
    max_cell_width = F(0)
    for cell in range(cell_count):
        v = F(-64) + F(2 * cell + 1, 64)
        ev = exp_box(Box.rational(v))
        amplitude = exp_complex(CBox(Box.rational(sigma * v) - ev,
                                     Box.rational(gamma * v)))
        ev_complex = CBox(ev, Box.rational(0))
        value = integrated_polynomial[-1]
        for coefficient in reversed(integrated_polynomial[:-1]):
            value = coefficient + value * ev_complex
        cell_value = amplitude * value
        total = total + cell_value
        max_cell_width = max(max_cell_width, cell_value.real.width() + cell_value.imag.width())
    # Cauchy disk radius1/4. cos(Im v)>=1/2, t^sigma<=t+t²,
    # damping bounds the latter by10. exp(23/4)<=exp6<=3^6.
    # Hence M<10*3^6<2^13; |local offset|/radius=1/16.
    cauchy = 70 * pow2(13) * F(1, 16) ** 25 / (1 - F(1, 16))
    left = F(3, 8) ** 64  # exp1>=8/3, sigma>=1.
    right = 257 * pow2(-256)  # exp6>=256, exp1>=2.
    rounding = total.real.width() + total.imag.width()
    if rounding > pow2(-120):
        raise ArithmeticError("actual independent-integral rounding guard failed")
    result = total.widen(cauchy + left + right)
    return result, {"cells": cell_count, "degree": degree,
                    "half_step": rational_json(half_step),
                    "Cauchy_radius": rational_json(F(1, 4)),
                    "Cauchy_M": 1 << 13, "Cauchy_error": rational_json(cauchy),
                    "left_tail": rational_json(left), "right_tail": rational_json(right),
                    "actual_rounding_width": rational_json(rounding),
                    "maximum_cell_width": rational_json(max_cell_width),
                    "phase_reference": True, "uses_Stirling": False,
                    "uses_old_result": False}


def gamma_norm_squared_reference(sigma, gamma):
    sigma, gamma = exact(sigma), exact(gamma)
    t = abs(gamma)
    pi = pi_box()
    if sigma not in (F(1), F(3, 2), F(2)):
        raise ValueError("reflection norm reference only three declared sigmas")
    # Stable expressions use only exp(-pi*t), never a positive large exp.
    q = exp_box(pi.scale(-t))
    one = Box.rational(1)
    if sigma == F(3, 2):
        return (pi * q).scale(2 * (t * t + F(1, 4))) / (one + q.square())
    base = one if t == 0 else (pi * q).scale(2 * t) / (one - q.square())
    return base if sigma == 1 else base.scale(1 + t * t)


def known_zeta_reference(s):
    if s == F(0):
        return CBox.exact(F(-1, 2))
    if s == F(-1, 2):
        raise ValueError("no exact constant reference for zeta(-1/2)")
    if s == F(2):
        return CBox(pi_box().square().scale(F(1, 6)), Box.rational(0))
    raise ValueError("only declared exact zeta constants are references")


def zeta_derivative_zero_reference():
    # DLMF25.6.11, exact independent special-value formula, not EM.
    return CBox(log_box(pi_box().scale(2)).scale(F(-1, 2)), Box.rational(0))


def complex_disjoint(a, b):
    return not a.real.intersects(b.real) or not a.imag.intersects(b.imag)


def strict_complex_width_guard(value, upper):
    width = value.real.width() + value.imag.width()
    if width > exact(upper):
        raise ArithmeticError("actual function enclosure exceeds fixed component guard")
    return width


def containment_relation(a, b):
    """Agreement is consistency of two independently enclosed true objects.

    Disjoint enclosures falsify at least one source claim. Overlap is never
    presented as a proof of the source identity or as a Goldbach theorem.
    """
    return "DISJOINT_COUNTEREXAMPLE" if complex_disjoint(a, b) else "CONSISTENT_OVERLAP"
