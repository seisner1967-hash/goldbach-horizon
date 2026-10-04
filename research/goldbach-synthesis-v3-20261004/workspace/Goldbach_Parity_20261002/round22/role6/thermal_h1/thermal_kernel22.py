"""Fresh integrated DFT weights and explicit four-way error propagation.

SOURCE ONLY. Vertical quadrature is over s=s0+i v: i^k is mandatory.
The Arch quadrature is over real u: its weights have no i^k.
The finite polynomial tests below exercise both that orientation and the
paid alias at degree m. They do not certify a global thermal identity.
"""
from fractions import Fraction as F
from thermal_dyadic22 import (Box, CBox, Point, EPS, exact, pow2,
                             pi_box, sin_cos_box, point_product)


def circle_node(j, m, radius):
    if type(j) is not int or type(m) is not int or not 0 <= j < m:
        raise ValueError("complete ordered circle catalogue index required")
    angle = pi_box().scale(F(2 * j, m))
    sine, cosine = sin_cos_box(angle)
    enclosure = CBox(cosine.scale(radius), sine.scale(radius))
    point, rho = Point.from_box(enclosure)
    if rho > pow2(-200):
        raise ArithmeticError("actual circle position radius guard failed")
    return point, rho, enclosure


def integrated_weight(j, m, radius, half_cell, degree, vertical):
    """Fresh DFT kernel, all even k before any summation simplification."""
    if type(vertical) is not bool or degree >= m or degree < 0:
        raise ValueError("orientation and degree<m required")
    angle = pi_box().scale(F(-2 * j, m))
    sine, cosine = sin_cos_box(angle)
    inverse_root = CBox(cosine, sine)
    inverse_root_squared = inverse_root * inverse_root
    root_power, result = CBox.exact(1), CBox.exact(0)
    for k in range(0, degree + 1, 2):
        sign = (-1) ** (k // 2) if vertical else 1
        coefficient = F(2 * sign, m * (k + 1)) * exact(half_cell) ** (k + 1) / exact(radius) ** k
        result = result + root_power.scale(coefficient)
        root_power = root_power * inverse_root_squared
    if vertical:
        divisor = CBox(pi_box().scale(2), Box.rational(0))
        result = result / divisor
    point, radius_error = Point.from_box(result)
    if radius_error > pow2(-200):
        raise ArithmeticError("constructed integrated-weight radius guard failed")
    return point, radius_error, result


def kernel_catalogue(m, radius, half_cell, degree, vertical):
    # Every j is visited; no conjugate shortcut can silently omit an input.
    return [dict(j=j, node=circle_node(j, m, radius),
                 weight=integrated_weight(j, m, radius, half_cell, degree, vertical))
            for j in range(m)]


def exact_point_power(point, exponent):
    """Polynomial evaluation with explicit accumulated norm-radius."""
    if type(exponent) is not int or exponent < 0:
        raise ValueError("nonnegative polynomial degree required")
    value, radius = Point.from_box(CBox.exact(1))
    radius = F(0)
    upper = point.abs_upper()
    for _ in range(exponent):
        value, rounding = point_product(value, point)
        radius = upper * radius + rounding
    return value, radius


class FourBudgets:
    """No category is replaced by a free tolerance; guards check real data."""
    __slots__ = ("point", "function", "position", "weights", "accumulation", "nodes")

    def __init__(self):
        self.point, _ = Point.from_box(CBox.exact(0))
        self.function = self.position = self.weights = self.accumulation = F(0)
        self.nodes = 0

    def add(self, sample_point, function_radius, position_radius, weight_point, weight_radius):
        function_radius, position_radius, weight_radius = map(
            exact, (function_radius, position_radius, weight_radius))
        if min(function_radius, position_radius, weight_radius) < 0:
            raise ValueError("negative error budget")
        product, rounding = point_product(sample_point, weight_point)
        weight_upper = weight_point.abs_upper() + weight_radius
        self.function += weight_upper * function_radius
        self.position += weight_upper * position_radius
        self.weights += sample_point.abs_upper() * weight_radius
        self.accumulation += rounding
        self.point = self.point + product
        self.nodes += 1

    def error(self):
        return self.function + self.position + self.weights + self.accumulation

    def enclosure(self):
        return self.point.box().widen(self.error())

    def as_json(self):
        from thermal_dyadic22 import rational_json
        return {"E_function": rational_json(self.function),
                "E_position": rational_json(self.position),
                "E_weights": rational_json(self.weights),
                "E_accumulation": rational_json(self.accumulation),
                "nodes": self.nodes, "point": self.point.box().as_json()}


def polynomial_quadrature(catalogue, exponent):
    total = FourBudgets()
    for item in catalogue:
        point, rho, _ = item["node"]
        value, rounding = exact_point_power(point, exponent)
        upper = point.abs_upper() + rho
        # L1 bounds are conservative upper bounds for the complex norm.
        position = F(0) if exponent == 0 else exponent * upper ** (exponent - 1) * rho
        weight, weight_radius, _ = item["weight"]
        total.add(value, rounding, position, weight, weight_radius)
    return total


def vertical_polynomial_integral(exponent, half_cell):
    if exponent % 2:
        return CBox.exact(0)
    numerator = F(2 * ((-1) ** (exponent // 2)), exponent + 1) * exact(half_cell) ** (exponent + 1)
    return CBox.exact(numerator) / CBox(pi_box().scale(2), Box.rational(0))


def real_polynomial_integral(exponent, half_cell):
    return CBox.exact(0 if exponent % 2 else F(2, exponent + 1) * exact(half_cell) ** (exponent + 1))
