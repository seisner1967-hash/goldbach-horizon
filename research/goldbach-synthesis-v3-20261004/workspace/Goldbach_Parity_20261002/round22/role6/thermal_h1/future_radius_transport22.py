"""FutureH1 representation, SOURCE ONLY, unused by frozen component bank.

Imports the frozen ground rules only after a future distinct producer gate.
No mathematical invocation is authorized for this file in the current bank.
"""
from fractions import Fraction as F
from thermal_dyadic22 import Point, EPS, SCALE, ceil, exact, pow2, point_product


def outward_radius(candidate):
    candidate = exact(candidate)
    if candidate < 0:
        raise ValueError("negative exact radius")
    result = F(ceil(candidate * SCALE), SCALE)
    rounding = result - candidate
    if not 0 <= rounding <= EPS:
        raise ArithmeticError("actual radius-round certificate failed")
    return result, rounding


class GridRadiusTrack:
    """Source interface with actual radius-round and product-round budgets."""
    __slots__ = ("point", "radius", "step", "step_radius", "U", "index", "last_index", "closed",
                 "product_round_sum", "radius_round_sum")

    def __init__(self, seed, step, U, last_index):
        if last_index not in (799, 999999):
            raise ValueError("one of the two fixed future catalogues required")
        self.point, self.radius = Point.from_box(seed)
        self.step, self.step_radius = Point.from_box(step)
        self.U, self.index, self.last_index = exact(U), 0, last_index
        if (self.U < 0 or self.radius > pow2(-200)
                or self.step_radius > pow2(-200)):
            raise ArithmeticError("actual future seed/step radius guard failed")
        steps = 800 if last_index == 799 else 1000000
        self.closed = 2 * self.radius + 2 * steps * (self.U * self.step_radius + 2 * EPS)
        self.product_round_sum = self.radius_round_sum = F(0)

    def box(self):
        return self.point.box().widen(self.radius)

    def advance(self):
        if self.index >= self.last_index:
            raise ValueError("future recurrence outside fixed catalogue")
        self.point, product_round = point_product(self.point, self.step)
        candidate = (1 + self.step_radius) * self.radius + self.U * self.step_radius + product_round
        self.radius, radius_round = outward_radius(candidate)
        if product_round + radius_round > 2 * EPS:
            raise ArithmeticError("actual combined two-round budget failed")
        self.product_round_sum += product_round
        self.radius_round_sum += radius_round
        self.index += 1
        if self.radius > self.closed:
            raise ArithmeticError("actual future finite closed-radius bound failed")
