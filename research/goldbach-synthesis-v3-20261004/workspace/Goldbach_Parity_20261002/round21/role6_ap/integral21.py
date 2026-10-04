"""NEW AP21 log weight, uniform derivative guards and rational Darboux integrals."""
from __future__ import annotations

from fractions import Fraction

from outward import add, neg, scale, mul, iv_json


def quotient(a: tuple, b: tuple) -> tuple:
    assert b[0] > 0
    values = (a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1])
    return min(values), max(values)


def weight(oracle, n: int, t: int, y: Fraction | int) -> tuple:
    y = Fraction(y)
    assert y > 1 and n - t * y > 1
    numerator = oracle.log(n - t * y)
    denominator = oracle.log(y)
    assert numerator[0] > 0 and denominator[0] > 0
    return quotient(numerator, denominator)


def derivative(oracle, n: int, t: int, y: Fraction | int) -> tuple:
    y = Fraction(y)
    candidate = n - t * y
    log_y = oracle.log(y)
    assert candidate > 1 and log_y[0] > 0
    first = quotient((Fraction(t), Fraction(t)), scale(log_y, candidate))
    second = quotient(oracle.log(candidate), scale(mul(log_y, log_y), y))
    return neg(add(first, second))


def integral(oracle, n: int, t: int, lower: int, upper: int, pieces: int = 32) -> tuple[tuple, dict]:
    if lower > upper:
        zero = (Fraction(0), Fraction(0))
        return zero, {"empty": True, "L": lower, "U": upper, "pieces": 0, "interval": iv_json(zero)}
    left, right = Fraction(lower - 1), Fraction(upper)
    assert left > 1 and n - t * right > 1 and left < right
    step = (right - left) / pieces
    nodes = [weight(oracle, n, t, left + step * index) for index in range(pieces + 1)]
    lo = step * sum((value[0] for value in nodes[1:]), Fraction(0))
    hi = step * sum((value[1] for value in nodes[:-1]), Fraction(0))
    assert lo > 0 and lo <= hi
    result = lo, hi
    return result, {"empty": False, "L": lower, "U": upper,
                    "continuous_endpoints": [str(left), str(right)], "pieces": pieces,
                    "mesh_step": str(step), "interval": iv_json(result),
                    "method": "monotone decreasing right/left rational Darboux sums",
                    "node_intervals": [iv_json(value) for value in nodes],
                    "float_operations": 0}


class IntegralCache:
    def __init__(self, oracle, stream):
        self.oracle = oracle
        self.stream = stream
        self.cache = {}
        self.guards = {}

    def get(self, n: int, t: int, lower: int, upper: int, pieces: int = 32) -> tuple:
        key = n, t, lower, upper, pieces
        if key not in self.cache:
            result, metadata = integral(self.oracle, n, t, lower, upper, pieces)
            identifier = len(self.cache)
            self.cache[key] = result, identifier
            self.stream.emit({"kind": "Darboux_log_integral", "id": identifier,
                              "N": n, "t": t, **metadata})
        return self.cache[key]

    def guard(self, n: int, t: int, lower: int, upper: int, source_a: int | None) -> dict:
        key = n, t, lower, upper, source_a
        if key in self.guards:
            return self.guards[key]
        if lower > upper:
            result = {"empty": True, "generic_guards": True, "source_16_over_7_applied": False}
        else:
            left, right = Fraction(lower - 1), Fraction(upper)
            assert left > 1 and n - t * right > 1
            f_left = weight(self.oracle, n, t, left)
            f_right = weight(self.oracle, n, t, right)
            log_right = self.oracle.log(right)
            log_left = self.oracle.log(left)
            j_left = n - t * left
            j_right = n - t * right
            derivative_upper = -Fraction(t, 1) / (j_left * log_right[1])
            derivative_lower = (-Fraction(t, 1) / (j_right * log_left[0])
                                - self.oracle.log(j_left)[1] / (left * log_left[0] ** 2))
            assert derivative_lower <= derivative_upper < 0
            derivative_points = [derivative(self.oracle, n, t, y) for y in (left, (left + right) / 2, right)]
            assert all(value[1] < 0 for value in derivative_points)
            variation = add(f_left, neg(f_right))
            assert variation[0] > 0
            source_bound = source_a is not None and left >= source_a
            if source_bound:
                assert f_left[1] < Fraction(16, 7)
                assert self.oracle.log(source_a)[0] >= Fraction(7, 16) * self.oracle.log(n)[1]
            result = {"empty": False, "generic_guards": True,
                      "A_gt_one": True, "N_minus_tU_gt_one": True,
                      "A": str(left), "U": str(right), "f_A": iv_json(f_left),
                      "f_U": iv_json(f_right), "variation_exact_FTC": iv_json(variation),
                      "variation_identity": "integral abs f'=f(A)-f(U)",
                      "universal_derivative_bounds_on_entire_compact": iv_json((derivative_lower, derivative_upper)),
                      "derivative_control_points": [iv_json(value) for value in derivative_points],
                      "source_16_over_7_applied": source_bound,
                      "source_f_bound_guard": source_a,
                      "f_interval": (f_left, f_right)}
        self.guards[key] = result
        self.stream.emit({"kind": "weight_variation_guard", "N": n, "t": t,
                          "L": lower, "U": upper,
                          **{name: value for name, value in result.items() if name != "f_interval"}})
        return result
