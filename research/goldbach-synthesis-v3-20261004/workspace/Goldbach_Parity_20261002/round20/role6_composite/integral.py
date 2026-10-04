"""NEW composite-only directed rational monotone integral; shared frozen log helper unchanged."""
from fractions import Fraction

from arithmetic import N, frac
from outward import SCALE, iv_json


def monotone_integral20(oracle, t, qlo, qhi, store, pieces=128):
    if qlo > qhi:
        return (Fraction(0), Fraction(0)), {"empty": True, "qlo": qlo, "qhi": qhi, "pieces": 0}
    left, right = Fraction(qlo - 1), Fraction(qhi)
    assert left > 1 and N - t * right > 0
    step = (right - left) / pieces
    ratio_bounds = []
    records = []
    for i in range(pieces + 1):
        y = left + i * step
        logj = oracle.scaled(N - t * y)
        logy = oracle.scaled(y)
        assert logj[0] > 0 and logy[0] > 0
        # Positive numerator/denominator intervals: lo/hi <= true ratio <= hi/lo.
        # The additional directed rounding at common 2^128 prevents GCD blowup.
        lower = (SCALE * logj[0]) // logy[1]
        upper = -((-SCALE * logj[1]) // logy[0])
        assert lower <= upper
        ratio_bounds.append((lower, upper))
        records.append({"point": i, "y": frac(y), "N_minus_ty": frac(N - t * y),
                        "logj_scaled_bounds": list(logj), "logy_scaled_bounds": list(logy),
                        "ratio_directed_scaled_bounds": [lower, upper],
                        "ratio_certificate": iv_json((Fraction(lower, SCALE), Fraction(upper, SCALE)))})
    lower_integral = step * Fraction(sum(pair[0] for pair in ratio_bounds[1:]), SCALE)
    upper_integral = step * Fraction(sum(pair[1] for pair in ratio_bounds[:-1]), SCALE)
    assert lower_integral <= upper_integral
    position = store.put({"t": t, "qlo": qlo, "qhi": qhi,
                          "left_endpoint": frac(left), "right_endpoint": frac(right),
                          "pieces": pieces, "mesh_step": frac(step), "all_129_mesh_points": records,
                          "monotone_function": "positive decreasing log(N-t*y)/log(y)",
                          "lower_uses_right_points": True, "upper_uses_left_points": True,
                          "additional_ratio_rounding_directed_at_2pow128": True,
                          "integral_certificate": iv_json((lower_integral, upper_integral)),
                          "float_operations": 0})
    return (lower_integral, upper_integral), {"empty": False, "qlo": qlo, "qhi": qhi,
        "left_endpoint": frac(left), "right_endpoint": frac(right), "pieces": pieces,
        "mesh_step": frac(step), "full_mesh_certificate_ref": position,
        "catalog": "integral_certificates", "ratio_outward_rounding_bits": 128,
        "method": "decreasing positive function, directed lower/right and upper/left rational sums"}
