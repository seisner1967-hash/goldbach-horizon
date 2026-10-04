"""New component bank of15.3, not globalH1. SOURCE ONLY before its own gate.

No source-import, dryrun, compilation, mathematical probe, or invocation has
yet been authorized. A future launcher must freeze every dependency first.
"""
import argparse
import json
from pathlib import Path
from fractions import Fraction as F
from dyadic_r01 import Box, CBox, Point, EPS, pow2, rational_json, COUNTERS as PRIMITIVES
from analytic_r01 import (gamma_box, em_zeta_and_derivative,
                               a_log_derivative, COUNTERS as ANALYTIC)
from kernel_r01 import (kernel_catalogue, polynomial_quadrature,
                             vertical_polynomial_integral, real_polynomial_integral,
                             exact_point_power, RADIUS_STATS)
from reference_r01 import (gamma_integral_reference, gamma_norm_squared_reference,
                                known_zeta_reference, complex_disjoint,
                                strict_complex_width_guard, zeta_derivative_zero_reference,
                                integer_binary_power_reference)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--contract", required=True)
    parser.add_argument("--actual-start", required=True)
    args = parser.parse_args()
    contract = json.loads(Path(args.contract).read_text(encoding="utf-8"))
    start = json.loads(Path(args.actual_start).read_text(encoding="utf-8"))
    if (contract["bank_id"] != "THERMAL_COMPONENT_R01_AUX22"
            or contract["gamma_phase_cases"] != 15 or contract["reference_cells_each"] != 2240
            or start["scope"] != "THERMAL_COMPONENT_R01_AUX_ONLY" or not start["captures_complete"]):
        raise RuntimeError("fixed contract/actualSTART scope required")
    import dyadic_r01 as ground
    certificate_path = Path(args.output).parent / "sqrt_certificates_r01.jsonl"
    certificate_stream = certificate_path.open("x", encoding="utf-8")
    def record_sqrt(certificate):
        certificate_stream.write(json.dumps(certificate, sort_keys=True) + "\n")
    ground.SQRT_OBSERVER = record_sqrt
    cases, failures, unresolved, mutations = [], [], [], []
    # The former representation failure is exercised first, using new exact
    # points and independent Gaussian-integer binary powers, not old results.
    for exponent, sign in ((512, 1), (768, -1)):
        point, point_radius = Point.from_box(CBox.exact(F(3, 4) + sign * EPS,
                                                       sign * (F(1, 8) + EPS)))
        if point_radius != 0:
            raise ArithmeticError("exact regression point lost exactness")
        evaluated, radius = exact_point_power(point, exponent)
        enclosure = evaluated.box().widen(radius)
        reference = integer_binary_power_reference(point, exponent)
        agreement = not complex_disjoint(enclosure, reference)
        if not agreement:
            failures.append("GRID_RADIUS_POWER_" + str(exponent))
        cases.append({"kind": "GRID_RADIUS_POWER_REGRESSION", "exponent": exponent,
                      "point": point.box().as_json(), "enclosure": enclosure.as_json(),
                      "reference": reference.as_json(), "radius": rational_json(radius),
                      "radius_denominator_bits": radius.denominator.bit_length(),
                      "agreement": agreement, "uses_old_result": False})
        print("GRID_RADIUS_POWER", exponent, "ENCODABLE_FIELDS_BUILT", flush=True)
    gamma_catalogue = [(sigma, gamma) for sigma in (F(1), F(3, 2), F(2))
                       for gamma in (0, -5, 5, -19, 19)]
    if len(gamma_catalogue) != 15:
        raise ArithmeticError("unfiltered15-case phase catalogue count failed")
    for index, (sigma, gamma) in enumerate(gamma_catalogue):
        print("GAMMA_PHASE", index + 1, len(gamma_catalogue), str(sigma), gamma, flush=True)
        evaluated = gamma_box(CBox.exact(sigma, gamma))
        width = strict_complex_width_guard(evaluated, pow2(-81))
        reference, certificate = gamma_integral_reference(sigma, gamma)
        norm_squared = evaluated.real.square() + evaluated.imag.square()
        norm_reference = gamma_norm_squared_reference(sigma, gamma)
        phase_agreement = not complex_disjoint(evaluated, reference)
        norm_agreement = norm_squared.intersects(norm_reference)
        reference_norm_lower = reference.norm_box().lower()
        relative_width = ((reference.real.width() + reference.imag.width()) / reference_norm_lower
                          if reference_norm_lower > 0 else F(1))
        phase_informative = reference_norm_lower > 0 and relative_width <= F(1, 1024)
        phase_mutant = evaluated * CBox.exact(0, 1)
        phase_mutant_disjoint = complex_disjoint(phase_mutant, reference)
        if not phase_agreement or not norm_agreement:
            failures.append("GAMMA_PHASE_OR_NORM_" + str(index))
        if not phase_mutant_disjoint:
            unresolved.append("GAMMA_PHASE_MUTANT_" + str(index))
        if not phase_informative:
            unresolved.append("GAMMA_PHASE_REFERENCE_TOO_WIDE_" + str(index))
        mutations.append({"case": index, "mutation": "MULTIPLY_GAMMA_BY_I",
                          "disjoint": phase_mutant_disjoint, "mutant": phase_mutant.as_json(),
                          "correct": reference.as_json()})
        cases.append({"kind": "COMPLEX_GAMMA_NEW_STIRLING_VS_NEW_INTEGRAL",
                      "sigma": rational_json(sigma), "gamma": gamma,
                      "evaluated": evaluated.as_json(), "reference": reference.as_json(),
                      "norm_squared": norm_squared.as_json(), "norm_reference": norm_reference.as_json(),
                      "actual_value_width": rational_json(width),
                      "phase_agreement": phase_agreement, "norm_agreement": norm_agreement,
                      "phase_informative": phase_informative,
                      "reference_relative_width_upper": rational_json(relative_width),
                      "reference_certificate": certificate})
    # Fixed extreme inputs validate actual finite widths of the new route.
    # Their value is not supplied by a norm-only phase oracle.
    for sigma in (F(5, 16), F(43, 16)):
        for gamma in (-100, 100):
            value = gamma_box(CBox.exact(sigma, gamma))
            width = strict_complex_width_guard(value, pow2(-81))
            cases.append({"kind": "GAMMA_DOMAIN_WIDTH_GUARD_ONLY", "sigma": rational_json(sigma),
                          "gamma": gamma, "value": value.as_json(),
                          "width": rational_json(width), "independent_phase_reference": False,
                          "phase_validation_claim": False})
    for s in (F(0), F(2)):
        value, derivative = em_zeta_and_derivative(CBox.exact(s))
        strict_complex_width_guard(value, pow2(-81))
        strict_complex_width_guard(derivative, pow2(-81))
        reference = known_zeta_reference(s)
        agreement = not complex_disjoint(value, reference)
        if not agreement:
            failures.append("EM_EXACT_CONSTANT_" + str(s))
        mutant = -value
        disjoint = complex_disjoint(mutant, reference)
        if not disjoint:
            unresolved.append("EM_SIGN_MUTANT_" + str(s))
        mutations.append({"case": str(s), "mutation": "NEGATE_ZETA", "disjoint": disjoint,
                          "mutant": mutant.as_json(), "correct": reference.as_json()})
        derivative_reference = zeta_derivative_zero_reference() if s == 0 else None
        derivative_agreement = (not complex_disjoint(derivative, derivative_reference)
                                if s == 0 else None)
        if s == 0:
            if not derivative_agreement:
                failures.append("EM_DERIVATIVE_ZERO")
            derivative_mutant = -derivative
            derivative_disjoint = complex_disjoint(derivative_mutant, derivative_reference)
            if not derivative_disjoint:
                unresolved.append("EM_DERIVATIVE_SIGN_MUTANT")
            mutations.append({"case": "0", "mutation": "NEGATE_ZETA_DERIVATIVE",
                              "disjoint": derivative_disjoint, "mutant": derivative_mutant.as_json(),
                              "correct": derivative_reference.as_json()})
        cases.append({"kind": "EM_NEW_EXACT_CONSTANT", "s": rational_json(s),
                      "value": value.as_json(), "derivative": derivative.as_json(),
                      "reference": reference.as_json(), "agreement": agreement,
                      "derivative_independent_reference": s == 0,
                      "derivative_reference": derivative_reference.as_json() if s == 0 else None,
                      "derivative_agreement": derivative_agreement})
    for real in (F(-11, 16), F(-5, 16), F(21, 16), F(27, 16)):
        for imag in (-F(1597, 16), F(1597, 16)):
            value = a_log_derivative(CBox.exact(real, imag))
            width = strict_complex_width_guard(value, pow2(-81))
            cases.append({"kind": "EM_LOGDERIV_DOMAIN_WIDTH_GUARD_ONLY",
                          "real": rational_json(real), "imag": rational_json(imag),
                          "value": value.as_json(), "width": rational_json(width),
                          "independent_value_reference": False})
    vertical = kernel_catalogue(128, F(3, 16), F(1, 8), 64, True)
    real = kernel_catalogue(96, F(1, 8), F(1, 32), 32, False)
    for name, catalogue, half, degrees, orientation in (
            ("VERTICAL", vertical, F(1, 8), (0, 1, 2, 3, 4, 16, 32, 64), True),
            ("REAL", real, F(1, 32), (0, 1, 2, 31, 32), False)):
        for degree in degrees:
            total = polynomial_quadrature(catalogue, degree)
            expected = (vertical_polynomial_integral(degree, half) if orientation
                        else real_polynomial_integral(degree, half))
            agreement = not complex_disjoint(total.enclosure(), expected)
            if not agreement:
                failures.append(name + "_POLYNOMIAL_" + str(degree))
            cases.append({"kind": name + "_EXACT_POLYNOMIAL", "degree": degree,
                          "enclosure": total.enclosure().as_json(), "reference": expected.as_json(),
                          "agreement": agreement, "four_budgets": total.as_json()})
    wrong_orientation = kernel_catalogue(128, F(3, 16), F(1, 8), 64, False)
    # Wrong weights still carry the1/(2pi) normalization for a fair i² mutation.
    wrong_total = polynomial_quadrature(wrong_orientation, 2).enclosure()
    from dyadic_r01 import pi_box
    wrong_total = wrong_total / CBox(pi_box().scale(2), Box.rational(0))
    correct = vertical_polynomial_integral(2, F(1, 8))
    wrong_disjoint = complex_disjoint(wrong_total, correct)
    if not wrong_disjoint:
        unresolved.append("DFT_OMIT_I_TO_K")
    mutations.append({"mutation": "DFT_OMIT_I_TO_K", "disjoint": wrong_disjoint,
                      "mutant": wrong_total.as_json(), "correct": correct.as_json()})
    # At exponent m the discrete transform aliases onto degree0. The exact
    # integral is different; demonstrating and paying this term is required.
    for name, catalogue, radius, half, exponent, orientation in (
            ("VERTICAL", vertical, F(3, 16), F(1, 8), 128, True),
            ("REAL", real, F(1, 8), F(1, 32), 96, False)):
        actual = polynomial_quadrature(catalogue, exponent)
        aliased = CBox.exact(2 * half * radius ** exponent)
        if orientation:
            aliased = aliased / CBox(pi_box().scale(2), Box.rational(0))
        integral = (vertical_polynomial_integral(exponent, half) if orientation
                    else real_polynomial_integral(exponent, half))
        alias_match = not complex_disjoint(actual.enclosure(), aliased)
        alias_is_nonzero_error = complex_disjoint(actual.enclosure(), integral)
        if not alias_match:
            failures.append(name + "_ALIAS_FORMULA")
        if not alias_is_nonzero_error:
            unresolved.append(name + "_ALIAS_DISCRIMINATION")
        cases.append({"kind": name + "_PAID_ALIAS_COUNTERTEST", "degree": exponent,
                      "actual": actual.enclosure().as_json(), "alias_reference": aliased.as_json(),
                      "true_integral": integral.as_json(), "alias_match": alias_match,
                      "nonzero_error": alias_is_nonzero_error, "four_budgets": actual.as_json()})
    verdict = ("THERMAL_COMPONENT_R01_SOURCE_COUNTEREXAMPLE" if failures else
               "THERMAL_COMPONENT_R01_UNRESOLVED" if unresolved else
               "THERMAL_COMPONENT_R01_AUX_PASS")
    result = {"schema": "ROUND22_THERMAL_COMPONENT_RESULT_R01", "status": verdict,
              "verdict": verdict, "selection": "15.3", "N_label_only": 100000000,
              "Gamma_phase_cases_before_masks": 15, "Gamma_reference_cells_each": 2240,
              "Gamma_reference_cells_total": 33600, "cases": cases,
              "failures": failures, "unresolved": unresolved, "mutations": mutations,
              "primitive_counts": PRIMITIVES, "analytic_counts": ANALYTIC,
              "radius_transport": {"updates": RADIUS_STATS["updates"],
                                   "outward_rounding_sum_upper": rational_json(RADIUS_STATS["rounding_sum_upper"]),
                                   "max_denominator_bits": RADIUS_STATS["max_denominator_bits"]},
              "previous_incomplete_values_used_as_oracle": False,
              "old_bank_replays": 0, "H1_numeric_claim": False, "H1_formal_claim": False,
              "coefficient_N_claim": False, "D_N_claim": False, "WIN": False}
    from checker_r01 import verify
    result["independent_checker"] = verify(result)
    if not result["independent_checker"]["checker_PASS"]:
        result["failures"].extend(result["independent_checker"]["checker_errors"])
        verdict = result["status"] = result["verdict"] = "THERMAL_COMPONENT_R01_SOURCE_COUNTEREXAMPLE"
    certificate_stream.close()
    with open(args.output, "x", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    print(verdict, flush=True)
    return 0 if not failures and not unresolved else 2


if __name__ == "__main__":
    raise SystemExit(main())
