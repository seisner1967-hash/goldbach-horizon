"""Fresh actual rotated-Laplace evaluation, never imported during preparation.

21 Gamma samples are AUXILIARY.  Completeness of zeta zeros, Weil, heat,
coefficient N, and D_N are outside this bank.  No Gamma API or old data is used.
"""
import argparse
import ast
from fractions import Fraction
import hashlib
import json
from math import factorial
from pathlib import Path
import sys

import dyadic_gamma22 as arithmetic
from dyadic_gamma22 import Box, ComplexBox, exp_box, pi_box, sin_cos_box

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def qjson(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def pair_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def pair_mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def cell_coefficients(sigma, gamma, radius):
    """Exact coefficients of sum_even 2*r^(k+1)*P_k(z,w)/(k+1)!.

    g^(k)(v)=g(v)P_k(z,c*exp(v)); P_(k+1)=(z-w)P_k+w*P'_k.
    Tiny Taylor weights multiply rational coefficients before dyadic conversion.
    """
    z = (sigma, Fraction(gamma))
    previous = [(Fraction(1), Fraction(0))]
    combined = [(Fraction(0), Fraction(0)) for _ in range(13)]
    for k in range(13):
        if k % 2 == 0:
            weight = 2 * radius ** (k + 1) / factorial(k + 1)
            for j, coefficient in enumerate(previous):
                combined[j] = pair_add(combined[j],
                                       (weight * coefficient[0], weight * coefficient[1]))
        if k < 12:
            next_coefficients = []
            for j in range(k + 2):
                a = pair_mul((z[0] + j, z[1]), previous[j]) if j <= k else (Fraction(0), Fraction(0))
                b = previous[j - 1] if j > 0 else (Fraction(0), Fraction(0))
                next_coefficients.append((a[0] - b[0], a[1] - b[1]))
            previous = next_coefficients
    return [ComplexBox.exact(a, b) for a, b in combined]


def polynomial(coefficients, w):
    value = coefficients[-1]
    for coefficient in reversed(coefficients[:-1]):
        value = value * w + coefficient
    return value


def reflected_reference(sigma, gamma, pi):
    """Independent Gamma reflection/recurrence, in factored normalized form."""
    g = abs(gamma)
    one = Box.rational(1)
    if g == 0:
        square = pi.scale(Fraction(1, 4)) if sigma == Fraction(3, 2) else one
    else:
        q = exp_box(pi.scale(-2 * g))
        v = exp_box(pi.scale(Fraction(-g, 2)))
        if sigma == Fraction(3, 2):
            square = (pi * v).scale(2 * (Fraction(g * g) + Fraction(1, 4))) / (one + q)
        else:
            square = (pi * v).scale(2 * g) / (one - q)
            if sigma == 2:
                square = square.scale(1 + g * g)
    return square.sqrt(), square


def verify_start(start_path, output):
    start = json.loads(start_path.read_text(encoding="utf-8"))
    gate_path = Path(start["gate_path"]).resolve()
    expected = BASE / ".arbor/sessions/parity/.coordinator/messages/round22_gamma_numeric_authorization.json"
    if gate_path != expected.resolve() or sha(gate_path) != start["gate_sha256"]:
        raise RuntimeError("exact distinct Gamma root gate required")
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    if gate.get("status") != "AUTHORIZED" or gate.get("actor") != "ROLE6":
        raise RuntimeError("numeric actor authorization missing")
    if gate.get("bank_id") != "GAMMA_ROTATED_LAPLACE_AUX22" or start.get("scope") != "GAMMA_H2_AUX_ONLY":
        raise RuntimeError("wrong bank or scope")
    if output.resolve().parent != start_path.resolve().parent:
        raise RuntimeError("output must stay in unique actual directory")
    if start.get("captures_complete") is not True:
        raise RuntimeError("actual PREEXEC captures required")
    return start


def source_guards():
    examined = []
    for filename in ("gamma_bank22.py", "dyadic_gamma22.py"):
        path = HERE / filename
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
                raise RuntimeError("floating-point/complex literal prohibited")
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in {"float", "complex", "gamma", "lgamma"}:
                raise RuntimeError("floating-point or Gamma API call prohibited")
        examined.append({"path": str(path), "sha256": sha(path), "AST_zero_float_guard": True})
    return examined


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--actual-start", required=True)
    args = parser.parse_args()
    output, contract_path = Path(args.output), Path(args.contract)
    start = verify_start(Path(args.actual_start), output)
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    expected = {"N_metadata": 100000000, "sigma_rationals": ["1", "3/2", "2"],
                "gamma_integers": [0, 1, -1, 10, -10, 100, -100],
                "canonical_case_count_before_any_mask": 21, "dyadic_bits": 768,
                "v_left": -32, "v_right": 6, "cell_count": 9728,
                "cell_step": "1/256", "cell_radius": "1/512", "Taylor_degree": 12,
                "exp_Taylor_degree": 128, "sin_cos_term_count_each": 128,
                "atan_term_count_each": 256,
                "normalized_absolute_tolerance": "1/100000000",
                "arithmetic_component_width_cap": "1/1208925819614629174706176",
                "mutant_case_abs_gamma": [1, 10], "mutant_case_count": 12,
                "expected_exp_calls": 38981, "expected_sin_cos_calls": 68117,
                "expected_sqrt_certificates": 43}
    for key, value in expected.items():
        if contract.get(key) != value:
            raise RuntimeError("frozen canonical parameter mismatch: " + key)
    guard_receipts = source_guards()
    sigma_values = [Fraction(s) for s in contract["sigma_rationals"]]
    cases = [(sigma, gamma) for sigma in sigma_values for gamma in contract["gamma_integers"]]
    # The catalogue exists BEFORE applying the sole declared mutation subset.
    if len(cases) != 21 or len(set(cases)) != 21:
        raise RuntimeError("complete canonical catalogue required")
    radius = Fraction(1, 512)
    step = Fraction(1, 256)
    tolerance = Fraction(1, 100000000)
    arithmetic_cap = Fraction(1, 1 << 80)
    quadrature_error = Fraction(38 * 64, 63 * (1 << 52))
    left_tail = Fraction(3, 8) ** 32
    right_tail = Fraction(516, 1 << 128)
    analytic_radius = quadrature_error + left_tail + right_tail
    certificate_path = output.parent / "gamma_sqrt_certificates22.jsonl"
    with certificate_path.open("x", encoding="utf-8", newline="\n") as certificates:
        def record(certificate):
            certificates.write(json.dumps(certificate, sort_keys=True) + "\n")
        arithmetic.SQRT_OBSERVER = record
        pi = pi_box()
        c = Box.rational(2).sqrt().scale(Fraction(1, 2))
        coefficients = {case: cell_coefficients(*case, radius) for case in cases}
        sums = {case: ComplexBox.exact(0) for case in cases}
        for j in range(9728):
            center = Fraction(-32) + (2 * j + 1) * radius
            v = Box.rational(center)
            e_v = exp_box(v)
            real_w = c * e_v
            amplitudes = {sigma: exp_box(v.scale(sigma) - real_w) for sigma in sigma_values}
            trig = {}
            for gamma in contract["gamma_integers"]:
                sign = 1 if gamma >= 0 else -1
                phase = v.scale(gamma) - real_w.scale(sign)
                trig[gamma] = sin_cos_box(phase, pi)
            for sigma, gamma in cases:
                sign = 1 if gamma >= 0 else -1
                w = ComplexBox(real_w, real_w.scale(sign))
                sine, cosine = trig[gamma]
                g = ComplexBox(amplitudes[sigma] * cosine, amplitudes[sigma] * sine)
                sums[(sigma, gamma)] = sums[(sigma, gamma)] + g * polynomial(coefficients[(sigma, gamma)], w)
            if (j + 1) % 256 == 0:
                print(json.dumps({"cells_completed_each_case": j + 1,
                                  "cells_total_each_case": 9728, "case_count": 21}), flush=True)
        rows = []
        mutation_detected = 0
        counterexample = False
        unresolved = False
        for sigma, gamma in cases:
            approximate = sums[(sigma, gamma)]
            width = max(approximate.real.width(), approximate.imag.width())
            enclosed = approximate.widen(analytic_radius)
            norm = enclosed.norm()
            reference, reference_square = reflected_reference(sigma, gamma, pi)
            overlaps = norm.intersects(reference)
            distance = norm.max_distance(reference)
            width_ok = width <= arithmetic_cap
            bound_ok = norm.upper() <= 2
            contradiction = (not overlaps) or norm.lower() > 2
            case_pass = overlaps and width_ok and bound_ok and distance <= tolerance
            counterexample = counterexample or contradiction
            unresolved = unresolved or (not case_pass and not contradiction)
            a = pi.scale(Fraction(abs(gamma), 4))
            theta = pi.scale(Fraction(1 if gamma >= 0 else -1, 4))
            phase_sine, phase_cosine = sin_cos_box(theta.scale(sigma), pi)
            genuine_gamma = enclosed * ComplexBox(phase_cosine, phase_sine)
            attenuation = exp_box(-a)
            genuine_gamma = ComplexBox(genuine_gamma.real * attenuation,
                                       genuine_gamma.imag * attenuation)
            mutant = {"applicable": abs(gamma) in (1, 10)}
            if mutant["applicable"]:
                wrong = norm * exp_box(a)
                detected = not wrong.intersects(reference) and wrong.lower() > 2
                mutation_detected += int(detected)
                unresolved = unresolved or not detected
                mutant.update({"normalized_wrong_norm": wrong.as_json(),
                               "disjoint_from_reference": not wrong.intersects(reference),
                               "H2_violation_lower_greater_than_two": wrong.lower() > 2,
                               "detected": detected})
            row = {"sigma": str(sigma), "gamma": gamma,
                   "cells_represented": 9728, "cells_actually_evaluated": 9728,
                   "Taylor_degree": 12, "integral_polynomial": approximate.as_json(),
                   "integral_with_all_errors": enclosed.as_json(),
                   "genuine_Gamma_rectangle": genuine_gamma.as_json(),
                   "normalized_norm": norm.as_json(), "independent_reference_norm": reference.as_json(),
                   "independent_reference_square": reference_square.as_json(),
                   "arithmetic_component_width": qjson(width), "arithmetic_cap_met": width_ok,
                   "target_intersects": overlaps, "max_distance": qjson(distance),
                   "absolute_tolerance_met": distance <= tolerance, "H2_sample_upper_at_most_two": bound_ok,
                   "omitted_attenuation_mutant": mutant,
                   "zero_mutant_not_discriminated_at_this_tolerance": reference.upper() <= tolerance,
                   "status": "COUNTEREXAMPLE_ENCLOSURES_DISJOINT" if contradiction else
                             ("GAMMA_AUX_CASE_PASS" if case_pass else "UNRESOLVED")}
            rows.append(row)
            print(json.dumps({"sigma": str(sigma), "gamma": gamma,
                              "case_status": row["status"], "mutant": mutant.get("detected")}), flush=True)
        arithmetic.SQRT_OBSERVER = None
    expected_counters = {"exp": 38981, "sin_cos": 68117, "sqrt": 43, "pi": 1}
    if arithmetic.COUNTERS != expected_counters:
        raise ArithmeticError("actual primitive/certificate counts disagree with full catalogue")
    verdict = "COUNTEREXAMPLE_ENCLOSURES_DISJOINT" if counterexample else (
        "UNRESOLVED" if unresolved or mutation_detected != 12 else "GAMMA_ROTATED_LAPLACE_AUX_PASS")
    result = {"schema": "round22.gamma_h2_aux.result.v1", "bank_id": contract["bank_id"],
              "scope": "GAMMA_H2_AUX_ONLY", "verdict": verdict, "status": verdict,
              "N_metadata": 100000000, "N_is_only_scale_label_not_a_prime_or_trace_evaluation": True,
              "canonical_cases_before_any_mask": 21, "cases_evaluated": len(rows),
              "fresh_cases_times_cells": 21 * 9728, "shared_exp_grid_is_new_within_this_attempt": True,
              "analytic_radius": qjson(analytic_radius), "quadrature_error": qjson(quadrature_error),
              "left_tail": qjson(left_tail), "right_tail": qjson(right_tail),
              "arithmetic_width_cap": qjson(arithmetic_cap), "tolerance": qjson(tolerance),
              "mutation_applicable": 12, "mutation_detected": mutation_detected,
              "noninformative_zero_mutant_cases": [row for row in rows if row["zero_mutant_not_discriminated_at_this_tolerance"]],
              "source_guards": guard_receipts, "primitive_counters": arithmetic.COUNTERS,
              "sqrt_certificate_path": str(certificate_path), "sqrt_certificate_sha256": sha(certificate_path),
              "actual_attempt_token": start["attempt_token"], "contract_sha256": sha(contract_path),
              "external_identity_obligations_remain_visible": contract["external_analytic_obligation"],
              "Lean_compilations": 0, "Weil_evaluations": 0, "heat_evaluations": 0,
              "coefficient_N_evaluations": 0, "D_N_claim": False, "WIN": False,
              "cases": rows}
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"verdict": verdict, "cases": len(rows), "mutation_detected": mutation_detected}), flush=True)
    return 0 if verdict == "GAMMA_ROTATED_LAPLACE_AUX_PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
