"""One new auxiliary unfolding bank; prepare only until a separate root gate.

No prime detector, zeta evaluator, old bank, sieve, inversion, or Float is used.
This exercises a geometric integral, not the coefficient at N.
"""
import argparse
import ast
import json
from fractions import Fraction
from pathlib import Path
from interval22 import BITS, Box, set_sqrt_observer, sqrt_certificate_count


def H(u, a2):
    return Box.rational(u) / Box.rational(Fraction(u * u) + a2).sqrt()


def finite_direct(y, m, Q):
    a2 = (m * y) ** 2
    pref = (Box.rational(y) * Box.rational(y).sqrt()
            / Box.rational(m * a2))
    total = Box.rational(0)
    for n in range(-Q, Q + 1):
        total = total + pref * (H(n + m, a2) - H(n, a2))
    return total


def finite_endpoints(y, m, Q):
    q = abs(m)
    a2 = (q * y) ** 2
    pref = (Box.rational(y) * Box.rational(y).sqrt()
            / Box.rational(q * a2))
    positive = Box.rational(0)
    negative = Box.rational(0)
    for u in range(Q + 1, Q + q + 1):
        positive = positive + H(u, a2)
    for u in range(-Q, -Q + q):
        negative = negative + H(u, a2)
    return pref * (positive - negative)


def canonical_cases():
    result = []
    ms = (-7, -2, -1, 1, 2, 7)
    for tag, pair in (("half", [1, 2]), ("1", [1, 1]), ("2", [2, 1])):
        for m in ms:
            mt = "minus" + str(-m) if m < 0 else str(m)
            result.append({"id": "original_y" + tag + "_m" + mt,
                           "y": pair, "m": m, "Q": 4096,
                           "route": "all_shifts_and_endpoints"})
    for m in ms:
        mt = "minus" + str(-m) if m < 0 else str(m)
        result.append({"id": "scale_Y_m" + mt, "y": [10000, 1],
                       "m": m, "Q": 1048576,
                       "route": "endpoints_finite_telescope"})
    return result


def forbid_float_syntax():
    for name in ("interval22.py", "epstein_bank22.py"):
        path = Path(__file__).resolve().parent / name
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        if any(isinstance(node, ast.Constant) and isinstance(node.value, float)
               for node in ast.walk(tree)):
            raise RuntimeError("Float literal in source: " + name)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    contract = json.loads(Path(args.contract).read_text(encoding="utf-8"))
    forbid_float_syntax()
    fixed = {"bank_id": "EPSTEIN_UNFOLDING_AUX22", "N": 100000000,
             "Y": 10000, "precision_bits": 96,
             "cases_before_any_filter": 24,
             "original_cases_before_any_filter": 18,
             "scale_cases_before_any_filter": 6,
             "source_onset_satisfied": False,
             "coefficient_N_computed": False,
             "heat_signal_computed": False,
             "Weil_trace_computed": False,
             "D_N_bound_proved": False,
             "scope": "EPSTEIN_UNFOLDING_AUX_ONLY"}
    if any(contract.get(key) != value for key, value in fixed.items()):
        raise RuntimeError("fixed-contract guard mismatch")
    if BITS != 96 or contract["cases"] != canonical_cases():
        raise RuntimeError("canonical 24-case catalog mismatch")
    if contract["tolerance"] != [1, 100000] or contract["tail_cap"] != [1, 1000000]:
        raise RuntimeError("pre-frozen tolerance mismatch")
    tolerance = Fraction(1, 100000)
    tail_cap = Fraction(1, 1000000)
    records = []
    unresolved = False
    refuted = False
    certificate_path = Path(args.output).parent / "epstein_sqrt_certificates22.jsonl"
    certificate_stream = certificate_path.open("x", encoding="utf-8", newline="\n")
    active_case = {"id": None}
    def record_sqrt(certificate):
        certificate["case_id"] = active_case["id"]
        certificate_stream.write(json.dumps(certificate, sort_keys=True,
                                            separators=(",", ":")) + "\n")
    set_sqrt_observer(record_sqrt)
    # No cases are filtered before this loop: all 24 are mandatory.
    for case in contract["cases"]:
        active_case["id"] = case["id"]
        certificate_start = sqrt_certificate_count()
        y = Fraction(*case["y"])
        m, Q = case["m"], case["Q"]
        q = abs(m)
        if m == 0 or Q <= q or y <= 0:
            raise RuntimeError("unfolding guard failure")
        endpoint = finite_endpoints(y, m, Q)
        if case["route"] == "all_shifts_and_endpoints":
            direct = finite_direct(y, m, Q)
            finite_agrees = direct.intersects(endpoint)
            finite = direct
            individually_evaluated_shifts = 2 * Q + 1
        else:
            direct = None
            finite_agrees = None
            finite = endpoint
            individually_evaluated_shifts = 0
        tail = (Box.rational(y) * Box.rational(y).sqrt()
                / Box.rational((Q - q) ** 2))
        whole = finite.widen_upper(tail)
        target = Box.rational(2) / (Box.rational(q * q) * Box.rational(y).sqrt())
        compatible = whole.intersects(target)
        distance = whole.max_distance(target)
        width_ok = max(whole.width(), target.width(), distance) <= tolerance
        tail_ok = tail.upper() <= tail_cap
        if q > 1:
            mutation = target * Box.rational(q)
            mutation_detected = not whole.intersects(mutation)
        else:
            mutation, mutation_detected = None, None
        if not compatible or finite_agrees is False:
            refuted = True
        if (not width_ok or not tail_ok or
                (q > 1 and mutation_detected is not True)):
            unresolved = True
        records.append({
            **case, "represented_integer_shifts": 2 * Q + 1,
            "individually_evaluated_integer_shifts": individually_evaluated_shifts,
            "endpoint_terms_evaluated": 2 * q,
            "finite_direct": None if direct is None else direct.as_json(),
            "finite_endpoints": endpoint.as_json(),
            "finite_two_routes_intersect": finite_agrees,
            "tail_enclosure": tail.as_json(), "tail_cap_satisfied": tail_ok,
            "whole_line_enclosure": whole.as_json(),
            "target_enclosure": target.as_json(),
            "target_intersects": compatible,
            "max_distance": {"numerator": str(distance.numerator),
                             "denominator": str(distance.denominator)},
            "tolerance_satisfied": width_ok,
            "mutated_target": None if mutation is None else mutation.as_json(),
            "mutation_factor_abs_m_detected": mutation_detected,
            "integer_square_certificates": sqrt_certificate_count() - certificate_start
        })
        certificate_stream.flush()
        print(json.dumps({"completed_case": case["id"],
                          "scope": fixed["scope"], "compatible": compatible,
                          "tolerance_satisfied": width_ok}, sort_keys=True), flush=True)
    set_sqrt_observer(None)
    certificate_stream.close()
    if refuted:
        status, exit_code = "NUMERIC_COUNTEREXAMPLE_AUX", 1
    elif unresolved:
        status, exit_code = "UNRESOLVED_NON_INFORMATIVE", 2
    else:
        status, exit_code = "EPSTEIN_UNFOLDING_AUX_PASS", 0
    result = {"schema": "round22.epstein_unfolding_aux.result.v1",
              **fixed, "status": status, "Float": False,
              "cases": records, "actual_cases": len(records),
              "Lean_compiled": False, "new_D_N_estimate": False,
              "old_results_replayed": False,
              "sqrt_certificate_path": str(certificate_path),
              "integer_square_certificates": sqrt_certificate_count(),
              "interval_overlap_alone_is_never_FALSE": True,
              "certification_basis": "exact dyadic outward integer arithmetic; analytic primitive and tail are paper-audited, not Lean-certified"}
    with Path(args.output).open("x", encoding="utf-8", newline="\n") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print(json.dumps({"status": status, "scope": fixed["scope"]}, sort_keys=True), flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
