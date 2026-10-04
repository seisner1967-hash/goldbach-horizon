"""Independent structural/interval checker for a new component result.

Uses only integers/Fractions and emitted enclosures. Does not import the
producer, analytic evaluator, quadrature reference, or any historic output.
It independently checks catalogues, overlap/disjoint decisions, mutation
decisions, actual widths and the separation of auxiliary/global claims.
Analytic validity remains in the reviewed source/rest derivations, not in a
free status string or a self-comparison.
"""
from fractions import Fraction as F


def fraction(data):
    return F(int(data["numerator"]), int(data["denominator"]))


def box(data):
    denominator = int(data["denominator"])
    lo, hi = int(data["lo_integer"]), int(data["hi_integer"])
    if denominator != 1 << 512 or lo > hi:
        raise ValueError("invalid ground interval")
    return F(lo, denominator), F(hi, denominator)


def overlap(a, b):
    al, ah = box(a)
    bl, bh = box(b)
    return max(al, bl) <= min(ah, bh)


def complex_overlap(a, b):
    return overlap(a["real"], b["real"]) and overlap(a["imag"], b["imag"])


def width(a):
    rl, rh = box(a["real"])
    il, ih = box(a["imag"])
    return rh - rl + ih - il


def verify(result):
    errors = []
    cases = result["cases"]
    phase = [c for c in cases if c["kind"] == "COMPLEX_GAMMA_NEW_STIRLING_VS_NEW_INTEGRAL"]
    expected = {(sigma, gamma) for sigma in (F(1), F(3, 2), F(2))
                for gamma in (0, -3, 3, -23, 23)}
    actual = {(fraction(c["sigma"]), c["gamma"]) for c in phase}
    if len(cases) != 44 or len(phase) != 15 or actual != expected:
        errors.append("catalogue44/15 mismatch")
    for c in phase:
        cert = c["reference_certificate"]
        expected_cauchy = 70 * (1 << 13) * F(1, 16) ** 25 / (1 - F(1, 16))
        if (cert["cells"] != 2240 or cert["degree"] != 24
                or cert["Cauchy_M"] != 1 << 13
                or fraction(cert["Cauchy_radius"]) != F(1, 4)
                or fraction(cert["Cauchy_error"]) != expected_cauchy
                or fraction(cert["left_tail"]) != F(3, 8) ** 64
                or fraction(cert["right_tail"]) != 257 * F(1, 1 << 256)
                or cert["uses_Stirling"] or cert["uses_old_result"]):
            errors.append("Gamma reference closed budget mismatch")
        if c["phase_agreement"] != complex_overlap(c["evaluated"], c["reference"]):
            errors.append("Gamma complex agreement mismatch")
        if c["norm_agreement"] != overlap(c["norm_squared"], c["norm_reference"]):
            errors.append("Gamma norm agreement mismatch")
        if width(c["evaluated"]) > F(1, 1 << 81):
            errors.append("Gamma actual width guard mismatch")
        informative = fraction(c["reference_relative_width_upper"]) <= F(1, 1024)
        if c["phase_informative"] != informative:
            errors.append("Gamma reference informativeness decision mismatch")
        # A correctly reported wide reference is UNRESOLVED in the producer,
        # never a checker counterexample or a falsification of Gamma itself.
    for c in cases:
        kind = c["kind"]
        if kind.endswith("WIDTH_GUARD_ONLY"):
            if width(c["value"]) > F(1, 1 << 81):
                errors.append("actual domain width guard mismatch")
        elif kind == "EM_NEW_EXACT_CONSTANT":
            if c["agreement"] != complex_overlap(c["value"], c["reference"]):
                errors.append("EM special value decision mismatch")
            if fraction(c["s"]) == 0 and (c["derivative_agreement"] !=
                    complex_overlap(c["derivative"], c["derivative_reference"])):
                errors.append("EM derivative special value decision mismatch")
        elif kind.endswith("EXACT_POLYNOMIAL"):
            if c["agreement"] != complex_overlap(c["enclosure"], c["reference"]):
                errors.append("polynomial decision mismatch")
        elif kind.endswith("PAID_ALIAS_COUNTERTEST"):
            if c["alias_match"] != complex_overlap(c["actual"], c["alias_reference"]):
                errors.append("alias equality decision mismatch")
            if c["nonzero_error"] == complex_overlap(c["actual"], c["true_integral"]):
                errors.append("alias nonzero decision mismatch")
    # Every expected mutation has an emitted mutant and independent reference.
    if len(result["mutations"]) != 19:
        errors.append("mutation19 count mismatch")
    for c in result["mutations"]:
        if c["disjoint"] == complex_overlap(c["mutant"], c["correct"]):
            errors.append("mutation disjointness mismatch")
    for field in ("H1_numeric_claim", "H1_formal_claim", "coefficient_N_claim", "D_N_claim", "WIN"):
        if result[field] is not False:
            errors.append("auxiliary credit boundary violated:" + field)
    if result["old_bank_replays"] != 0:
        errors.append("old replay count nonzero")
    return {"scope": "THERMAL_COMPONENT_AUX_ONLY", "checker_errors": errors,
            "checker_PASS": not errors, "independent_interval_decisions": True,
            "imports_producer": False, "old_result_oracle": False,
            "H1_claim": False}
