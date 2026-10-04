"""NEW full composite20/13.12 bank, executable only through its reviewed unique launcher."""
from __future__ import annotations

from bisect import bisect_left, bisect_right
from fractions import Fraction
import json
from math import gcd, prod, lcm
from pathlib import Path

from arithmetic import (N, LEFT, RIGHT, A, ALPHA, Q_ORIGINAL, M, H, ceildiv, sieve,
                        segment, factor, frac, add_map, map_json, properpowers, actual_weights)
from outward import (LogOracle, SCALE, iv_json, add, neg, scale, mul,
                     absolute_upper)
from storage import JsonCatalog, binary_catalog, file_info
from ap import TemplateBank, FiniteAP, candidate_cells
from reference import evaluate_reference
from integral import monotone_integral20
from certify import StrictCertificates

ROOT = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
OWN = ROOT / "round20" / "role6_composite"
OUT = OWN / "canonical_attempt01"
RESULT = ROOT / "round20" / "composite.json"
SN = Fraction(2541, 1536), Fraction(11011, 6144)
CONFIGS = [("SOURCE_z2_P1_K1", 2, 1, 1),
           ("TEST_z11_P17_K0", 11, 17, 0), ("TEST_z11_P17_K1", 11, 17, 1),
           ("TEST_z19_P17_K0", 19, 17, 0), ("TEST_z19_P17_K1", 19, 17, 1)]


def progress(stage, **values):
    print(json.dumps({"stage": stage, **values}, sort_keys=True), flush=True)


class Affine:
    def __init__(self, oracle):
        self.oracle = oracle
        self.intercept = Fraction(0), Fraction(0)
        self.slope = Fraction(0), Fraction(0)
        self.terms = []
        self.literal_zero_terms = 0

    def append(self, c, quantity, reference, multiplier=1):
        quantity = scale(quantity, multiplier)
        if quantity == (0, 0):
            self.literal_zero_terms += 1
            return
        self.intercept = add(self.intercept, mul(self.oracle.log(c), quantity))
        self.slope = add(self.slope, quantity)
        self.terms.append({"c": c, "quantity_ref": reference, "multiplier": frac(multiplier)})

    def enclosure(self):
        return add(self.intercept, mul(SN, self.slope))

    def data(self, kind="ACTUAL_EXACT_AFFINE_MAPS"):
        enclosure = self.enclosure()
        certificate = iv_json(enclosure)
        if certificate["sign"] == "UNRESOLVED_SIGN_INTERVAL":
            certificate["sign"] = ("PRINCIPAL_INTEGRAL_COMPARISON_NOT_DECIDED"
                                   if "PRINCIPAL" in kind else "PARAMETER_BOX_NOT_SIGN_DETERMINED")
        return {"kind": kind, "S_N_acquired_box": [frac(v) for v in SN],
                "intercept_interval": iv_json(self.intercept), "slope_interval": iv_json(self.slope),
                "whole_box_certificate": certificate, "all_exact_affine_terms": self.terms,
                "literal_zero_terms_already_retained_in_full_position_catalogs": self.literal_zero_terms,
                "S_N_not_evaluated_for_free": True}


def difference(oracle, left, right):
    target = Affine(oracle)
    target.intercept = add(left.intercept, neg(right.intercept))
    target.slope = add(left.slope, neg(right.slope))
    target.terms = left.terms + [{**term, "multiplier": frac(-Fraction(term["multiplier"]))}
                                for term in right.terms]
    target.literal_zero_terms = left.literal_zero_terms + right.literal_zero_terms
    return target


def p0_actual(primes):
    return next(p for p in primes if p != 2 and N % p)


def physical_guard(c, r, s, q, t, j, prime_set):
    b = s * q
    guards = {"c_prime": c in prime_set, "r_prime": r in prime_set,
              "s_prime": s in prime_set, "q_prime": q in prime_set,
              "c_lt_r": c < r, "r_lt_s": r < s, "s_le_a": s <= A,
              "a_lt_q": A < q, "cr_le_a": c * r <= A, "cs_le_a": c * s <= A,
              "a_lt_rs": A < r * s, "rs_lt_q": r * s < q,
              "a_lt_crs": A < t, "b_eq_s_times_q": b == s * q,
              "unit_m": gcd(c * r * b, N) == 1, "bulk": M <= c * r * b,
              "original_front": c * r * b + Q_ORIGINAL < N,
              "j_eq_N_minus_tq": j == N - t * q, "new_window": LEFT < j <= RIGHT,
              "j_unit_N": gcd(j, N) == 1, "j_unit_t": gcd(j, t) == 1}
    assert all(guards.values())
    return guards


def coefficient_maps(candidates, template, P, K, falsifiers, cfg_name):
    weights = template["weights"]["lambdas"]
    maps = {name: {} for name in ("Ttheta", "Traw", "PPbeta", "Q", "Ctrue", "Clow", "Cminus", "Ctail", "slack")}
    per_candidate = []
    for row in candidates:
        j = row["j"]
        amplitude = sum((value for k, value in weights.items() if j % k == 0), Fraction(0))
        weight = amplitude * amplitude
        assert weight >= 0
        if weight:
            maps["Q"][j] = weight
        if row["prime"]:
            assert amplitude == 1 and weight == 1 and j > template["weights"]["z"]
            maps["Ttheta"][j] = Fraction(1)
            maps["Traw"][j] = Fraction(1)
        else:
            if weight:
                maps["Ctrue"][j] = weight
                destination = "Clow" if row["minFac"] <= P else "Ctail"
                maps[destination][j] = weight
                if destination == "Ctail":
                    falsifiers.setdefault("delete_true_composite_tail", {}).setdefault(cfg_name, {
                        "candidate_ref": row["id"], "j": j, "minimum": row["minFac"], "cut": P,
                        "weight": frac(weight), "status": "ACTUAL_NONZERO_TAIL_RETAINED"})
            if row["properpower"]:
                base, exponent = row["factors"][0]
                maps["PPbeta"][base] = maps["PPbeta"].get(base, Fraction(0)) + 1
                maps["Traw"][base] = maps["Traw"].get(base, Fraction(0)) + 1
                falsifiers.setdefault("forget_raw_properpowers", {"candidate_ref": row["id"], "j": j,
                                      "base": base, "exponent": exponent, "mu_squared_zero_raw_nonzero": True})
                if weight:
                    falsifiers.setdefault("replace_weight_logj_by_logbase", {"candidate_ref": row["id"],
                                          "j": j, "base": base, "exponent": exponent,
                                          "lambda_square": frac(weight), "logj_equals_exponent_logbase": True})
        cell_records = []
        lower_coefficient = 0
        for cell in row["cells"]:
            if cell["p"] > P:
                continue
            Lvalue = cell["L_K0_K1"][str(K)]
            catalog = template["lower"][cell["p"]]
            actual_L = sum(xi for h, xi in catalog["active"] if cell["v"] % h == 0)
            assert actual_L == Lvalue
            assert cell["rough_indicator"] - Lvalue >= 0
            lower_coefficient += Lvalue
            cell_records.append({"p": cell["p"], "L": Lvalue,
                                 "rough_minus_L": cell["rough_indicator"] - Lvalue,
                                 "nonminimum": not cell["actual_minimum"],
                                 "weight": frac(weight), "weighted_L": frac(weight * Lvalue)})
            if Lvalue < 0:
                falsifiers.setdefault("force_L_positive", {}).setdefault(cfg_name, {
                    "candidate_ref": row["id"], "j": j, "p": cell["p"], "v": cell["v"],
                    "r": cell["r"], "L": Lvalue})
                if weight and not cell["actual_minimum"]:
                    falsifiers.setdefault("keep_only_minimum_p_in_Cminus", {}).setdefault(cfg_name, {
                        "candidate_ref": row["id"], "j": j, "p": cell["p"], "minimum": row["minFac"],
                        "weighted_nonminimum_negative": frac(weight * Lvalue)})
        lower_weight = weight * lower_coefficient
        if lower_weight:
            maps["Cminus"][j] = lower_weight
        slack = (weight if not row["prime"] and row["minFac"] <= P else Fraction(0)) - lower_weight
        assert slack >= 0
        if slack:
            maps["slack"][j] = slack
        per_candidate.append({"candidate_ref": row["id"], "sum_lambda_divisors": frac(amplitude),
                              "lambda_square": frac(weight), "lambda_square_exact_sign": "ZERO" if weight == 0 else "POS",
                              "log_weight_basis": j,
                              "developed_cells_all_within_cut": cell_records, "slack": frac(slack),
                              "true_minimum_in_low": not row["prime"] and row["minFac"] <= P,
                              "true_minimum_in_tail": not row["prime"] and row["minFac"] > P})
    identity = {}
    add_map(identity, maps["Q"])
    add_map(identity, maps["Ctrue"], -1)
    add_map(identity, maps["Ttheta"], -1)
    assert identity == {}
    add_map(identity, maps["Clow"])
    add_map(identity, maps["Cminus"], -1)
    add_map(identity, maps["slack"], -1)
    assert identity == {}
    add_map(identity, maps["Ctrue"])
    add_map(identity, maps["Clow"], -1)
    add_map(identity, maps["Ctail"], -1)
    assert identity == {}
    add_map(identity, maps["Traw"])
    add_map(identity, maps["Ttheta"], -1)
    add_map(identity, maps["PPbeta"], -1)
    assert identity == {}
    assert all(value >= 0 for value in maps["slack"].values())
    return maps, per_candidate


def ap_instance(c, t, qlo, qhi, candidates, template, P, oracle, finite_AP, templates,
                integral_cache, instance_store, falsifiers, cfg_name, p0, empty_class_store, empty_class_cache, integral_store, strict):
    Y = Fraction(N, t)
    if qlo > qhi:
        assert candidates == []
        caps = {p: min(qhi, (N - p * p) // t) for p in template["lower"]}
        assert all(cap == qhi for cap in caps.values())
        modules = set(template["q_original_counts"]) | {nu for p, nu in template["c_original_counts"]}
        # The independently recorded p0 layer exists even outside the source cut P=1.
        modules |= {lcm(p0, nu) for nu in template["q_original_counts"]}
        refs = []
        for nu in sorted(modules):
            if nu not in empty_class_cache:
                common = gcd(nu, t * N)
                compatible = common == 1
                residue = (N * pow(t, -1, nu)) % nu if compatible else None
                if compatible:
                    assert gcd(residue, nu) == 1 and (t * residue - N) % nu == 0
                position = empty_class_store.put({"t": t, "nu": nu, "class_reduced": residue,
                    "compatible_tN": compatible, "gcd_nu_tN": common,
                    "incompatible_reason": None if compatible else "shared_t_unsatisfiable_or_nonunit_N_class",
                    "every_original_coefficient_and_representation_ref_in_template": True,
                    "integer_window": [qlo, qhi], "literal_empty_window": True,
                    "Y": frac(Y), "module_greater_than_Y": nu > Y,
                    "actual_principal_remainder_exact_ZERO": True,
                    "finite_class_error_not_used_for_empty_interval": True})
                empty_class_cache[nu] = position
            refs.append([nu, empty_class_cache[nu]])
        coefficient_p0 = template["weights"]["Q"] / (p0 - 1) if t % p0 else Fraction(0)
        assert min(qhi, (N - p0 * p0) // t) == qhi
        zero_certificate = strict.interval(["AP_empty_instance", instance_store.count, cfg_name, t],
            (Fraction(0), Fraction(0)), exact_zero=True,
            exact_expression={"window": [qlo, qhi], "all_windows_and_members_empty": True,
                              "template_ref": template["id"], "all_class_refs": refs})
        position = instance_store.put({"config": cfg_name, "c": c, "t": t, "Y": frac(Y),
            "template_ref": template["id"], "all_original_coefficients_concrete_template_headers": True,
            "all_original_expanded_k_l_h_positions": [template["header"]["representation_first_index"],
                                                       template["header"]["representation_end_exclusive"]],
            "all_reduced_module_classes_concrete_refs": refs, "J_t": [qlo, qhi],
            "p_squared_caps_all": [[p, (N - p * p) // t, cap] for p, cap in sorted(caps.items())],
            "all_literal_windows_agree_verified": True,
            "all_signed_coefficients_ref": ["template", template["id"], "signed_coefficients_grouped_when_literal_windows_agree"],
            "all_members_maps_integrals_principals_remainders_literal_ZERO": True,
            "strict_shared_ZERO_certificate": zero_certificate,
            "integral_mesh": {"empty": True, "qlo": qlo, "qhi": qhi, "pieces": 0},
            "fronts_qlo_minus1_qhi": [qlo - 1, qhi], "empty_integer_window": True,
            "p0_layer_recorded_separately_even_when_p0_above_cut": {"p0": p0, "p0_divides_t": t % p0 == 0,
                "coefficient": frac(coefficient_p0), "principal_actual_remainder": "ZERO",
                "p0_squared_cap_floor": (N - p0 * p0) // t, "p0_cap_preserves_full_empty_window": True,
                "finite_G_comparison_ref": ["template", template["id"]],
                "ideal_G_exclusion_and_retention_factor": frac(Fraction(p0 - 2, p0 - 1)) if t % p0 else "1/1",
                "ideal_inflation_times_removal_exact1": True},
            "all_original_zero_coefficients_retained": True, "no_triple_domain_reduction": True,
            "not_global_Etheta_or_BV": True})
        zero = Fraction(0), Fraction(0)
        return {"position": position, "Q_map": {}, "Cminus_map": {}, "principalQ": zero,
                "principalCminus": zero, "principalSigned": zero, "RAP": zero, "p0Principal": zero, "p0RAP": zero,
                "group_count": len(template["header"]["signed_coefficients_grouped_when_literal_windows_agree"]),
                "component_count": len(template["q_original_counts"]) + len(template["c_original_counts"]),
                "max_representations": max(row[2] for row in template["header"]["signed_coefficients_grouped_when_literal_windows_agree"])}
    if (t, qlo, qhi) not in integral_cache:
        integral_cache[(t, qlo, qhi)] = monotone_integral20(oracle, t, qlo, qhi, integral_store)
    full_integral, full_mesh = integral_cache[(t, qlo, qhi)]
    # First preserve Q and each composite layer separately; only then group
    # the signed coefficients by literal (window,nu), before absolute values.
    components = []
    for nu, count in template["q_original_counts"].items():
        components.append(("Q", None, qlo, qhi, nu,
                           template["q_groups"].get(nu, Fraction(0)), count))
    for (p, nu), count in template["c_original_counts"].items():
        capped_hi = min(qhi, (N - p * p) // t)
        components.append(("Cminus", p, qlo, capped_hi, nu,
                           template["c_groups"].get((p, nu), Fraction(0)), count))
    grouped = {}
    representations = {}
    component_records = []
    member_cache = {}
    Q_actual = {}
    C_actual = {}
    mainQ = (Fraction(0), Fraction(0))
    mainC = (Fraction(0), Fraction(0))
    mainp0 = (Fraction(0), Fraction(0))
    Cp0_coefficient = Fraction(0)
    p0_actual_map = {}
    for kind, p, low, high, nu, coefficient, count in components:
        compatible = gcd(nu, t * N) == 1
        residue = (N * pow(t, -1, nu)) % nu if compatible else None
        if compatible:
            assert gcd(residue, nu) == 1 and (t * residue - N) % nu == 0
        key = (low, high, nu)
        if key not in member_cache:
            members = [row for row in candidates if low <= row["q"] <= high and row["j"] % nu == 0]
            if compatible:
                by_class = [row for row in candidates if low <= row["q"] <= high and row["q"] % nu == residue]
                assert [row["id"] for row in members] == [row["id"] for row in by_class]
            else:
                assert members == []
            member_cache[key] = members
        else:
            members = member_cache[key]
        if (t, low, high) not in integral_cache:
            integral_cache[(t, low, high)] = monotone_integral20(oracle, t, low, high, integral_store)
        integral, mesh = integral_cache[(t, low, high)]
        component_main = scale(integral, coefficient / templates.totient(nu)) if compatible else (Fraction(0), Fraction(0))
        actual_map = {row["j"]: coefficient for row in members if coefficient}
        component_actual, component_cert = strict.vector(["AP_component", instance_store.count, cfg_name, t, kind, p, nu], actual_map)
        add_map(Q_actual if kind == "Q" else C_actual, actual_map)
        if kind == "Q":
            mainQ = add(mainQ, component_main)
        else:
            mainC = add(mainC, component_main)
            if p == p0:
                mainp0 = add(mainp0, component_main)
                add_map(p0_actual_map, actual_map)
                if compatible:
                    assert (low, high) == (qlo, qhi) or qlo > qhi
                    Cp0_coefficient += coefficient / templates.totient(nu)
        sign = 1 if kind == "Q" else -1
        grouped[key] = grouped.get(key, Fraction(0)) + sign * coefficient
        representations[key] = representations.get(key, 0) + count
        component_records.append({"kind": kind, "p": p, "nu": nu, "class": residue,
                                  "compatible_tN": compatible, "gcd_nu_tN": gcd(nu, t * N),
                                  "incompatible_reason": None if compatible else "shared_t_unsatisfiable_or_nonunit_N_class",
                                  "window": [low, high], "empty_window": low > high,
                                  "p_squared_cap_floor": (N - p * p) // t if p is not None else None,
                                  "plus1_fronts": {"left_endpoint": low - 1, "right_endpoint": high},
                                  "original_representation_count": count, "coefficient": frac(coefficient),
                                  "zero_coefficient_retained": coefficient == 0,
                                  "members_all_physical_q_refs_before_jprime_filter": [row["id"] for row in members],
                                  "actual_logj_map": map_json(actual_map),
                                  "actual_fixed_log_map_certificate": component_cert,
                                  "actual_interval": iv_json(component_actual),
                                  "integral_mesh": mesh, "principal": iv_json(component_main),
                                  "module_greater_than_Y": nu > Y,
                                  "module_greater_than_sqrtY": nu * nu > Y})
    if t % p0 == 0:
        assert mainp0 == (0, 0) and p0_actual_map == {} and Cp0_coefficient == 0
    else:
        assert template["lower"].get(p0, {"eligible_primes": []})["eligible_primes"] == []
        if p0 <= P:
            assert Cp0_coefficient == template["weights"]["Q"] / (p0 - 1)
            expected_p0 = {row["j"]: sum((v for k, v in template["weights"]["lambdas"].items()
                                        if row["j"] % k == 0), Fraction(0)) ** 2
                           for row in candidates if row["j"] % p0 == 0}
            expected_p0 = {j: v for j, v in expected_p0.items() if v}
            assert expected_p0 == p0_actual_map
    independent_p0_records = []
    independent_p0_map = {}
    independent_p0_coefficient = Fraction(0)
    independent_p0_RAP = (Fraction(0), Fraction(0))
    for K0, count in sorted(template["q_original_counts"].items()):
        nu = lcm(p0, K0)
        coefficient = template["q_groups"].get(K0, Fraction(0))
        compatible = gcd(nu, t * N) == 1
        residue = (N * pow(t, -1, nu)) % nu if compatible else None
        if compatible:
            assert gcd(residue, nu) == 1 and (t * residue - N) % nu == 0
        members = [row for row in candidates if row["j"] % nu == 0]
        if not compatible:
            assert members == []
        else:
            assert [row["id"] for row in members] == [row["id"] for row in candidates if row["q"] % nu == residue]
        if coefficient:
            assert K0 % p0 and templates.totient(nu) == (p0 - 1) * templates.totient(K0)
        actual_map = {row["j"]: coefficient for row in members if coefficient}
        add_map(independent_p0_map, actual_map)
        principal = scale(full_integral, coefficient / templates.totient(nu)) if compatible else (Fraction(0), Fraction(0))
        if compatible:
            independent_p0_coefficient += coefficient / templates.totient(nu)
        p0_actual_interval, p0_cert = strict.vector(["AP_p0_independent", instance_store.count, cfg_name, t, K0, nu], actual_map)
        remainder = add(p0_actual_interval, neg(principal))
        R = (Fraction(0), Fraction(0))
        query = None
        if compatible and coefficient:
            query = finite_AP.query(nu, residue, Y, qlo, qhi)
            R = scale(add(query["E"], oracle.log(N)), 6 * abs(coefficient))
            assert absolute_upper(remainder) <= R[0]
            independent_p0_RAP = add(independent_p0_RAP, R)
        independent_p0_records.append({"K0": K0, "Kp0": K0 // gcd(K0, p0),
            "nu": nu, "nu_equals_p0_times_Kp0": nu == p0 * (K0 // gcd(K0, p0)),
            "coefficient": frac(coefficient),
            "all_original_k_l_count": count, "zero_originals_retained": coefficient == 0,
            "window": [qlo, qhi], "p0_squared_cap": (N - p0 * p0) // t,
            "full_window_guard_actual": p0 * p0 < LEFT + 1,
            "class_reduced": residue, "compatible": compatible,
            "removed_q_dividing_N": [q for q in (2, 5) if qlo <= q <= qhi and compatible and q % nu == residue],
            "actual_logj_map": map_json(actual_map), "principal": iv_json(principal),
            "actual_fixed_log_map_certificate": p0_cert,
            "remainder": iv_json(remainder), "finite_AP_query_ref": query["query_ref"] if query else None,
            "finite_class_error_bound": iv_json(R), "separate_from_Cminus_if_p0_above_cut": p0 > P})
    if t % p0 == 0:
        assert independent_p0_coefficient == 0 and independent_p0_map == {}
    else:
        assert independent_p0_coefficient == template["weights"]["Q"] / (p0 - 1)
        if p0 <= P:
            assert independent_p0_map == p0_actual_map
    mainp0 = scale(full_integral, independent_p0_coefficient)
    Cp0_coefficient = independent_p0_coefficient
    p0_actual_map = independent_p0_map
    grouped_records = []
    signed_actual = {}
    signed_principal = (Fraction(0), Fraction(0))
    RAP_scalar = (Fraction(0), Fraction(0))
    max_representations = 0
    for (low, high, nu), coefficient in sorted(grouped.items()):
        compatible = gcd(nu, t * N) == 1
        residue = (N * pow(t, -1, nu)) % nu if compatible else None
        members = member_cache[(low, high, nu)]
        actual_map = {row["j"]: coefficient for row in members if coefficient}
        add_map(signed_actual, actual_map)
        integral, mesh = integral_cache[(t, low, high)]
        principal = scale(integral, coefficient / templates.totient(nu)) if compatible else (Fraction(0), Fraction(0))
        signed_principal = add(signed_principal, principal)
        actual, actual_cert = strict.vector(["AP_signed_group", instance_store.count, cfg_name, t, low, high, nu], actual_map)
        remainder = add(actual, neg(principal))
        finite_info = None
        R_bound = (Fraction(0), Fraction(0))
        exceptions = []
        if compatible and low <= high and coefficient:
            finite_info = finite_AP.query(nu, residue, Y, low, high)
            E = finite_info["E"]
            unit_removed_q = [q for q in (2, 5) if low <= q <= high and q % nu == residue]
            exceptions = [{"q": q, "logq": iv_json(oracle.log(q)),
                           "weighted_logj": iv_json(oracle.log(N - t * q))} for q in unit_removed_q]
            assert unit_removed_q == []  # Actual endpoint low>a, retained explicitly, never preassumed.
            single_bound = scale(add(E, oracle.log(N)), 6)
            R_bound = scale(single_bound, abs(coefficient))
            assert absolute_upper(remainder) <= R_bound[0]
            RAP_scalar = add(RAP_scalar, R_bound)
        if coefficient and nu > Y:
            falsifiers.setdefault("delete_modules_greater_than_Y", {}).setdefault(cfg_name, {
                "t": t, "nu": nu, "Y": frac(Y), "class": residue, "coefficient": frac(coefficient),
                "compatible": compatible, "principal": iv_json(principal), "remainder": iv_json(remainder),
                "status": "PRINCIPAL_AND_REMAINDER_RETAINED"})
        max_representations = max(max_representations, representations[(low, high, nu)])
        grouped_records.append({"window": [low, high], "nu": nu, "class": residue,
                                "signed_grouped_coefficient_before_abs": frac(coefficient),
                                "all_original_representation_count": representations[(low, high, nu)],
                                "actual_logj_map": map_json(actual_map), "actual_interval": iv_json(actual),
                                "actual_fixed_log_map_certificate": actual_cert,
                                "principal_interval": iv_json(principal), "remainder_actual_minus_principal": iv_json(remainder),
                                "finite_profile_query_ref": finite_info["query_ref"] if finite_info else None,
                                "finite_class_RAP_bound": iv_json(R_bound), "removed_q_dividing_N": exceptions,
                                "empty_window": low > high, "compatible": compatible,
                                "module_greater_than_Y": nu > Y, "no_old_multiplicity_cap": True})
    check = {}
    add_map(check, Q_actual)
    add_map(check, C_actual, -1)
    assert signed_actual == check
    if t % p0:
        euler_exclusion_G_factor = Fraction(p0 - 2, p0 - 1)
        removed_principal_factor = 1 - Fraction(1, p0 - 1)
        assert removed_principal_factor / euler_exclusion_G_factor == 1
        unrestricted = actual_weights(template["weights"]["z"], t, 1, templates.primes)
        finite_comparison = {"G_with_p0_admitted_finite": frac(unrestricted["G"]),
                             "G_with_p0_excluded_finite": frac(template["weights"]["G"]),
                             "finite_G_ratio_not_forced_to_Euler_asymptotic": True}
    else:
        euler_exclusion_G_factor = Fraction(1)
        removed_principal_factor = Fraction(1)
        finite_comparison = {"branch_zero_p0_divides_t": True}
    position = instance_store.put({"config": cfg_name, "c": c, "t": t, "template_ref": template["id"],
                                   "Y": frac(Y), "J_t": [qlo, qhi], "full_integral": iv_json(full_integral),
                                   "full_integral_mesh": full_mesh, "all_original_module_components": component_records,
                                   "all_signed_groups_before_abs": grouped_records,
                                   "max_observed_original_representations": max_representations,
                                   "principal_Q": iv_json(mainQ), "principal_Cminus": iv_json(mainC),
                                   "signed_principal_grouped": iv_json(signed_principal),
                                   "RAP_finite_class_scalar": iv_json(RAP_scalar),
                                   "p0_actual_positive_layer": {"p0": p0, "p0_divides_t": t % p0 == 0,
                                       "principal": iv_json(mainp0), "actual_logj_map": map_json(p0_actual_map),
                                       "coefficient": frac(Cp0_coefficient),
                                       "all_independent_p0_components": independent_p0_records,
                                       "finite_p0_RAP": iv_json(independent_p0_RAP),
                                       "p0_above_Cminus_cut_separate": p0 > P,
                                       "Euler_G_exclusion_factor": frac(euler_exclusion_G_factor),
                                       "retained_principal_factor": frac(removed_principal_factor),
                                       "ideal_inflation_times_removal_exact1": True, **finite_comparison},
                                   "B6_analytic_Lean_not_claimed": True,
                                   "exact_actual_equals_principal_plus_defined_remainder": True,
                                   "source_global_Etheta_not_replaced_by_finite_class": True})
    return {"position": position, "Q_map": Q_actual, "Cminus_map": C_actual,
            "principalQ": mainQ, "principalCminus": mainC,
            "principalSigned": signed_principal, "RAP": RAP_scalar, "p0Principal": mainp0, "p0RAP": independent_p0_RAP,
            "group_count": len(grouped_records), "component_count": len(component_records),
            "max_representations": max_representations}


def run():
    assert OUT.is_dir() and not RESULT.exists()
    parameter_certificates = {"alpha_integer": ALPHA ** 4 <= N < (ALPHA + 1) ** 4,
                              "a_integer_ceil": (A - 1) ** 16 < N ** 7 <= A ** 16,
                              "M_integer_ceil": (M - 1) ** 4 < N ** 3 <= M ** 4,
                              "Q_literal": Q_ORIGINAL == N // ALPHA - 1,
                              "z_source_integer_ceil2": 1 ** 64 < N <= 2 ** 64,
                              "P_source_integer_floor1": 1 ** 64 <= N < 2 ** 64,
                              "sqrt_bitmap_divisor_bound": 6928 ** 2 < RIGHT <= 6929 ** 2}
    assert all(parameter_certificates.values())
    oracle = LogOracle(OUT / "primitive_log_enclosures.jsonl.gz")
    u_initial = oracle.log(N)
    assert u_initial[1] < 10 ** 24
    names = ["physical_candidates", "physical_triples", "expanded_AP_representations", "AP_instances", "empty_AP_classes",
             "finite_AP_profiles", "finite_AP_queries", "integral_certificates", "identity_maps_and_weights", "reference_fibres", "certificates"]
    stores = {name: JsonCatalog(OUT / f"{name}.jsonl.gz") for name in names}
    primes, small_flags = sieve(11000)
    prime_set = set(primes)
    p0 = p0_actual(primes)
    assert p0 == 3 and all(N % p == 0 for p in primes if p < p0 and p != 2)
    segment_flags = segment(primes)
    assert len(segment_flags) == RIGHT - LEFT
    total_prime = total_unit = 0
    for offset in range(len(segment_flags)):
        j = LEFT + 1 + offset
        prime = int(segment_flags[offset])
        unit = int(j % 2 != 0 and j % 5 != 0)
        segment_flags[offset] = prime | (unit << 1)
        total_prime += prime
        total_unit += unit
    bitmap = binary_catalog(OUT / "all_24000000_candidate_axes.bin.gz", segment_flags,
                            {"first": LEFT + 1, "last": RIGHT, "count": RIGHT - LEFT,
                             "one_byte_each_integer_before_all_masks": True,
                             "bits": ["prime", "unit_N"], "factor_primes_full_through": 11000,
                             "ceil_sqrt_RIGHT": 6929, "completeness_square_divisor_sieve": True})
    pp = properpowers(primes)
    properpower_catalog = [{"j": j, "base_prime": p, "exponent": exponent,
                            "unit_N": gcd(j, N) == 1, "theta_zero": True,
                            "raw_logbase_not_logj": True} for j, (p, exponent) in pp.items()]
    small_info = binary_catalog(OUT / "new_primes_0through11000.bin.gz", small_flags,
                               {"first": 0, "last": 11000, "all_integer_axes": True})
    templates = TemplateBank(primes, stores["expanded_AP_representations"])
    strict = StrictCertificates(primes, oracle, stores["certificates"])
    finite_AP = FiniteAP(primes, oracle, stores["finite_AP_profiles"], stores["finite_AP_queries"], templates, strict)
    aggregates = {cfg: {name: Affine(oracle) for name in ("Ttheta", "Traw", "PPbeta", "Q", "Ctrue", "Clow", "Cminus", "Ctail", "slack",
                                                               "principalQ", "principalCminus", "principalSigned", "RAP", "p0Principal", "p0RAP")}
                  for cfg, z, P, K in CONFIGS}
    falsifiers = {}
    integral_cache = {}
    pairs = []
    beta_by_pair = {}
    triples_summary = []
    t_seen = set()
    counts = {"pairs": 0, "triples": 0, "empty_integer_windows": 0,
              "empty_prime_windows": 0, "physical_q": 0, "prime_j": 0,
              "composite_j": 0, "properpower_j": 0, "AP_components": 0, "AP_groups": 0,
              "reference_b_axes": 0, "reference_theta_axes": 0, "reference_PP_axes": 0}
    progress("NEW_FULL_BITMAP_COMPLETE", integer_axes=len(segment_flags), prime_axes=total_prime,
             unit_axes=total_unit, p0=p0, properpowers=len(pp))
    unit_small_primes = [p for p in primes if p <= A and gcd(p, N) == 1]
    for ic, c in enumerate(unit_small_primes):
        for r in unit_small_primes[ic + 1:]:
            d = c * r
            if d > A:
                break
            pairs.append((c, r, d))
            beta_by_pair[d] = set()
            counts["pairs"] += 1
            for s in unit_small_primes:
                if s <= r:
                    continue
                if c * s > A:
                    break
                t = d * s
                if r * s <= A or t <= A:
                    continue
                assert gcd(t, N) == 1 and t not in t_seen
                t_seen.add(t)
                low = max(A + 1, r * s + 1, ceildiv(N - RIGHT, t), ceildiv(M, t))
                high = min(ceildiv(N - LEFT, t) - 1, (N - Q_ORIGINAL - 1) // t)
                assert high < 11000
                qs = [q for q in primes[bisect_left(primes, low):bisect_right(primes, high)] if gcd(q, N) == 1] if low <= high else []
                candidates = []
                first_candidate = stores["physical_candidates"].count
                for q in qs:
                    j = N - t * q
                    guards = physical_guard(c, r, s, q, t, j, prime_set)
                    assert factor(t * q, primes) == [(c, 1), (r, 1), (s, 1), (q, 1)]
                    pf = factor(j, primes)
                    prime = len(pf) == 1 and pf[0][1] == 1
                    properpower = len(pf) == 1 and pf[0][1] > 1
                    assert bool(segment_flags[j - LEFT - 1] & 1) == prime
                    assert (j in pp) == properpower
                    cells = candidate_cells(pf, j, t, 17, primes)
                    row = {"c": c, "r": r, "s": s, "q": q, "d": d, "t": t,
                           "b": s * q, "j": j, "physical_witness18_all_guards": guards,
                           "factorization_m": [[c, 1], [r, 1], [s, 1], [q, 1]],
                           "factors": pf, "minFac": pf[0][0], "prime": prime,
                           "composite": not prime, "properpower": properpower,
                           "squarefree_j": all(exponent == 1 for p, exponent in pf),
                           "cells": cells, "q_primality_checked_before_j_primality": True}
                    row["id"] = stores["physical_candidates"].count
                    stores["physical_candidates"].put(row)
                    candidates.append(row)
                    assert row["b"] not in beta_by_pair[d]
                    beta_by_pair[d].add(row["b"])
                    counts["physical_q"] += 1
                    counts["prime_j" if prime else "composite_j"] += 1
                    counts["properpower_j"] += properpower
                    if not prime and pf[0][1] >= 2:
                        witness = {"candidate_ref": row["id"], "j": j, "minimum": pf[0][0],
                                   "v": j // pf[0][0], "gcd_p_v": pf[0][0], "rough_ge_p_true": True}
                        falsifiers.setdefault("replace_rough_ge_by_strict_gt", witness)
                        falsifiers.setdefault("impose_gcd_p_v_equal1", witness)
                counts["triples"] += 1
                counts["empty_integer_windows"] += low > high
                counts["empty_prime_windows"] += not qs
                triple = {"id": len(triples_summary), "c": c, "r": r, "s": s, "d": d, "t": t,
                          "qlo": low, "qhi": high, "all_q_prime_unit": qs,
                          "candidate_first_ref": first_candidate, "candidate_end_ref": stores["physical_candidates"].count,
                          "integer_window_empty": low > high, "prime_window_empty": not qs,
                          "literal_qlo_components": [A + 1, r * s + 1, ceildiv(N - RIGHT, t), ceildiv(M, t)],
                          "literal_qhi_components": [ceildiv(N - LEFT, t) - 1, (N - Q_ORIGINAL - 1) // t],
                          "fronts_qlo_minus1_qhi": [low - 1, high], "config_refs": []}
                empty_class_cache = {}
                for cfg, z, P, K in CONFIGS:
                    template = templates.get(z, P, K, t, p0)
                    maps, weights = coefficient_maps(candidates, template, P, K, falsifiers, cfg)
                    ap = ap_instance(c, t, low, high, candidates, template, P, oracle, finite_AP,
                                     templates, integral_cache, stores["AP_instances"], falsifiers, cfg, p0,
                                     stores["empty_AP_classes"], empty_class_cache, stores["integral_certificates"], strict)
                    assert ap["Q_map"] == maps["Q"] and ap["Cminus_map"] == maps["Cminus"]
                    intervals = {}
                    fixed_certificates = {}
                    for name, vector in maps.items():
                        intervals[name], fixed_certificates[name] = strict.vector(
                            ["physical_triple_map", triple["id"], cfg, name], vector)
                    config_position = stores["identity_maps_and_weights"].put({
                        "config": cfg, "triple_ref": triple["id"], "c": c, "t": t,
                        "template_ref": template["id"], "AP_instance_ref": ap["position"],
                        "all_physical_q_weight_records": weights,
                        "exact_rational_logj_maps_before_log_evaluation": {name: map_json(vector) for name, vector in maps.items()},
                        "strict_or_declared_box_certificates": {name: iv_json(value) for name, value in intervals.items()},
                        "strict_fixed_log_map_certificates": fixed_certificates,
                        "B1_Q_minus_Ctrue_equals_Ttheta": True,
                        "B3_Clow_minus_Cminus_equals_nonnegative_slack": True,
                        "raw_Ttheta_plus_true_logbase_PP_exact": True,
                        "AP_exact_maps_match_Q_and_Cminus": True,
                        "raw_mu_squared_mask_not_used": True})
                    for name, quantity in intervals.items():
                        aggregates[cfg][name].append(c, quantity, ["identity_maps_and_weights", config_position, name])
                    for name in ("principalQ", "principalCminus", "principalSigned", "RAP", "p0Principal", "p0RAP"):
                        aggregates[cfg][name].append(c, ap[name], ["AP_instances", ap["position"], name])
                    counts["AP_components"] += ap["component_count"]
                    counts["AP_groups"] += ap["group_count"]
                    triple["config_refs"].append({"config": cfg, "map_ref": config_position,
                                                  "AP_ref": ap["position"], "template_ref": template["id"]})
                    if "replace_lcm_by_product" not in falsifiers:
                        for row in candidates:
                            for ell in template["weights"]["active"]:
                                if ell > 1 and row["j"] % ell == 0 and row["j"] % (ell * ell):
                                    assert template["weights"]["lambdas"][ell]
                                    falsifiers["replace_lcm_by_product"] = {
                                        "candidate_ref": row["id"], "j": row["j"], "k": ell, "l": ell,
                                        "actual_lcm": ell, "wrong_product": ell * ell,
                                        "actual_divides_j": True, "wrong_product_divides_j": False,
                                        "shared_factors_retained": True}
                                    break
                            if "replace_lcm_by_product" in falsifiers:
                                break
                stores["physical_triples"].put(triple)
                triples_summary.append({"id": triple["id"], "t": t, "d": d, "q_count": len(qs),
                                        "empty_integer_window": low > high, "empty_prime_window": not qs})
                if counts["triples"] % 25 == 0:
                    progress("ALL_TRIPLES_AND_Q_AP", **counts, primitive_logs=oracle.primitive_count,
                             templates=len(templates.templates))
    reference_aggregates = {name: Affine(oracle) for name in ("M0theta", "M0raw", "PP_reference0", "Md_model")}
    reference_summary = []
    for pair in pairs:
        ref = evaluate_reference(pair, beta_by_pair[pair[2]], segment_flags, pp, primes,
                                 oracle, templates, OUT, stores["reference_fibres"], strict)
        for name, key in (("M0theta", "theta"), ("M0raw", "raw"), ("PP_reference0", "pp"), ("Md_model", "Md")):
            reference_aggregates[name].append(ref["c"], ref[key], ["reference_fibres", ref["position"], key])
        counts["reference_b_axes"] += ref["L"]
        counts["reference_theta_axes"] += ref["theta_positions"]
        counts["reference_PP_axes"] += ref["pp_positions"]
        reference_summary.append({"d": ref["d"], "c": ref["c"], "r": ref["r"], "A": ref["A"], "J": ref["J"],
                                  "L": ref["L"], "reference_ref": ref["position"], "all_b_bitmap": ref["bitmap"]})
        if len(reference_summary) % 10 == 0:
            progress("LITERAL_M0_ALL_B", completed_pairs=len(reference_summary), **counts,
                     primitive_logs=oracle.primitive_count)
    globals_by_config = {}
    for cfg, z, P, K in CONFIGS:
        values = {name: aggregate.data("AP_PRINCIPAL_INTEGRAL" if name.startswith("principal") or name == "p0Principal" else "ACTUAL_EXACT_AFFINE_MAPS")
                  for name, aggregate in aggregates[cfg].items()}
        values["Gamma0_theta"] = difference(oracle, aggregates[cfg]["Ttheta"], reference_aggregates["M0theta"]).data()
        values["Gamma0_raw"] = difference(oracle, aggregates[cfg]["Traw"], reference_aggregates["M0raw"]).data()
        values["Gamma0_PP_correction"] = difference(oracle, aggregates[cfg]["PPbeta"], reference_aggregates["PP_reference0"]).data()
        values["new_principal_minus_M0"] = difference(oracle, aggregates[cfg]["principalSigned"], reference_aggregates["M0theta"]).data("AP_PRINCIPAL_INTEGRAL_COMPARISON")
        values["Q_minus_Cminus_minus_Ctail_bound"] = {"identity": "Ttheta + nonnegative slack",
                                                      "slack": values["slack"], "tail_separate": values["Ctail"]}
        values["exact_remainder_identity"] = {"actual": "Q-Cminus", "principal": "principalSigned",
                                               "remainder": "all AP actual_minus_principal terms, before any bound",
                                               "finite_RAP_not_source_BV": values["RAP"]}
        globals_by_config[cfg] = values
    for key in ("replace_rough_ge_by_strict_gt", "impose_gcd_p_v_equal1", "replace_lcm_by_product",
                "forget_raw_properpowers", "replace_weight_logj_by_logbase"):
        falsifiers.setdefault(key, {"status": "NONE_IN_DOMAIN_COMPLETE_PHYSICAL_SEARCH"})
    for key in ("force_L_positive", "keep_only_minimum_p_in_Cminus", "delete_true_composite_tail", "delete_modules_greater_than_Y"):
        falsifiers.setdefault(key, {})
        for cfg, z, P, K in CONFIGS:
            falsifiers[key].setdefault(cfg, {"status": "NONE_IN_DOMAIN_COMPLETE_PHYSICAL_SEARCH"})
    local_square_pf = factor(49, primes)
    assert local_square_pf == [(7, 2)]
    local_square_cell = candidate_cells(local_square_pf, 49, 3 * 11 * 13, 17, primes)[0]
    assert local_square_cell["p"] == 7 and local_square_cell["v"] == 7
    assert local_square_cell["rough_indicator"] == 1 and local_square_cell["p_divides_v"]
    assert local_square_cell["gcd_p_v"] == 7 and local_square_cell["L_K0_K1"] == {"0": 1, "1": 1}
    local_identity, local_identity_cert = strict.vector(["local_outside_window", "log49_equals2log7"],
                                                       {49: Fraction(1), 7: Fraction(-2)})
    assert local_identity == (0, 0)
    local_log_difference, local_difference_cert = strict.vector(["local_outside_window", "logj_vs_logbase"],
                                                               {49: Fraction(1), 7: Fraction(-1)})
    assert local_log_difference[0] > 0
    local_source_weights = actual_weights(2, 3 * 11 * 13, p0, primes)
    assert sum((value for k, value in local_source_weights["lambdas"].items() if 49 % k == 0), Fraction(0)) == 1
    falsifiers["separate_local_p_squared_not_physical_incidence"] = {
        "j": 49, "p": 7, "v": 7, "factorization": local_square_pf, "tested_actual_cell": local_square_cell,
        "rough_ge_p": True, "rough_gt_p": False, "gcd_p_v": 7,
        "raw_logbase_nonzero_mu_squared_would_erase": True,
        "source_z2_actual_lambda_square": "1/1", "log49_equals2log7_certificate": local_identity_cert,
        "log49_minus_log7_strict_POS_certificate": local_difference_cert,
        "physical_N1e8_incidence_not_claimed": True}
    local_v = 3 * 7 * 11 * 13
    local_j = 17 * local_v
    local_t = 19 * 23 * 29
    local_negative_cells = candidate_cells(factor(local_j, primes), local_j, local_t, 17, primes)
    local_p17 = next(cell for cell in local_negative_cells if cell["p"] == 17)
    assert local_p17["r"] == 4 and local_p17["L_K0_K1"] == {"0": -3, "1": -1}
    assert not local_p17["actual_minimum"] and local_j < LEFT
    falsifiers["separate_local_L_negative_both_K_not_physical_incidence"] = {
        "j": local_j, "v": local_v, "p": 17, "t": local_t,
        "tested_all_actual_factor_cells": local_negative_cells,
        "K0_and_K1_actual_negative": True, "outside_new_window": True,
        "physical_N1e8_incidence_not_claimed": True}
    falsifiers["promote_test_window_to_source_guard"] = {"x_test": RIGHT, "N_over4": N // 4,
                                                        "x_test_le_Nover4": False,
                                                        "source_window_stays_distinct": True}
    falsifiers["promote_p0_with_no_Euler_cost"] = {"p0_actual": p0,
        "Euler_G_exclusion_factor": frac(Fraction(p0 - 2, p0 - 1)),
        "retained_principal_factor": frac(1 - Fraction(1, p0 - 1)),
        "ideal_product_inflation_times_retention": "1/1", "net_Gamma_credit_not_proved": True,
        "all_finite_G_comparisons_stored_per_AP_instance": True}
    # The exact log maps/affine expressions, every integral enclosure and every
    # per-class point are stored before this final report; no unreported sign.
    cert_counts = {}
    for cfg, values in globals_by_config.items():
        for name, value in values.items():
            if "whole_box_certificate" in value:
                cert = value["whole_box_certificate"]
                stores["certificates"].put({"config": cfg, "name": name, "certificate": cert,
                                            "intercept": value["intercept_interval"], "slope": value["slope_interval"],
                                            "S_N_box": value["S_N_acquired_box"]})
                cert_counts[cert["sign"]] = cert_counts.get(cert["sign"], 0) + 1
    reference_output = {name: value.data("SEPARATE_Md_MODEL_PRINCIPAL" if name == "Md_model" else "ACTUAL_EXACT_AFFINE_MAPS")
                        for name, value in reference_aggregates.items()}
    for name, value in reference_output.items():
        stores["certificates"].put({"name": name, "certificate": value["whole_box_certificate"],
                                    "intercept": value["intercept_interval"], "slope": value["slope_interval"]})
        sign = value["whole_box_certificate"]["sign"]
        cert_counts[sign] = cert_counts.get(sign, 0) + 1
    assert stores["certificates"].count == sum(strict.counts.values()) + sum(cert_counts.values())
    logs = oracle.close()
    catalog_files = {name: store.close() for name, store in stores.items()}
    u = oracle.cache[N]
    data = {"status": "PASS_NEW_COMPOSITE20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE", "round": 20,
            "node": "13.12", "role": 6, "parameters": {"N": N, "alpha": ALPHA, "Q": Q_ORIGINAL,
                "a": A, "M": M, "h": H, "p0_actual": p0, "window": [LEFT + 1, RIGHT],
                "source_z": 2, "source_P": 1, "source_K": 1,
                "test_configs": [list(row) for row in CONFIGS], "S_N_box": [frac(v) for v in SN]},
            "parameter_integer_certificates": parameter_certificates,
            "source_guards": {"x_test_le_Nover4": False, "u_ge10pow24": Fraction(u[1], SCALE) >= 10 ** 24,
                              "source_onset": "u>=10^24", "source_low_layer_empty_at_finite_N": True,
                              "source_analytic_ceil_and_BV_SD_guards_not_proved_by_bank": True},
            "complete_bitmap": bitmap, "new_small_prime_axes": small_info,
            "all_new_properpowers_including_nonunits": properpower_catalog,
            "counts": counts, "all_pairs_including_A0": [list(pair) for pair in pairs],
            "all_triples_summary": triples_summary, "all_reference_fibres_summary": reference_summary,
            "all_template_headers": [template["header"] for template in templates.templates.values()],
            "all_positions_and_certificates_stored_in_catalogs": catalog_files,
            "aggregate_affine_expressions_and_certificates": globals_by_config,
            "literal_M0_and_separate_Md": reference_output,
            "strict_aggregate_certificate_labels": cert_counts, "primitive_logs": logs,
            "new_falsifiers": falsifiers, "exact_identities": {"B1": True, "B2_actual_Bonferroni": True,
                "B3_slack_and_tail": True, "B5_prime_support_all_quotients_and_all_physical_classes": True,
                "AP_grouping_before_abs": True, "literal_M0_all_b": True,
                "raw_Ttheta_plus_PPbeta_and_M0raw_M0theta_plus_PPref": True,
                "Gamma0raw_Gamma0theta_plus_PPbeta_minus_PPref_by_exact_affine_terms": True},
            "coefficient_map_compression_has_full_indices_and_exact_constants": True,
            "actual_fixed_sign_certificate_counts": strict.counts,
            "fixed_sign_policy": "prime-log reduction, exact ZERO only by vanishing reduced coefficients; any other unseparated fixed sign raises ArithmeticError",
            "float_operations": 0, "D_W_kernel_evaluations_in_this_bank": 0,
            "D_W_kernel_unresolved_signs_in_this_bank": 0,
            "actual_fixed_unresolved_signs": 0,
            "principal_interval_or_parameter_box_indecisions_published_separately": True,
            "old_producer_or_Lean_executions": 0, "D_W_old_kernels_not_replayed": True,
            "source_budget_or_Lean_B6_SD_proved": False, "victory": False,
            "unpaid": ["source_SD_and_effective_AP_onsets", "full_principal_favorable_comparison",
                       "large_prime_tail_level_and_slack_optimization", "whole_Gamma", "whole_Ua_Q_k1_raw_PP_source_ledger",
                       "parents_W_capacity_medium_long_nonSS_TA", "entire_D_N"]}
    with RESULT.open("x", encoding="utf8", newline="\n") as handle:
        json.dump(data, handle, indent=2, sort_keys=True)
        handle.write("\n")
    progress("FINAL_CANONICAL_NEW_COMPOSITE20", status=data["status"], result=str(RESULT),
             result_sha256=file_info(RESULT)["sha256"], primitive_logs=logs["primitive_count"],
             counts=counts, certificates=cert_counts, float_operations=0, victory=False)
    return data
