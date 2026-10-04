"""NEW complete friable20 bank; execution requires the separate root-gated launcher."""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
import gzip
import hashlib
import json
from math import gcd, prod
from pathlib import Path

from core import (A, ALPHA, D, M, N, P0, Q, QHI, QLO, Y_TEST, Z,
                  Arithmetic, abs_interval, add_vector, exp_interval,
                  strict_certificate, text, vector_json)
from annexes import euler_rankin, totient_annex
from outward import LogOracle, add, iv_json, mul, scale

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
ROUND = BASE / "round20"
OWN = ROUND / "role6_friable"
OUT = OWN / "canonical_attempt01"
RESULT = ROUND / "friable.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def progress(stage: str, **data) -> None:
    print(json.dumps({"stage": stage, **data}, sort_keys=True), flush=True)


def prefix_certificate(resource: dict) -> dict:
    size_guard = resource["n"] >= D
    smooth = resource["largestPrime"] <= Y_TEST
    if not size_guard or not smooth:
        return {"size_guard_n_ge_D": size_guard, "smooth_Ytest": smooth,
                "certificate": None, "reason": "resource_below_D" if not size_guard else "actual_large_prime_above_Ytest"}
    value = 1
    prefix = []
    previous = 1
    for p in resource["factor_multiset"]:
        previous = value
        value *= p
        prefix.append(p)
        if value >= D:
            break
    assert prod(resource["factor_multiset"]) == resource["n"]
    assert resource["n"] % value == 0 and previous < D <= value < D * Y_TEST
    assert all(p <= Y_TEST for p in prefix)
    return {"size_guard_n_ge_D": True, "smooth_Ytest": True,
            "certificate": {"d": value, "prefix_multiset": prefix, "previous_product": previous,
                            "last_prime": prefix[-1], "quotient": resource["n"] // value,
                            "gcd_prefix_quotient": gcd(value, resource["n"] // value),
                            "unit_N": gcd(value, N) == 1,
                            "D_le_d_lt_DY": True, "d_divides_actual_resource": True}}


def small_semiprime(arithmetic: Arithmetic, resource: dict) -> bool:
    minimum = resource["factor_multiset"][0]
    quotient = resource["n"] // minimum
    return minimum <= Z and arithmetic.record(quotient)["prime"]


def source_guard_configuration(arithmetic: Arithmetic) -> dict:
    oracle = arithmetic.oracle
    u = oracle.log(N)
    ell = (oracle.log(u[0])[0], oracle.log(u[1])[1])
    assert 0 < ell[0] <= ell[1]
    exponent = (u[0] / (128 * ell[1]), u[1] / (128 * ell[0]))
    exponential = exp_interval(exponent)
    floor_lo = exponential[0].numerator // exponential[0].denominator
    floor_hi = exponential[1].numerator // exponential[1].denominator
    assert floor_lo == floor_hi == 1 and 1 <= exponential[0] <= exponential[1] < 2
    assert u[1] < 10 ** 24 and ell[1] < 6
    assert (ALPHA - 1) ** 4 < N <= ALPHA ** 4
    assert (A - 1) ** 16 < N ** 7 <= A ** 16
    assert (M - 1) ** 4 < N ** 3 <= M ** 4
    assert Z ** 4 <= N < (Z + 1) ** 4
    assert D * D == N and Q == (N - 1) // ALPHA
    assert P0 == next(p for p in arithmetic.primes if p != 2 and N % p)
    return {"N": N, "alpha": ALPHA, "Q_original": Q, "a": A, "M": M, "Z": Z, "p0_actual": P0, "D": D,
            "u": iv_json(u), "ell": iv_json(ell), "T_source": iv_json(exponent),
            "exp_T_source": iv_json(exponential), "Y_source_floor_certified": 1,
            "log_Y_source": strict_certificate((Fraction(0), Fraction(0)), True),
            "sigma_source": None, "sigma_source_status": "UNDEFINED_LOG_Y_EQUALS_ZERO",
            "source_guards": {"u_ge10pow24": False, "ell_ge6": False, "logY_ge4": False},
            "Y_test": Y_TEST, "test_threshold_never_substituted_for_source": True,
            "integer_parameter_rounding_verified": True}


def matrix(first_base: int | None, cvec: dict[int, Fraction]) -> dict[tuple[int, int], Fraction]:
    if first_base is None:
        return {}
    return {tuple(sorted((first_base, p))): coefficient for p, coefficient in cvec.items() if coefficient}


def matrix_json(values: dict[tuple[int, int], Fraction]) -> list:
    return [[p, q, text(coefficient)] for (p, q), coefficient in sorted(values.items()) if coefficient]


def add_matrix(target: dict, source: dict, coefficient=1) -> None:
    for key, value in source.items():
        updated = target.get(key, Fraction(0)) + coefficient * value
        if updated:
            target[key] = updated
        elif key in target:
            del target[key]


def exact_class_members(lo: int, hi: int, d: int, multiplier: int) -> tuple[list[int], dict]:
    common = gcd(multiplier, d)
    solvable = N % common == 0
    if lo > hi or not solvable:
        return [], {"gcd_multiplier_d": common, "solvable": solvable, "residue": None,
                    "effective_modulus": d // common, "empty_window": lo > hi}
    modulus = d // common
    reduced_multiplier = multiplier // common
    residue = ((N // common) * pow(reduced_multiplier, -1, modulus)) % modulus if modulus > 1 else 0
    first = lo + (residue - lo) % modulus
    members = list(range(first, hi + 1, modulus)) if first <= hi else []
    assert all((multiplier * q - N) % d == 0 for q in members)
    return members, {"gcd_multiplier_d": common, "solvable": True, "residue": residue,
                     "effective_modulus": modulus, "empty_window": False}


def affine_class_annex(observed: dict[int, list], arithmetic: Arithmetic) -> dict:
    tests = {2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 25, 30, 10000}
    divisors = sorted(set(observed) | tests)
    catalog = [{"d": d, "observed_prefix_origins": observed.get(d, []),
                "explicit_class_test": d in tests, "not_promoted_to_source_B_D": True,
                "gcd_d_N": gcd(d, N), "gcd_d_p0": gcd(d, P0),
                "actual_factorization": arithmetic.factors(d)} for d in divisors]
    membership_cache, memberships, rows = {}, [], []
    unions = []
    observed_inverse = sum((Fraction(1, d) for d in observed), Fraction(0))
    plus1_witness = None
    emax = (N - Q - 1) // M
    for e in range(1, emax + 2):
        lo, hi = max(QLO, M), min(QHI, (N - Q - 1) // e)
        length = max(0, hi - lo + 1)
        counts = {0: 0, 1: 0}
        union = {0: set(), 1: set()}
        for d in divisors:
            for resource, multiplier in ((1, 1), (0, P0)):
                key = (lo, hi, d, multiplier)
                if key not in membership_cache:
                    members, info = exact_class_members(lo, hi, d, multiplier)
                    units = [q for q in members if gcd(q, N) == 1]
                    if gcd(d, N) > 1:
                        assert not units
                    if resource == 0 and d % P0 == 0:
                        assert not members
                    ref = len(memberships)
                    membership_cache[key] = ref
                    memberships.append({"id": ref, "qlo": lo, "qhi": hi, "d": d,
                                        "resource": resource, "members": members,
                                        "unit_N_members": units, **info})
                membership = memberships[membership_cache[key]]
                cardinal = len(membership["members"])
                bound_window = Fraction(length - 1, d) + 1 if length else Fraction(0)
                bound_source = Fraction(N, e * d) + 1
                assert cardinal <= bound_window and cardinal <= bound_source
                if plus1_witness is None and length and cardinal > Fraction(length - 1, d):
                    plus1_witness = {"e": e, "d": d, "resource": resource,
                                     "card": cardinal, "without_plus1": text(Fraction(length - 1, d)),
                                     "membership_ref": membership["id"]}
                rows.append({"e": e, "d": d, "resource": resource, "membership_ref": membership["id"],
                             "L": length, "bound_Lminus1_over_d_plus1": text(bound_window),
                             "bound_N_over_ed_plus1": text(bound_source), "actual_card": cardinal,
                             "actual_unit_card": len(membership["unit_N_members"]),
                             "literal_plus1_preserved": True})
                if d in observed:
                    counts[resource] += cardinal
                    union[resource].update(membership["members"])
        for resource in (0, 1):
            assert len(union[resource]) <= counts[resource]
            assert counts[resource] <= Fraction(N, e) * observed_inverse + len(observed)
        total_union = sorted(union[0] | union[1])
        assert len(total_union) <= counts[0] + counts[1]
        unions.append({"e": e, "qlo": lo, "qhi": hi,
                       "resource0_union": sorted(union[0]), "resource1_union": sorted(union[1]),
                       "union_both": total_union, "sum_actual_class_cards0": counts[0], "sum_actual_class_cards1": counts[1],
                       "observed_sum1overd": text(observed_inverse), "observed_card_d": len(observed),
                       "positive_union_bound_one_resource": text(Fraction(N, e) * observed_inverse + len(observed)),
                       "two_resources_two_fronts_preserved": True})
    return {"d_catalog": catalog, "observed_prefix_d_only_count": len(observed),
            "not_full_B_D": True, "explicit_test_d": sorted(tests), "membership_catalog": memberships,
            "all_e1through_Eplus1": emax + 1, "all_class_rows": rows, "all_unions": unions,
            "plus1_deletion_counterexample": plus1_witness,
            "empty_window_eabove_cap_retained": True}


def run() -> dict:
    if RESULT.exists():
        raise RuntimeError("Friable20 canonical result already exists; routine replay forbidden")
    oracle = LogOracle(OUT / "primitive_log_enclosures.jsonl.gz")
    arithmetic = Arithmetic(oracle)
    config = source_guard_configuration(arithmetic)
    progress("NEW_Q_ARITHMETIC_AND_SOURCE_GUARDS", integer_axes=Q, Y_source=1, Y_test=Y_TEST)
    table_files = {}
    for name, data in (("mu_signed_bytes", arithmetic.mu.tobytes()),
                       ("phi_uint32", arithmetic.phi.tobytes()), ("spf_uint32", arithmetic.spf.tobytes())):
        path = OUT / (name + ".bin.gz")
        with path.open("xb") as handle:
            handle.write(gzip.compress(data, mtime=0))
        table_files[name] = {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path),
                             "uncompressed_bytes": len(data), "uncompressed_sha256": hashlib.sha256(data).hexdigest()}
    qrows, labels, observed = [], [], {}
    requested_caps = []
    active_indices = []
    q_f1, q_f0_only, q_h = set(), set(), set()
    emax = (N - Q - 1) // M
    e_catalog = [arithmetic.record(e) for e in range(1, emax + 2)]
    counters = Counter()
    for q in range(QLO, QHI + 1):
        qrec = arithmetic.record(q)
        resource1, resource0 = arithmetic.record(N - q), arithmetic.record(N - P0 * q)
        prefix1, prefix0 = prefix_certificate(resource1), prefix_certificate(resource0)
        for resource_index, pref in ((1, prefix1), (0, prefix0)):
            if pref["certificate"] is not None:
                d = pref["certificate"]["d"]
                observed.setdefault(d, []).append([q, resource_index])
        ss1, ss0 = small_semiprime(arithmetic, resource1), small_semiprime(arithmetic, resource0)
        cell_guards = {"N_ne_zero": N != 0, "N_even": N % 2 == 0, "q_pos": q > 0,
                       "q_unit": qrec["unit_N"], "anchor_mul_q_lt": P0 * q < N,
                       "resource1_two": resource1["n"] >= 2, "resource0_two": resource0["n"] >= 2,
                       "resource1_composite": not resource1["prime"], "resource0_composite": not resource0["prime"]}
        cell = all(cell_guards.values())
        selector = ((resource1["factor_multiset"][0] <= Z or resource0["factor_multiset"][0] <= Z)
                    and not (ss1 and ss0))
        h_product = resource1["cofactor"] * resource0["cofactor"]
        r_product = resource1["terminalPrime"] * resource0["terminalPrime"]
        direct = h_product <= r_product
        conductor = h_product if direct else r_product
        original_b = 2
        assert (original_b - 1) ** 64 < N <= original_b ** 64
        stratum = "short" if conductor <= original_b else "medium" if conductor * conductor <= N else "long"
        assert conductor < N
        f1, f0 = prefix1["smooth_Ytest"], prefix0["smooth_Ytest"]
        cap = (N - Q - 1) // q
        qrow = {"q": q, "q_record": qrec, "resource1": resource1, "resource0": resource0,
                "ResourceCell_guards": cell_guards, "ResourceCell": cell,
                "smallSemiprime1": ss1, "smallSemiprime0": ss0, "nonSSSelector": selector,
                "prefix1": prefix1, "prefix0": prefix0, "F1_test": f1, "F0_test": f0,
                "F_test": f1 or f0, "F0_inter_F1": f0 and f1, "F0_minus_F1": f0 and not f1,
                "F_source_Y1": False, "cap_e": cap,
                "terminal_cofactor_channel": "D" if direct else "P", "equality_goes_D": h_product == r_product,
                "h_product": h_product, "r_product": r_product, "conductor": conductor,
                "B_original": original_b, "stratum": stratum,
                "resource1_gcd_terminal_cofactor": gcd(resource1["cofactor"], resource1["terminalPrime"]),
                "resource0_gcd_terminal_cofactor": gcd(resource0["cofactor"], resource0["terminalPrime"])}
        qrows.append(qrow)
        for e in range(1, cap + 1):
            erec = e_catalog[e - 1]
            n = N - e * q
            nrec = arithmetic.record(n)
            guards = {"ResourceCell": cell, "q_prime": qrec["prime"], "M_le_q": M <= q,
                      "anchor_lt_e": P0 < e, "Squarefree_e": erec["squarefree"], "e_unit_N": erec["unit_N"],
                      "actual_cap": e * q + Q + 1 <= N, "nonSSSelector": selector}
            in_h = all(guards.values())
            selected = in_h and (f0 or f1)
            first_theta = n if nrec["prime"] and nrec["unit_N"] else None
            first_raw = nrec["factors"][0][0] if len(nrec["factors"]) == 1 and nrec["unit_N"] else None
            label = {"id": len(labels), "e": e, "q": q, "e_catalog_ref": e - 1, "n_e": nrec,
                     "StructuralSupport_guards": guards, "H": in_h, "F": selected,
                     "F1_H": in_h and f1, "F0_H": in_h and f0,
                     "F0minusF1_H": in_h and f0 and not f1,
                     "theta_first_log_base": first_theta, "raw_first_log_base": first_raw,
                     "theta0": first_theta is None, "raw0": first_raw is None,
                     "properpower_first_axis": nrec["properpower"], "stratum": stratum,
                     "cap_margin": N - e * q - Q - 1,
                     "all_integer_label_before_prime_or_friable_masks": True}
            if in_h:
                assert e <= A < q and e <= Q and e < q and q != P0
                assert resource0["n"] >= (e - P0) * q + Q + 1 >= M >= D
                assert resource1["n"] >= (e - 1) * q + Q + 1 >= M >= D
                assert gcd(resource1["n"], resource0["n"]) == 1
                q_h.add(q)
                counters["H"] += 1
                counters["H_" + stratum] += 1
                if f1:
                    q_f1.add(q)
                if f0 and not f1:
                    q_f0_only.add(q)
            if selected:
                counters["F"] += 1
                if first_raw is not None:
                    active_indices.append(label["id"])
                    requested_caps.append(min(Q, (e * q - 1) // A))
                    counters["active_raw"] += 1
                    counters["active_theta"] += first_theta is not None
                else:
                    label["zero_weight_reason"] = "both_actual_first_measures_zero_no_kernel_evaluated"
                    label["theta_bracket_zero_certificate"] = strict_certificate((Fraction(0), Fraction(0)), True)
                    label["raw_bracket_zero_certificate"] = strict_certificate((Fraction(0), Fraction(0)), True)
            labels.append(label)
        assert (cap + 1) * q + Q + 1 > N
        qrow["overflow_e_test"] = {"e": cap + 1, "actual_cap": False, "outside_H": True}
    assert len(qrows) == 1001
    q_index = {row["q"]: row for row in qrows}
    for q in q_f1:
        m1 = q_index[q]["resource1"]
        if m1["squarefree"]:
            requested_caps.append(min(Q, (m1["n"] - 1) // A))
    progress("FULL_Q_AND_ALL_CORE_LABELS", q_axes=len(qrows), all_e_labels=len(labels),
             H=counters["H"], F=counters["F"], active_raw=counters["active_raw"], unique_F1_q=len(q_f1))
    arithmetic.prepare_prefixes(requested_caps)
    u = oracle.log(N)
    demand_records = []
    demand_weights = {"theta": {}, "raw": {}}
    totals = {"theta": (Fraction(0), Fraction(0)), "raw": (Fraction(0), Fraction(0))}
    exact_totals = {"theta": {}, "raw": {}}
    for index in active_indices:
        label = labels[index]
        e, q = label["e"], label["q"]
        m = e * q
        kernel = arithmetic.kernel(m)
        assert kernel["mu_m"] == -arithmetic.mu_value(e)
        mangoldt_e = {arithmetic.factors(e)[0][0]: Fraction(1)} if len(arithmetic.factors(e)) == 1 else {}
        rhs_c = mangoldt_e.copy()
        add_vector(rhs_c, kernel["W_vector"], -arithmetic.mu_value(e))
        assert rhs_c == kernel["C_vector"]
        short_rhs = {}
        add_vector(short_rhs, mangoldt_e, -1)
        assert short_rhs == kernel["Ua_vector"]
        assert max(abs(kernel["W_bounds"][0]), abs(kernel["W_bounds"][1])) <= u[1] * arithmetic.tk[kernel["record"]["R"]]
        assert max(abs(kernel["C_bounds"][0]), abs(kernel["C_bounds"][1])) <= 7 * u[0] ** 2
        row = {"label_ref": index, "e": e, "q": q, "m": m, "kernel_ref": str(m),
               "cofactor_identity_exact": True, "short_sum_equals_minus_Lambda_e_exact": True,
               "generic_TK_kernel_envelope_verified": True}
        for measure, base in (("theta", label["theta_first_log_base"]), ("raw", label["raw_first_log_base"])):
            bounds = mul(oracle.log(base), kernel["C_bounds"]) if base is not None else (Fraction(0), Fraction(0))
            exact = matrix(base, kernel["C_vector"])
            certificate = strict_certificate(bounds, not exact)
            assert max(abs(bounds[0]), abs(bounds[1])) <= 7 * u[0] ** 3
            absolute = abs_interval(bounds)
            sign = -1 if certificate["sign"] == "NEG" else 1
            absolute_matrix = {key: sign * coefficient for key, coefficient in exact.items()}
            row[measure + "_bracket_matrix"] = matrix_json(exact)
            row[measure + "_bracket_certificate"] = certificate
            row[measure + "_absolute_interval"] = iv_json(absolute)
            physical_key = (N - m, m)
            assert physical_key not in demand_weights[measure]
            demand_weights[measure][physical_key] = (absolute, absolute_matrix)
            totals[measure] = add(totals[measure], absolute)
            add_matrix(exact_totals[measure], absolute_matrix)
        demand_records.append(row)
    reciprocals = []
    reciprocal_weights = {}
    reciprocal_total = (Fraction(0), Fraction(0))
    reciprocal_matrix = {}
    for q in sorted(q_f1):
        resource = q_index[q]["resource1"]
        kernel = arithmetic.kernel(resource["n"])
        exact = matrix(q, kernel["C_vector"])
        bounds = mul(oracle.log(q), kernel["C_bounds"]) if exact else (Fraction(0), Fraction(0))
        certificate = strict_certificate(bounds, not exact)
        absolute = abs_interval(bounds)
        assert absolute[1] <= 7 * u[0] ** 3 * resource["tau"]
        sign = -1 if certificate["sign"] == "NEG" else 1
        absolute_matrix = {key: sign * coefficient for key, coefficient in exact.items()}
        physical_key = (q, resource["n"])
        assert physical_key not in reciprocal_weights
        reciprocal_weights[physical_key] = (absolute, absolute_matrix)
        reciprocal_total = add(reciprocal_total, absolute)
        add_matrix(reciprocal_matrix, absolute_matrix)
        reciprocals.append({"q": q, "m1": resource, "kernel_ref": str(resource["n"]),
                            "physical_key": list(physical_key), "bracket_matrix": matrix_json(exact),
                            "bracket_certificate": certificate, "absolute_interval": iv_json(absolute),
                            "mu0_entry_not_removed_from_tau_majorant": not resource["squarefree"],
                            "generic_reciprocal_envelope_verified": True, "unique_consumption": True})
    zero_m0 = []
    for q in sorted(q_h):
        first = arithmetic.record(P0 * q)
        assert first["factors"] == ((P0, 1), (q, 1)) and not first["prime"] and not first["properpower"]
        zero_m0.append({"q": q, "m0": q_index[q]["resource0"], "actual_first_axis": first,
                        "theta_bracket": strict_certificate((Fraction(0), Fraction(0)), True),
                        "raw_bracket": strict_certificate((Fraction(0), Fraction(0)), True),
                        "kernel_not_evaluated": "two_distinct_prime_first_axis_zero"})
    unions = {}
    for measure in ("theta", "raw"):
        weighted_union = dict(demand_weights[measure])
        intersections = []
        for key, weight in reciprocal_weights.items():
            if key in weighted_union:
                assert weighted_union[key][1] == weight[1]
                intersections.append(list(key))
            else:
                weighted_union[key] = weight
        union_total = (Fraction(0), Fraction(0))
        union_matrix = {}
        for weight in weighted_union.values():
            union_total = add(union_total, weight[0])
            add_matrix(union_matrix, weight[1])
        comparison = exact_totals[measure].copy()
        add_matrix(comparison, reciprocal_matrix)
        add_matrix(comparison, union_matrix, -1)
        expected_intersection = {}
        for key in intersections:
            add_matrix(expected_intersection, reciprocal_weights[tuple(key)][1])
        assert comparison == expected_intersection
        unions[measure] = {"demand_absolute": strict_certificate(totals[measure], not exact_totals[measure]),
                           "reciprocal_absolute": strict_certificate(reciprocal_total, not reciprocal_matrix),
                           "union_absolute": strict_certificate(union_total, not union_matrix),
                           "demand_matrix": matrix_json(exact_totals[measure]),
                           "reciprocal_matrix": matrix_json(reciprocal_matrix), "union_matrix": matrix_json(union_matrix),
                           "intersections": intersections, "single_consumption_identity_exact": True,
                           "alternative_theta_or_raw_not_added_twice": True}
    demand_vertices_all = sorted({(N - label["e"] * label["q"], label["e"] * label["q"])
                                  for label in labels if label["F"]})
    reciprocal_vertices_all = [(q, N - q) for q in sorted(q_f1)]
    complete_union = sorted(set(demand_vertices_all) | set(reciprocal_vertices_all))
    unpaid = [{"q": q, "m1": q_index[q]["resource1"], "status": "UNPAID_F0_MINUS_F1_NONFRIABLE_M1",
               "not_in_Q_F1": True, "kernel_not_evaluated_for_credit": True} for q in sorted(q_f0_only)]
    for row in unpaid:
        assert row["q"] not in q_f1 and row["m1"]["largestPrime"] > Y_TEST
    progress("TRUE_NEW_KERNELS_AND_UNIQUE_RECIPROCALS", kernels=len(arithmetic.kernel_cache),
             active_demands=len(demand_records), unique_reciprocals=len(reciprocals), unpaid_m1=len(unpaid))
    classes = affine_class_annex(observed, arithmetic)
    progress("AFFINE_CLASSES_LITERAL_FRONTS", observed_prefix_divisors=len(observed), class_rows=len(classes["all_class_rows"]))
    euler = euler_rankin(arithmetic)
    progress("FINITE_EULER_EXHAUSTIVE", tuple_count=euler["tuple_count"])
    totients = totient_annex(arithmetic)
    progress("FINITE_TOTIENT_EXHAUSTIVE", integer_axes=totients["integer_axes"])
    repeat_witness = None
    for row in qrows:
        for resource_index in (0, 1):
            prefix = row["prefix" + str(resource_index)]["certificate"]
            if prefix is not None and len(prefix["prefix_multiset"]) != len(set(prefix["prefix_multiset"])):
                repeat_witness = {"q": row["q"], "resource": resource_index, "actual_prefix": prefix,
                                  "distinct_prime_product": prod(set(prefix["prefix_multiset"])),
                                  "status": "ACTUAL_REPEATED_FACTORS_RETAINED"}
                break
        if repeat_witness is not None:
            break
    f1_labels = {q: [label["id"] for label in labels if label["q"] == q and label["F1_H"]]
                 for q in sorted(q_f1)}
    duplicate_f1 = next(({"q": q, "all_label_refs": refs, "unique_reciprocal_count": 1,
                          "false_per_label_count": len(refs)}
                         for q, refs in f1_labels.items() if len(refs) > 1), None)
    negative_witness = next(({"kind": "demand", "label_ref": row["label_ref"],
                              "certificate": row["theta_bracket_certificate"]}
                             for row in demand_records if row["theta_bracket_certificate"]["sign"] == "NEG"), None)
    if negative_witness is None:
        negative_witness = next(({"kind": "unique_reciprocal", "q": row["q"],
                                  "certificate": row["bracket_certificate"]}
                                 for row in reciprocals if row["bracket_certificate"]["sign"] == "NEG"), None)
    falsifiers = {"discard_repeated_prime_factors": repeat_witness or {"status": "NONE_IN_DOMAIN"},
                  "discard_literal_plus1": classes["plus1_deletion_counterexample"] or {"status": "NONE_IN_DOMAIN"},
                  "count_F1_reciprocal_per_e": duplicate_f1 or {"status": "NONE_IN_DOMAIN"},
                  "replace_absolute_by_positive_part": negative_witness or {"status": "NONE_IN_DOMAIN"},
                  "drop_F0minusF1_m1": unpaid[0] if unpaid else {"status": "NONE_IN_DOMAIN"},
                  "invert_p0_when_p0_divides_d": {"d": 3, "gcd_p0_d": 3, "N_mod_gcd": N % 3,
                                                   "solvable": False, "actual_class0_card": 0},
                  "promote_Ytest_to_source": {"Y_source": 1, "Y_test": Y_TEST,
                                               "sigma_source_undefined": True, "source_guards": config["source_guards"]}}
    logs = oracle.close()
    result = {"status": "PASS_NEW_FRIABLE20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE", "round": 20, "node": "14.5", "role": 6,
              "parameters_and_source_guards": config, "all_q_axes": qrows, "all_integer_e_catalog": e_catalog,
              "all_integer_e_q_labels_before_masks": labels, "full_q_count": len(qrows), "full_label_count": len(labels),
              "counts": dict(counters), "all_active_friable_demand_weights": demand_records,
              "all_unique_F1_reciprocal_weights": reciprocals, "all_H_zero_m0_reciprocals": zero_m0,
              "F0_minus_F1_unpaid_m1": unpaid, "Q_F1": sorted(q_f1), "Q_F0minusF1": sorted(q_f0_only),
              "sum_tau_unique_F1_actual": sum(row["m1"]["tau"] for row in reciprocals),
              "absolute_payment_alternatives": unions,
              "physical_vertices": {"all_friable_demand_vertices_including_zeros": demand_vertices_all,
                                    "all_F1_reciprocal_vertices_including_mu0": reciprocal_vertices_all,
                                    "actual_union": complete_union,
                                    "intersections": sorted(set(demand_vertices_all) & set(reciprocal_vertices_all)),
                                    "all_m0_first_axis_zeros_retained": True},
              "all_actual_new_kernels": {str(m): value["record"] for m, value in sorted(arithmetic.kernel_cache.items())},
              "full_Q_arithmetic_metadata": arithmetic.arithmetic_metadata(), "full_Q_table_files": table_files,
              "affine_class_annex": classes, "finite_Euler_Rankin_annex": euler, "finite_totient_annex": totients,
              "all_F1_q_label_refs_before_unique_consumption": f1_labels, "new_local_falsifiers": falsifiers,
              "primitive_log_certificates": logs,
              "exact_identities": {"actual_cofactor_sign_and_wholeUa": True, "theta_and_raw_properpower_distinct": True,
                                    "all_k1throughQ_prefix_equivalence": True, "actual_classes_nonunits_plus1": True,
                                    "physical_reciprocals_once": True, "full_Euler_polynomials": True, "finite_TK": True},
              "float_operations": 0, "unresolved_signs": 0, "old_producer_or_Lean_executions": 0,
              "source_budget_exponents_not_certified_by_finite_bank": True, "victory": False,
              "unpaid_scope": ["F0minusF1 nonfriablem1", "remaining_nonfriable_H", "source_domain_bridge",
                               "e1_p0_singletons", "parents_W_capacity", "medium_long_complement", "wholeGamma_TA_full_ledger"]}
    with RESULT.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, separators=(",", ":"), ensure_ascii=False)
        handle.write("\n")
    progress("FINAL_CANONICAL_NEW_FRIABLE20", status=result["status"], result=str(RESULT), result_sha256=sha256(RESULT),
             kernels=len(arithmetic.kernel_cache), primitive_logs=logs["primitive_count"], float_operations=0, unresolved_signs=0, victory=False)
    return result
