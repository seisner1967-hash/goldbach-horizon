"""Fresh exhaustive finite non-SS support, bijection and physical accounting.

No tables or checks run on import.  This bank imports only the NEW captured
arithmetic helper.  It never reads a previous bank or imports an old producer.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import gcd

from arithmetic import (N, ALPHA, A, Q, M, P0, Z, BITS, SCALE, Arithmetic,
                        integer_root, ceil_div, add_vector, serialize_fraction,
                        certificate, sign_bounds)

LEFT, RIGHT, B_TEST = 1600100, 1601100, 2048
UNIVERSAL_C = "-mu(e*q)*(D_a(N-e*q,e*q)-W_kernel(N-e*q,e*q))"


def axis(ar, n):
    factors = ar.factor(n)
    unit = gcd(n, N) == 1
    prime = factors == (n,) and n >= 2
    raw = factors[0] if factors and len(set(factors)) == 1 and unit else None
    return {"n": n, "factor_multiset": list(factors), "Omega": len(factors),
            "unit_N": unit, "prime": prime,
            "theta_log_base": n if prime and unit else None,
            "raw_log_base": raw,
            "proper_power": bool(factors and len(set(factors)) == 1 and len(factors) > 1)}


def resource(ar, n):
    data = axis(ar, n)
    factors = ar.factor(n)
    assert factors
    least, terminal = factors[0], factors[-1]
    head, quotient = n // terminal, n // least
    assert ar.prime(terminal) and n == head * terminal
    assert ar.max_prime(head) <= terminal
    assert len(ar.factor(head)) + 1 == len(factors)
    data.update({"least_prime": least, "minfac_quotient": quotient,
                 "minfac_quotient_prime": ar.prime(quotient),
                 # Exact SS18 selector; there is no added strict inequality.
                 "canonical_small_semiprime": least <= Z and ar.prime(quotient),
                 "r_largest_prime": terminal, "h_full_cofactor": head,
                 "h_factor_multiset": list(ar.factor(head)),
                 "gcd_h_r": gcd(head, terminal),
                 "terminal_extraction_and_multiset_rank_verified": True})
    return data


def classify(one, zero):
    if one["theta_log_base"] or zero["theta_log_base"]:
        category = "A"
    elif one["least_prime"] > Z and zero["least_prime"] > Z:
        category = "R"
    else:
        category = "S"
    ss = one["canonical_small_semiprime"] and zero["canonical_small_semiprime"]
    if ss:
        assert category == "S"
    return category, ss, category == "S" and not ss


def coordinate(ar, q, e, one, zero, b_hyp):
    h1, r1 = one["h_full_cofactor"], one["r_largest_prime"]
    h0, r0 = zero["h_full_cofactor"], zero["r_largest_prime"]
    tag = "D" if h1 * h0 <= r1 * r0 else "P"
    aa, bb, x, y = (h1, h0, r1, r0) if tag == "D" else (r1, r0, h1, h0)
    assert gcd(one["n"], zero["n"]) == gcd(P0, zero["n"]) == 1
    cross = [gcd(v, w) for v in (h1, r1) for w in (h0, r0)]
    assert cross == [1] * 4 and gcd(P0 * aa, bb) == 1
    inverse = pow(P0 * aa, -1, bb)
    x0 = (P0 - 1) * N * inverse % bb
    numerator = P0 * aa * x0 - (P0 - 1) * N
    assert numerator % bb == 0 and (x - x0) % bb == 0
    y0, t = numerator // bb, (x - x0) // bb
    conductor = aa * bb
    assert conductor == min(h1 * h0, r1 * r0)
    assert conductor * conductor <= one["n"] * zero["n"] < N * N
    assert conductor < N and P0 * aa * x - bb * y == (P0 - 1) * N
    assert x == x0 + bb * t and y == y0 + P0 * aa * t
    q_intercept = N - aa * x0
    assert q == N - aa * x == q_intercept - conductor * t
    qmax = (N - Q - 1) // e
    lo = max(ceil_div(1 - x0, bb), ceil_div(1 - y0, P0 * aa),
             ceil_div(q_intercept - qmax, conductor))
    hi = (q_intercept - M) // conductor
    wlo = max(lo, ceil_div(q_intercept - RIGHT, conductor))
    whi = min(hi, (q_intercept - LEFT) // conductor)
    count, window_count = max(0, hi - lo + 1), max(0, whi - wlo + 1)
    assert lo <= t <= hi and wlo <= t <= whi
    assert count <= N // (e * conductor) + 1
    assert window_count <= (RIGHT - LEFT) // conductor + 1
    if tag == "D":
        assert aa >= 2 and bb >= 2 and ar.prime(x) and ar.prime(y)
        assert ar.max_prime(aa) <= x and ar.max_prime(bb) <= y and aa * bb <= x * y
    else:
        assert x >= 2 and y >= 2 and ar.prime(aa) and ar.prime(bb)
        assert ar.max_prime(x) <= aa and ar.max_prime(y) <= bb and x * y > aa * bb
    assert aa * x == one["n"] and bb * y == zero["n"]
    assert h1 >= 3 and h0 >= 7 and h1 * h0 >= 21 > b_hyp
    stratum = "SHORT" if conductor <= b_hyp else ("MEDIUM" if conductor ** 2 <= N else "LONG")
    return {"tag": tag, "e": e, "a1": aa, "b0": bb, "x": x, "y": y,
            "x0": x0, "y0_signed": y0, "t_signed": t,
            "inverse_p0a1_mod_b0": inverse, "q_intercept": q_intercept,
            "C_bal": conductor, "C_bal_squared": conductor ** 2, "stratum": stratum,
            "source_t_interval_before_factor_selectors": [lo, hi],
            "source_t_count": count, "outer_plus1_upper": serialize_fraction(Fraction(N, e * conductor) + 1),
            "window_t_interval_before_factor_selectors": [wlo, whi],
            "window_t_count": window_count, "cross_gcds": cross,
            "gcd_resources": 1, "gcd_p0_resource0": 1, "gcd_p0a1_b0": 1,
            "H1_H2_H3_and_resource_inverse_verified": True,
            "P_masks_are_parameter_primes_not_four_prime_forms": tag == "P",
            "rank3_aux_Btest_route": (2 <= one["Omega"] <= 3 and 2 <= zero["Omega"] <= 3
                                       and max(one["Omega"], zero["Omega"]) == 3
                                       and h1 * h0 <= B_TEST)}


def decode_family(ar, family, q_rows):
    """Independently enumerate every t in its full declared finite front.

    Factor selectors and non-SS are reapplied before the target prime mask.
    A family is generated from the COMPLETE unmasked q/core catalog, so the
    union of these candidate families is exactly its finite tuple domain.
    """
    tag, e, aa, bb = family["tag"], family["e"], family["a1"], family["b0"]
    x0, y0 = family["x0"], family["y0_signed"]
    lo, hi = family["window_t_interval_before_factor_selectors"]
    decoded, candidate_rows = [], []
    for t in range(lo, hi + 1):
        x, y = x0 + bb * t, y0 + P0 * aa * t
        q = N - aa * x
        assert LEFT <= q <= RIGHT and q >= M and e * q <= N - Q - 1
        assert aa * x >= 1 and bb * y >= 1
        arithmetic_guard = (x >= 2 and y >= 2 and ar.prime(aa) and ar.prime(bb)
                            and ar.max_prime(x) <= aa and ar.max_prime(y) <= bb
                            and x * y > aa * bb) if tag == "P" else (
                            aa >= 2 and bb >= 2 and ar.prime(x) and ar.prime(y)
                            and ar.max_prime(aa) <= x and ar.max_prime(bb) <= y
                            and aa * bb <= x * y)
        q_row = q_rows[q]
        selected = arithmetic_guard and q_row["unit_N"] and q_row["structural_nonSS"]
        if selected:
            actual = q_row["coordinates_by_e"][e]
            assert (actual["tag"], actual["a1"], actual["b0"], actual["x"], actual["y"],
                    actual["t_signed"]) == (tag, aa, bb, x, y, t)
            assert (aa * x, bb * y) == (q_row["n1_resource"]["n"], q_row["n0_resource"]["n"])
            decoded.append([q, e, t])
        candidate_rows.append([t, q, x, y, bool(arithmetic_guard), bool(selected)])
    assert sorted(decoded) == sorted(family["encoded_labels_q_e_t"])
    return {**family, "all_window_t_candidates_before_selectors": candidate_rows,
            "decoded_labels_q_e_t": decoded, "exact_inverse_support_verified": True}


def harmonic(ar):
    primes = [p for p in ar.primes if p <= B_TEST]
    s1 = sum((Fraction(1, p) for p in primes), Fraction(0))
    s2 = sum((Fraction(1, p * p) for p in primes), Fraction(0))
    products, pair_sum, pair_count, diagonals = [], Fraction(0), 0, []
    hasher = sha256()
    for i, p in enumerate(primes):
        row = []
        for q in primes[i:]:
            pq = p * q
            row.append(pq)
            pair_sum += Fraction(1, pq)
            pair_count += 1
            hasher.update(f"{p},{q},{pq}\n".encode("ascii"))
            if p == q:
                diagonals.append(pq)
        products.append(row)
    h2 = s1 + pair_sum
    assert h2 == s1 + (s1 * s1 + s2) / 2
    assert pair_count == len(primes) * (len(primes) + 1) // 2
    cut = [[h, list(ar.factor(h))] for h in range(2, B_TEST + 1)
           if 1 <= len(ar.factor(h)) <= 2]
    cut_sum = sum((Fraction(1, h) for h, _ in cut), Fraction(0))
    unit_cut = [row for row in cut if gcd(row[0], N) == 1]
    assert cut_sum <= h2 and all(row[0] <= B_TEST for row in cut)
    return {"B_test": B_TEST, "all_primes_through_Btest_including_2_5": primes,
            "uncut_products_upper_triangle_by_prime_index": products,
            "uncut_pair_count": pair_count, "uncut_pair_catalog_sha256_ascii_p_q_pq_lines": hasher.hexdigest(),
            "uncut_all_diagonal_p_squared": diagonals,
            "S1": serialize_fraction(s1), "S2": serialize_fraction(s2),
            "uncut_H2": serialize_fraction(h2), "direct_pair_sum": serialize_fraction(pair_sum),
            "H8_S1_plus_half_S1_squared_plus_S2_exact": True,
            "all_cut_h_2_through_Btest_Omega1or2": cut, "cut_harmonic": serialize_fraction(cut_sum),
            "cut_harmonic_le_uncut_H2": True,
            "separate_unit_cut_h": [row[0] for row in unit_cut],
            "separate_unit_cut_harmonic": serialize_fraction(sum((Fraction(1, row[0]) for row in unit_cut), Fraction(0))),
            "no_squarefree_filter_in_H8_and_no_analytic_payment": True}


def terms_sum(ar, terms):
    """Exact symbolic coefficient map of log(base)*C(physical_m).

    Equal (m,base) terms combine as integers; C is stored as its rational
    prime-log vector in the unique physical kernel catalog.  Bounds reuse the
    same per-term dyadic enclosures.  No independent rounded equality is used.
    """
    multiplicity = Counter((m, base) for m, base in terms)
    bounds = [0, 0]
    positive, negative = [0, 0], [0, 0]
    signs = Counter()
    rows = []
    for (m, base), count in sorted(multiplicity.items()):
        weight, exact_zero = ar.weighted_bounds(m, base)
        sign = sign_bounds(weight, exact_zero)
        signs[sign] += count
        bounds[0] += count * weight[0]
        bounds[1] += count * weight[1]
        if sign == "POSITIVE":
            positive[0] += count * weight[0]
            positive[1] += count * weight[1]
        elif sign == "NEGATIVE":
            negative[0] -= count * weight[1]
            negative[1] -= count * weight[0]
        rows.append([m, base, count])
    exact_zero = not rows or all(ar.mu(m) == 0 or not ar.kernels[m]["C"] for m, _ in multiplicity)
    return {"exact_symbolic_terms_m_base_multiplicity": rows, "positions_with_multiplicity": sum(multiplicity.values()),
            "signed_sum_certificate": certificate(tuple(bounds), exact_zero),
            "positive_part_sum_certificate": certificate(tuple(positive), not positive[1]),
            "negative_part_sum_certificate": certificate(tuple(negative), not negative[1]),
            "individual_weight_sign_counts": dict(signs)}


def run_bank():
    ar = Arithmetic()
    assert N % 2 == 0 and N % P0 and ar.prime(P0) and all(N % p == 0 for p in ar.primes if 2 <= p < P0)
    assert Q == (N - 1) // ALPHA and ALPHA ** 4 == N and Z ** 4 == N and M ** 4 == N ** 3
    assert (A - 1) ** 16 < N ** 7 <= A ** 16
    b_hyp = integer_root(N, 8)
    b_orig_floor = integer_root(N, 64)
    b_original_ceil = b_orig_floor if b_orig_floor ** 64 == N else b_orig_floor + 1
    assert b_hyp == 10 and b_original_ceil == 2
    q_rows, families, direct_terms, pp_terms = {}, {}, [], []
    counts = Counter()
    for q in range(LEFT, RIGHT + 1):
        one, zero = resource(ar, N - q), resource(ar, N - P0 * q)
        q_prime, unit = ar.prime(q), gcd(q, N) == 1
        category, ss, nonss = classify(one, zero)
        cap = (N - Q - 1) // q
        cores = [e for e in range(1, cap + 1) if ar.mu(e) != 0 and gcd(e, N) == 1]
        row = {"q": q, "factor_multiset_q": list(ar.factor(q)), "q_prime_indicator": q_prime,
               "unit_N": unit, "core_cap_floor_actual": cap, "all_SF_unit_cores": cores,
               "n1_resource": one, "n0_resource": zero, "category": category, "SS": ss,
               "structural_nonSS": nonss, "coordinates_by_e": {}, "all_core_rows": []}
        counts["q_positions"] += 1
        counts["q_prime"] += q_prime
        counts["q_unit"] += unit
        counts["q_unit_structural_nonSS"] += unit and nonss
        counts[f"all_q_resource_category_{category}"] += 1
        counts["all_q_SS"] += ss
        for e in cores:
            m, target = e * q, axis(ar, N - e * q)
            assert m <= N - Q - 1 and target["n"] > Q
            eligible = unit and nonss and e > P0
            theta_selected = eligible and q_prime and bool(target["theta_log_base"])
            raw_selected = eligible and q_prime and bool(target["raw_log_base"])
            original_theta = unit and e > P0 and q_prime and bool(target["theta_log_base"])
            if original_theta:
                counts[f"all_original_theta_{category}"] += 1
                if category == "S":
                    counts["all_original_theta_SS" if ss else "all_original_theta_nonSS"] += 1
            data = {"e": e, "mu_e": ar.mu(e), "m": m, "mu_m": ar.mu(m),
                    "target_axis": target, "structural_selected_before_q_and_target_prime_masks": eligible,
                    "q_prime_indicator": q_prime, "theta_selected": theta_selected,
                    "raw_selected": raw_selected, "proper_power_selected": raw_selected and target["proper_power"],
                    "universal_C_literal": UNIVERSAL_C,
                    "original_fronts_retained": True, "kernel_ref": None,
                    "kernel_status": "LITERAL_UNEVALUATED_OUTSIDE_SELECTED_RAW_MEASURE",
                    "literal_selected_theta_term_zero": not theta_selected,
                    "literal_selected_raw_term_zero": not raw_selected}
            if e <= P0:
                data["small_core_exception"] = "e1" if e == 1 else "e3_anchor"
            if eligible:
                coords = coordinate(ar, q, e, one, zero, b_hyp)
                row["coordinates_by_e"][e] = coords
                key = f"{coords['tag']}:{e}:{coords['a1']}:{coords['b0']}"
                data["family_ref"] = key
                family = families.setdefault(key, {k: coords[k] for k in (
                    "tag", "e", "a1", "b0", "x0", "y0_signed", "inverse_p0a1_mod_b0", "q_intercept",
                    "C_bal", "stratum", "source_t_interval_before_factor_selectors", "source_t_count",
                    "outer_plus1_upper", "window_t_interval_before_factor_selectors", "window_t_count")})
                family.setdefault("encoded_labels_q_e_t", []).append([q, e, coords["t_signed"]])
                counts["structural_labels_before_q_target_masks"] += 1
                counts[f"structural_{coords['tag']}_{coords['stratum']}"] += 1
                if q_prime:
                    assert gcd(m, N) == 1 and e < q and q > A and ar.mu(m) == -ar.mu(e)
                if raw_selected:
                    value = ar.kernel(m)
                    expected = ar.mangoldt_vector(e)
                    add_vector(expected, value["W"], Fraction(-ar.mu(e)))
                    assert value["C"] == expected
                    assert value["Ua"] == {p: -c for p, c in ar.mangoldt_vector(e).items()}
                    data["kernel_ref"] = str(m)
                    data["kernel_status"] = "NEW_ACTIVE_PHYSICAL_KERNEL"
                    data["F1_only_under_q_prime_verified"] = True
                    base = target["raw_log_base"]
                    weight, zero_weight = ar.weighted_bounds(m, base)
                    data["raw_sourceBracket_certificate"] = certificate(weight, zero_weight)
                    if theta_selected:
                        direct_terms.append([q, e, m, base, coords["tag"], coords["stratum"],
                                             one["Omega"], zero["Omega"], ar.mu(e)])
                        data["theta_sourceBracket_certificate"] = data["raw_sourceBracket_certificate"]
                    else:
                        assert target["proper_power"] and ar.mu(target["n"]) == 0
                        pp_terms.append([q, e, m, base, coords["tag"], coords["stratum"],
                                         one["Omega"], zero["Omega"], ar.mu(e)])
                counts["theta_nonSS_demands"] += theta_selected
                counts["raw_nonSS_axes"] += raw_selected
                counts["selected_properpowers"] += bool(raw_selected and target["proper_power"])
            counts["all_SF_unit_core_axes"] += 1
            counts["all_target_properpowers_before_masks"] += target["proper_power"]
            row["all_core_rows"].append(data)
        q_rows[q] = row
    assert counts["q_positions"] == 1001 and len(q_rows) == 1001
    assert counts["all_original_theta_S"] == counts["all_original_theta_SS"] + counts["all_original_theta_nonSS"]
    assert counts["all_original_theta_nonSS"] == counts["theta_nonSS_demands"]
    decoded = {key: decode_family(ar, value, q_rows) for key, value in sorted(families.items())}
    structural_encoded = sorted([q, e, c["t_signed"], c["tag"], c["a1"], c["b0"]]
                                for q, row in q_rows.items() for e, c in row["coordinates_by_e"].items())
    structural_decoded = sorted([q, e, t, family["tag"], family["a1"], family["b0"]]
                                for family in decoded.values() for q, e, t in family["decoded_labels_q_e_t"])
    assert structural_encoded == structural_decoded and len(structural_encoded) == counts["structural_labels_before_q_target_masks"]
    reindexed_theta, reindexed_pp = [], []
    for family in decoded.values():
        for q, e, _ in family["decoded_labels_q_e_t"]:
            row = q_rows[q]
            target = axis(ar, N - e * q)
            if not row["q_prime_indicator"] or not target["raw_log_base"]:
                continue
            entry = [q, e, e * q, target["raw_log_base"], family["tag"], family["stratum"],
                     row["n1_resource"]["Omega"], row["n0_resource"]["Omega"], ar.mu(e)]
            (reindexed_theta if target["theta_log_base"] else reindexed_pp).append(entry)
    assert sorted(direct_terms) == sorted(reindexed_theta) and sorted(pp_terms) == sorted(reindexed_pp)
    physical = {}
    def merge(m, role, label):
        entry = physical.setdefault(m, {"m": m, "first_axis_n": N - m, "roles": [], "labels": []})
        if role not in entry["roles"]:
            entry["roles"].append(role)
        if label not in entry["labels"]:
            entry["labels"].append(label)
    for q, e, m, base, tag, *_ in direct_terms + pp_terms:
        merge(m, "theta_demand" if ar.prime(N - m) else "raw_properpower_demand", f"q={q},e={e},tag={tag}")
    reciprocal_terms, reciprocal_rows, zero_m0 = [], [], []
    for q, row in q_rows.items():
        if not (row["q_prime_indicator"] and row["unit_N"] and row["structural_nonSS"] and row["coordinates_by_e"]):
            continue
        m1, m0 = N - q, N - P0 * q
        merge(m1, "reciprocal_m1_existing_resource_once", f"q={q}")
        merge(m0, "reciprocal_m0_literal_zero_raw_axis", f"q={q}")
        assert axis(ar, P0 * q)["raw_log_base"] is None
        zero_m0.append(m0)
        entry = {"q": q, "m1": m1, "first_axis_n": q, "mu_m1": ar.mu(m1),
                 "factor_multiset_m1": list(ar.factor(m1)), "Omega_m1": len(ar.factor(m1)),
                 "shared_structural_e_labels": sorted(row["coordinates_by_e"]),
                 "physically_counted_once": True, "kernel_ref": None}
        if ar.mu(m1) == 0:
            entry.update({"literal_C": "0", "sourceBracket_certificate": certificate((0, 0), True),
                          "kernel_status": "LITERAL_ZERO_BY_MU_M1_NO_FAKE_W"})
        else:
            value = ar.kernel(m1)
            entry.update({"kernel_ref": str(m1), "kernel_status": "NEW_UNIQUE_ACTIVE_M1_KERNEL"})
            h1, r1 = row["n1_resource"]["h_full_cofactor"], row["n1_resource"]["r_largest_prime"]
            guard = h1 <= A < r1
            entry["head_factorization_guard_h1_le_a_lt_r1"] = guard
            if guard:
                expected = ar.mangoldt_vector(h1)
                add_vector(expected, value["W"], Fraction(-ar.mu(h1)))
                assert value["C"] == expected
                entry["C_equals_Lambda_h1_minus_mu_h1_W_only_under_guard"] = True
            weight, exact_zero = ar.weighted_bounds(m1, q)
            entry["sourceBracket_certificate"] = certificate(weight, exact_zero)
        reciprocal_terms.append((m1, q))
        reciprocal_rows.append(entry)
    assert len(reciprocal_rows) == len({row["m1"] for row in reciprocal_rows})
    assert len({item[2] for item in direct_terms + pp_terms}) == len(direct_terms) + len(pp_terms)
    for m, entry in physical.items():
        if m in ar.kernels:
            entry["kernel_ref"] = str(m)
        elif m in zero_m0:
            entry["literal_weighted_term"] = "0"
            entry["zero_reason"] = "raw_Lambda_N(p0*q)=theta_N(p0*q)=0_for_prime_q_distinct_p0"
        else:
            assert ar.mu(m) == 0
            entry["literal_C"] = "0"
            entry["zero_reason"] = "mu_m=0_no_W_evaluation"
    assert set(ar.kernels) <= set(physical)
    aggregates = {}
    raw_terms = direct_terms + pp_terms
    for mode, entries in (("theta", direct_terms), ("raw", raw_terms), ("properpower", pp_terms)):
        groups = {"ALL": entries}
        for tag in ("D", "P"):
            groups[tag] = [v for v in entries if v[4] == tag]
            for stratum in ("SHORT", "MEDIUM", "LONG"):
                groups[f"{tag}:{stratum}"] = [v for v in entries if v[4:6] == [tag, stratum]]
        for mu in (-1, 1):
            groups[f"mu_e={mu}"] = [v for v in entries if v[8] == mu]
        for ranks in sorted({(v[6], v[7]) for v in entries}):
            groups[f"ranks={ranks[0]},{ranks[1]}"] = [v for v in entries if (v[6], v[7]) == ranks]
        aggregates[mode] = {key: terms_sum(ar, [(v[2], v[3]) for v in values]) for key, values in groups.items()}
    raw_map = Counter((v[2], v[3]) for v in raw_terms)
    assert raw_map == Counter((v[2], v[3]) for v in direct_terms) + Counter((v[2], v[3]) for v in pp_terms)
    raw_bounds = aggregates["raw"]["ALL"]["signed_sum_certificate"]
    th_bounds = aggregates["theta"]["ALL"]["signed_sum_certificate"]
    pp_bounds = aggregates["properpower"]["ALL"]["signed_sum_certificate"]
    assert all(int(raw_bounds[k]) == int(th_bounds[k]) + int(pp_bounds[k]) for k in ("lower_scaled", "upper_scaled"))
    reciprocal_sum = terms_sum(ar, reciprocal_terms)
    # These are literal diagnostics, not a capacity subtraction or a ledger payment.
    physical_union_terms = sorted(set((v[2], v[3]) for v in raw_terms) | set(reciprocal_terms))
    union_sum = terms_sum(ar, physical_union_terms)
    falsifiers = {}
    def example(name, values):
        falsifiers[name] = {"status": "COUNTEREXAMPLE" if values else "NO_COUNTEREXAMPLE_IN_WINDOW",
                            "first_example": values[0] if values else None, "finite_only": True}
    repeated = [{"q": q, "axis": j, "n": res["n"], "h": res["h_full_cofactor"],
                 "r": res["r_largest_prime"], "gcd_h_r": res["gcd_h_r"], "multiset": res["factor_multiset"]}
                for q, row in q_rows.items() if row["unit_N"] and row["structural_nonSS"]
                for j, res in ((1, row["n1_resource"]), (P0, row["n0_resource"])) if res["gcd_h_r"] > 1]
    example("universal_gcd_h_r_equals_1", repeated)
    p_four, long_actual = [], []
    for v in direct_terms:
        q, e = v[:2]
        c = q_rows[q]["coordinates_by_e"][e]
        if c["tag"] == "P" and (not ar.prime(c["x"]) or not ar.prime(c["y"])):
            p_four.append({"q": q, "e": e, "four_values_q_ne_x_y": [q, N-e*q, c["x"], c["y"]],
                           "x_prime": ar.prime(c["x"]), "y_prime": ar.prime(c["y"]), "a1": c["a1"], "b0": c["b0"]})
        if c["C_bal_squared"] > N:
            long_actual.append({"q": q, "e": e, "tag": c["tag"], "C_bal": c["C_bal"], "C_bal_squared": c["C_bal_squared"]})
    example("four_divided_forms_prime_in_P_actual_theta_demand", p_four)
    example("balanced_conductor_le_sqrtN_actual_theta_demand", long_actual)
    example("triprime_reciprocal_necessarily_favourable_negative_bracket", [row for row in reciprocal_rows
            if row["Omega_m1"] == 3 and row["mu_m1"] != 0
            and row["sourceBracket_certificate"]["sign"] in ("POSITIVE", "ZERO")])
    example("repeated_prime_reciprocal_nonzero_capacity", [row for row in reciprocal_rows if row["mu_m1"] == 0])
    demand_labels = {}
    for q, e, *_ in direct_terms:
        demand_labels.setdefault(q, []).append(e)
    example("each_e_tag_supplies_a_fresh_m1_actual_theta_labels", [
        {"q": q, "m1": N-q, "two_actual_theta_e_labels": labels[:2], "unique_physical_count": 1}
        for q, labels in sorted(demand_labels.items()) if len(labels) >= 2])
    short_count = sum(c["stratum"] == "SHORT" for row in q_rows.values() for c in row["coordinates_by_e"].values())
    assert short_count == 0
    log_n = ar.log_bounds(N)
    assert log_n[1] < (10 ** 24) * SCALE and log_n[1] < (10 ** 40) * SCALE
    h8 = harmonic(ar)
    counts["new_physical_kernels"] = len(ar.kernels)
    counts["physical_union_vertices"] = len(physical)
    counts["unique_m1_vertices"] = len(reciprocal_rows)
    counts["zero_m0_vertices"] = len(zero_m0)
    counts["literal_zero_m1_mu0_vertices"] = sum(row["mu_m1"] == 0 for row in reciprocal_rows)
    counts["inverse_families"] = len(decoded)
    sign_totals = Counter()
    for kernel in ar.kernels.values():
        for field in ("C_certificate", "W_kernel_certificate", "D_certificate"):
            sign_totals[kernel["record"][field]["sign"]] += 1
    return {"round": 19, "role": 6, "node": "14.4", "status": "PASS_NEW_FINITE_IDENTITIES_ONLY",
            "N": N, "window": [LEFT, RIGHT], "all_1001_integer_positions": True,
            "parameters": {"alpha": ALPHA, "a": A, "Q": Q, "M": M, "p0": P0, "Z": Z},
            "thresholds": {"B_original_ceil_N_1_over_64": b_original_ceil, "B_hyp_floor_N_1_over_8": b_hyp,
                           "T_hyp_floor_N_1_over_8": b_hyp, "B_test": B_TEST,
                           "source_D_short_structurally_empty": True, "all_balanced_short_count": short_count},
            "counts": dict(counts), "all_q_catalog": list(q_rows.values()),
            "all_tagged_families_and_independent_window_decodes": decoded,
            "H4_theta_direct_terms": direct_terms, "H4_raw_properpower_direct_terms": pp_terms,
            "H4_exact_support_reindex_verified_theta_and_raw": True,
            "raw_equals_theta_plus_properpower_exact_terms_and_bounds": True,
            "literal_signed_prices_by_channel_stratum_mu_and_rank": aggregates,
            "unique_physical_union_catalog": {str(m): row for m, row in sorted(physical.items())},
            "reciprocal_m1_physically_once": reciprocal_rows,
            "reciprocal_signed_diagnostic_no_capacity_credit": reciprocal_sum,
            "merged_union_signed_diagnostic_no_ledger_payment": union_sum,
            "physical_kernels_new_only": {str(m): value["record"] for m, value in sorted(ar.kernels.items())},
            "kernel_sign_positions_counts": dict(sign_totals), "finite_H8": h8,
            "strict_log_catalog": ar.log_catalog(), "falsifiers": falsifiers,
            "source_onset_logN_10power24_verified": False, "written_rank3_onset_logN_10power40_verified": False,
            "logN_upper_certificate_scaled": str(log_n[1]), "dyadic_bits": BITS,
            "analytic_H7_H9_or_global_DN_bounds_applied": False,
            "all_old_banks_Lean_PDF_preflights_executed": False,
            "no_floats_no_assumed_signs_no_raw_mu2_no_fake_zero_kernels": True,
            "victory": False}
