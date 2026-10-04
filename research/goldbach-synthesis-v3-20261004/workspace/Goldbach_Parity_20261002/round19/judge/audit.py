"""Independent Judge19, closed until the separate reviewed root gate.

Reads frozen stored data and integer/rational encodings, then compiles only
fresh new Lean modules. No producer imports, factorization, primality test,
W/D evaluation, logarithm or new logarithmic sign is computed here.
"""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import hashlib
import gzip
import json
import os
import re
import subprocess
import traceback
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
from math import gcd, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SKIP = {".lake", ".git", ".arbor", "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache"}
ACTIVE_STAGE = "not_started"


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def load(path):
    def invalid_constant(value):
        raise ValueError("Non-finite JSON number: " + value)
    return json.loads(Path(path).read_text(encoding="utf-8-sig"), parse_constant=invalid_constant)


def exclusive(path, obj):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=2) + "\n")


def emit(stage, **values):
    print(json.dumps({"stage": stage, **values}, ensure_ascii=False), flush=True)


def bound(relative):
    p = (BASE / relative).resolve()
    assert p.is_relative_to(BASE.resolve()) and p.is_file(), ("unsafe_or_missing_input", relative)
    return p


def verify(bindings):
    for relative, digest in bindings.items():
        assert sha(bound(relative)) == digest, ("input_changed", relative)


def input_check(inputs):
    verify(inputs["final_input_sha256"])
    verify(inputs["historical_dependencies_sha256"])
    for original, digest in inputs["original_documents_sha256"].items():
        assert sha(original) == digest, ("original_document_changed", original)
    assert sha(inputs["lean_executable"]) == inputs["lean_sha256"]
    assert sha(inputs["python_executable"]) == inputs["python_sha256"]
    assert sha(inputs["mathlib_HEAD_path"]) == inputs["mathlib_HEAD_sha256"]
    assert Path(inputs["mathlib_HEAD_path"]).read_text(encoding="utf-8").strip() == inputs["mathlib_commit"]
    for name, digest in inputs["judge_code_sha256"].items():
        assert sha(HERE / name) == digest, ("judge_source_changed", name)
    for name, capture in inputs["PREEXEC_captures"].items():
        assert sha(capture["original"]) == sha(capture["snapshot"]) == capture["sha256"], ("PREEXEC_capture_changed", name)


def preservation():
    registry = load(ROUND / "previous_artifacts_sha256.json")
    assert registry["file_count"] == len(registry["sha256"]) == 1361
    verify(registry["sha256"])
    actual = set()
    for folder, dirs, files in os.walk(BASE):
        dirs[:] = [d for d in dirs if d not in SKIP and not
                   (re.fullmatch(r"round\d+", d) and int(d[5:]) >= 19)]
        for name in files:
            p = Path(folder) / name
            if p != BASE / "REPORT.md":
                actual.add(p.relative_to(BASE).as_posix())
    assert actual == set(registry["sha256"]), {
        "added": sorted(actual - set(registry["sha256"])),
        "removed": sorted(set(registry["sha256"]) - actual)}
    return {"exact_protected_inventory": 1361, "hashes_preserved": True,
            "old_scripts_or_Lean_or_PDF_executed": False}


def certificate_rows(value, pointer=""):
    assert not isinstance(value, float), ("float_in_stored_bank", pointer)
    if isinstance(value, dict):
        if {"whole_box_sign", "whole_box_enclosure", "endpoint_certificates"} <= value.keys():
            box = value["whole_box_enclosure"]
            lo, hi = int(box["lower_scaled"]), int(box["upper_scaled"])
            endpoints = [item["certificate"] for item in value["endpoint_certificates"]]
            assert [Fraction(item) for item in value["acquired_S_box"]] == [Fraction(2541, 1536), Fraction(11011, 6144)]
            assert [Fraction(item["S"]) for item in value["endpoint_certificates"]] == [Fraction(item) for item in value["acquired_S_box"]]
            assert lo == min(int(item["lower_scaled"]) for item in endpoints)
            assert hi == max(int(item["upper_scaled"]) for item in endpoints)
            label = value["whole_box_sign"]
            assert label in {"POSITIVE", "NEGATIVE", "ZERO", "PARAMETER_BOX_MAY_CHANGE_SIGN"}
            assert ((label == "POSITIVE" and lo > 0) or (label == "NEGATIVE" and hi < 0) or
                    (label == "ZERO" and lo == hi == 0) or
                    (label == "PARAMETER_BOX_MAY_CHANGE_SIGN" and lo <= 0 <= hi)), pointer
        if {"sign", "lower_scaled", "upper_scaled", "dyadic_bits"} <= value.keys():
            lo, hi, sign = int(value["lower_scaled"]), int(value["upper_scaled"]), value["sign"]
            assert isinstance(value["dyadic_bits"], int) and value["dyadic_bits"] > 0
            assert lo <= hi and sign in {"POSITIVE", "NEGATIVE", "ZERO"}, pointer
            assert ((sign == "POSITIVE" and lo > 0) or
                    (sign == "NEGATIVE" and hi < 0) or
                    (sign == "ZERO" and lo == hi == 0)), ("stored_encoding_inconsistent", pointer)
            encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
            yield {"json_pointer": pointer, "stored_sign_label": sign,
                   "stored_certificate_sha256": hashlib.sha256(encoded).hexdigest()}
        elif {"sign", "lower", "upper"} <= value.keys():
            lo, hi, sign = Fraction(value["lower"]), Fraction(value["upper"]), value["sign"]
            assert lo <= hi and sign in {"POSITIVE", "NEGATIVE", "ZERO"}, pointer
            assert ((sign == "POSITIVE" and lo > 0) or
                    (sign == "NEGATIVE" and hi < 0) or
                    (sign == "ZERO" and lo == hi == 0)), ("stored_encoding_inconsistent", pointer)
            encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
            yield {"json_pointer": pointer, "stored_sign_label": sign,
                   "stored_certificate_sha256": hashlib.sha256(encoded).hexdigest()}
        for key, item in value.items():
            escaped = str(key).replace("~", "~0").replace("/", "~1")
            yield from certificate_rows(item, pointer + "/" + escaped)
    elif isinstance(value, list):
        for index, item in enumerate(value):
            yield from certificate_rows(item, pointer + "/" + str(index))


def stored_numeric(inputs):
    results = {}
    for bank, specification in inputs["numeric_banks"].items():
        data = load(bound(specification["result"]))
        receipt = load(bound(specification["canonical_receipt"]))
        assert receipt[specification["exit_code_field"]] == 0
        assert sha(bound(specification["result"])) == receipt[specification["result_sha256_field"]]
        final = load(bound(specification["final_receipt"]))
        for relative, binding in final[specification["bindings_field"]].items():
            digest = binding["sha256"] if isinstance(binding, dict) else binding
            root = ROUND if specification["bindings_relative_to"] == "round19" else BASE
            assert sha(root / relative) == digest, ("numeric_FINAL_binding_changed", bank, relative)
        for field, expected in specification["required_stored_fields"].items():
            assert data[field] == expected, ("stored_bank_contract_changed", bank, field)
        rows = list(certificate_rows(data))
        counts = Counter(row["stored_sign_label"] for row in rows)
        results[bank] = {"result_sha256": sha(bound(specification["result"])),
                         "actual_exit_code": receipt[specification["exit_code_field"]],
                         "stored_certificate_positions_including_repeated_JSON_fields": len(rows),
                         "stored_sign_labels": dict(counts), "stored_certificate_index": rows,
                         "new_logarithmic_signs_computed": False,
                         "producer_kernel_log_or_replay_executed": False}
    return results


def stored_resource(resource):
    factors = resource["factor_multiset"]
    assert all(isinstance(p, int) and p >= 2 for p in factors)
    assert factors == sorted(factors) and prod(factors) == resource["n"]
    assert len(factors) == resource["Omega"]
    assert resource["r_largest_prime"] == factors[-1]
    assert resource["h_full_cofactor"] * factors[-1] == resource["n"]
    assert resource["h_factor_multiset"] == factors[:-1]
    assert resource["gcd_h_r"] == gcd(resource["h_full_cofactor"], factors[-1])
    assert resource["least_prime"] == factors[0]
    assert resource["minfac_quotient"] * factors[0] == resource["n"]


def nonss_stored_integer_audit(inputs):
    data = load(bound(inputs["numeric_banks"]["nonss"]["result"]))
    assert data["N"] == 100000000 and data["window"] == [1600100, 1601100]
    n, p0, qcap, source_b = data["N"], data["parameters"]["p0"], data["parameters"]["Q"], data["thresholds"]["B_hyp_floor_N_1_over_8"]
    rows = data["all_q_catalog"]
    assert [row["q"] for row in rows] == list(range(1600100, 1601101))
    encoded = []
    for row in rows:
        q = row["q"]
        one, zero = row["n1_resource"], row["n0_resource"]
        assert one["n"] == n - q and zero["n"] == n - p0 * q
        stored_resource(one)
        stored_resource(zero)
        assert prod(row["factor_multiset_q"]) == q
        assert row["q_prime_indicator"] == (row["factor_multiset_q"] == [q])
        assert row["unit_N"] == (gcd(q, n) == 1)
        assert row["core_cap_floor_actual"] == (n - qcap - 1) // q
        for e_text, c in row["coordinates_by_e"].items():
            e = int(e_text)
            h1, h0 = one["h_full_cofactor"], zero["h_full_cofactor"]
            r1, r0 = one["r_largest_prime"], zero["r_largest_prime"]
            direct = h1 * h0 <= r1 * r0
            assert c["tag"] == ("D" if direct else "P")
            a, b, x, y = (h1, h0, r1, r0) if direct else (r1, r0, h1, h0)
            assert [c["a1"], c["b0"], c["x"], c["y"]] == [a, b, x, y]
            assert gcd(one["n"], zero["n"]) == gcd(p0 * a, b) == 1
            assert c["C_bal"] == a * b == min(h1 * h0, r1 * r0)
            assert c["C_bal_squared"] == (a * b) ** 2 <= one["n"] * zero["n"] < n * n
            assert a * b < n and p0 * a * x - b * y == (p0 - 1) * n
            assert 0 <= c["x0"] < b
            assert p0 * a * c["x0"] - b * c["y0_signed"] == (p0 - 1) * n
            t = c["t_signed"]
            assert x == c["x0"] + b * t and y == c["y0_signed"] + p0 * a * t
            assert q == n - a * x == c["q_intercept"] - a * b * t
            assert e > p0 and e in row["all_SF_unit_cores"] and e * q <= n - qcap - 1
            assert c["stratum"] == ("SHORT" if a * b <= source_b else
                                      "MEDIUM" if (a * b) ** 2 <= n else "LONG")
            lo, hi = c["source_t_interval_before_factor_selectors"]
            wlo, whi = c["window_t_interval_before_factor_selectors"]
            assert lo <= t <= hi and wlo <= t <= whi
            assert c["source_t_count"] == max(0, hi - lo + 1) <= n // (e * a * b) + 1
            assert c["window_t_count"] == max(0, whi - wlo + 1) <= 1000 // (a * b) + 1
            encoded.append([q, e, t, c["tag"], a, b])
    decoded = []
    families = data["all_tagged_families_and_independent_window_decodes"]
    for family in families.values():
        assert sorted(family["encoded_labels_q_e_t"]) == sorted(family["decoded_labels_q_e_t"])
        for q, e, t in family["decoded_labels_q_e_t"]:
            decoded.append([q, e, t, family["tag"], family["a1"], family["b0"]])
        lo, hi = family["window_t_interval_before_factor_selectors"]
        candidates = family["all_window_t_candidates_before_selectors"]
        assert [row[0] for row in candidates] == list(range(lo, hi + 1))
        for t, q, x, y, _, _ in candidates:
            assert x == family["x0"] + family["b0"] * t
            assert y == family["y0_signed"] + p0 * family["a1"] * t
            assert q == n - family["a1"] * x
    assert sorted(encoded) == sorted(decoded)
    assert len(encoded) == data["counts"]["structural_labels_before_q_target_masks"] == 5120
    recips = data["reciprocal_m1_physically_once"]
    assert len(recips) == len({row["m1"] for row in recips}) == 48
    for row in recips:
        assert row["m1"] == n - row["q"] and row["first_axis_n"] == row["q"]
        factors = row["factor_multiset_m1"]
        assert prod(factors) == row["m1"] and len(factors) == row["Omega_m1"]
        mu = 0 if len(set(factors)) != len(factors) else (-1) ** len(factors)
        assert row["mu_m1"] == mu and row["physically_counted_once"] is True
        if mu == 0:
            assert row["kernel_ref"] is None and row["literal_C"] == "0"
            assert row["sourceBracket_certificate"]["exact_zero"] is True
    union = data["unique_physical_union_catalog"]
    assert len(union) == data["counts"]["physical_union_vertices"] == 220
    for m_text, vertex in union.items():
        assert int(m_text) == vertex["m"] and vertex["first_axis_n"] == n - int(m_text)
    h8 = data["finite_H8"]
    primes = h8["all_primes_through_Btest_including_2_5"]
    products = h8["uncut_products_upper_triangle_by_prime_index"]
    assert len(primes) == len(products) == 309 and primes == sorted(set(primes))
    pair_count = 0
    catalog = hashlib.sha256()
    for index, p in enumerate(primes):
        assert products[index] == [p * q for q in primes[index:]]
        for q in primes[index:]:
            catalog.update(f"{p},{q},{p*q}\n".encode("ascii"))
            pair_count += 1
    assert h8["uncut_all_diagonal_p_squared"] == [p * p for p in primes]
    assert pair_count == h8["uncut_pair_count"] == 47895
    assert catalog.hexdigest() == h8["uncut_pair_catalog_sha256_ascii_p_q_pq_lines"]
    s1, s2 = Fraction(h8["S1"]), Fraction(h8["S2"])
    pair_mass, whole = Fraction(h8["direct_pair_sum"]), Fraction(h8["uncut_H2"])
    assert pair_mass == (s1 * s1 + s2) / 2 and whole == s1 + pair_mass
    assert Fraction(h8["cut_harmonic"]) <= whole
    for h, factors in h8["all_cut_h_2_through_Btest_Omega1or2"]:
        assert 2 <= h <= h8["B_test"] and len(factors) in (1, 2) and prod(factors) == h
    return {"all_q_integer_positions": len(rows), "stored_encoded_and_decoded_labels": len(encoded),
            "unique_m1": len(recips), "unique_physical_union": len(union), "H8_pairs_with_diagonal": pair_count,
            "stored_H8_rational_identity_checked": True, "fresh_primality_or_factorization_called": False,
            "kernel_log_or_logarithmic_sign_computed": False, "capacity_or_ledger_payment_inferred": False}


def add_coefficients(target, source, coefficient=Fraction(1)):
    for base, value in source.items():
        updated = target.get(base, Fraction(0)) + coefficient * value
        if updated:
            target[base] = updated
        elif base in target:
            del target[base]


def coefficient_digest(vector):
    digest = hashlib.sha256()
    for base, value in sorted(vector.items()):
        digest.update(f"{base}:{value.numerator}/{value.denominator}\n".encode("ascii"))
    return digest.hexdigest()


def known_factor_divisors(factors):
    """Algebraic products of already supplied factors, no trial division."""
    values = [(1, 1)]
    for p, exponent in sorted(Counter(factors).items()):
        old = list(values)
        power = 1
        for k in range(1, exponent + 1):
            power *= p
            values.extend((d * power, -mu if k == 1 else 0) for d, mu in old)
    return sorted(values)


def known_phi(n, factors):
    assert prod(factors) == n
    value = n
    for p in set(factors):
        value = value // p * (p - 1)
    return value


def rank_stored_integer_audit(inputs):
    data = load(bound(inputs["numeric_banks"]["rank"]["result"]))
    n, a, h, p = data["N"], data["fixed_parameters"]["a"], data["fixed_parameters"]["h"], data["fixed_parameters"]["P"]
    assert (n, a, h, p) == (100000000, 3163, 39, 1771)
    assert data["candidate_domain_left_exclusive_right_inclusive"] == [12000000, 24000000]
    bitmap = data["candidate_full_domain_prime_bitmap"]
    bitmap_path = Path(bitmap["path"])
    assert bitmap_path.resolve().is_relative_to((ROUND / "role6_rank").resolve())
    assert sha(bitmap_path) == bitmap["sha256"]
    packed = gzip.decompress(bitmap_path.read_bytes())
    width, start = 12000000, 12000001
    assert len(packed) == (width + 7) // 8 and hashlib.sha256(packed).hexdigest() == bitmap["uncompressed_sha256"]
    assert bitmap["integer_axes"] == width and bitmap["left_exclusive"] == 12000000 and bitmap["right_inclusive"] == 24000000
    assert sum(byte.bit_count() for byte in packed) == bitmap["full_prime_count"] == data["counts"]["all_candidate_primes"]
    def stored_prime_bit(j):
        index = j - start
        assert 0 <= index < width
        return bool((packed[index // 8] >> (index % 8)) & 1)
    base = bitmap["all_base_primes_through_sqrt_right"]
    assert base == sorted(set(base))
    expected_pairs = sorted([c, r, c * r] for c in base for r in base
                            if c < r and c * r <= a and gcd(c * r, n) == 1)
    assert data["all_prime_pairs_c_lt_r_unit_N_cr_le_a"] == expected_pairs
    fibers = data["all_conductor_fibers"]
    assert [[fiber["c"], fiber["r"], fiber["d"]] for fiber in fibers] == expected_pairs
    assert len(fibers) == data["counts"]["fibers"]
    assert sum(fiber["A_beta"] == 0 for fiber in fibers) == data["counts"]["fibers_A0"]
    proper_rows = data["all_candidate_properpowers_value_primebase_exponent_including_nonunits"]
    assert proper_rows == sorted(proper_rows) and len({row[0] for row in proper_rows}) == len(proper_rows)
    proper = {}
    for value, primebase, exponent in proper_rows:
        assert primebase in base and exponent >= 2 and value == primebase ** exponent
        assert 12000000 < value <= 24000000 and not stored_prime_bit(value)
        proper[value] = (primebase, exponent)
    assert len(proper) == data["counts"]["all_candidate_properpowers"]
    expected_reference_names = ["U0", "U", "Uprime", "Us2", "Usprime2", "Us17", "Usprime17"]
    n_factors = [2] * 8 + [5] * 8
    assert prod(n_factors) == n and gcd(p, n * h) == 1
    expected_module_rows = {"2": {}, "17": {}}
    all_beta = {}
    integer_axes, prime_member_positions, proper_member_positions = 0, 0, 0
    for fiber in fibers:
        c, r, d = fiber["c"], fiber["r"], fiber["d"]
        assert d == c * r and c < r and d <= a and gcd(d, n) == 1
        blo, bhi = fiber["b_interval_complete"]
        assert blo == -((-(n - 24000000)) // d) and bhi == -((-(n - 12000000)) // d) - 1
        length = max(0, bhi - blo + 1)
        nlo, nhi = n - d * bhi, n - d * blo
        assert fiber["L"] == length and fiber["real_j_interval"] == [nlo, nhi]
        assert fiber["X"] == nhi - nlo + 1 == d * (length - 1) + 1
        xwidth, pd = fiber["X"], p // gcd(p, d)
        assert fiber["P_d"] == pd > 1 and gcd(pd, n * h * d) == 1
        assert fiber["P_sharing_count"] == sum(d % ell == 0 for ell in (7, 11, 23))
        assert fiber["reference_mask_bit_names"] == expected_reference_names
        factors_by_reference = {"U0": n_factors + [3, 13], "U": n_factors + [3, 13, c, r],
                                "Uprime": n_factors + [3, 13, c, r]}
        for cutoff in (2, 17):
            supplied_small = [ell for ell in (c, r) if ell <= cutoff]
            for prefix in ("Us", "Usprime"):
                factors_by_reference[prefix + str(cutoff)] = n_factors + [3, 13] + supplied_small
        cards = fiber["reference_counts"]
        moduli = fiber["reference_unit_moduli"]
        for name in expected_reference_names:
            factors = factors_by_reference[name]
            modulus = prod(factors)
            assert moduli[name] == modulus
            ie_pair = fiber["reference_IE_counts"][name]
            complete = data["all_complete_original_IE_divisors_including_mu0"][str(modulus)]
            assert complete == [list(row) for row in known_factor_divisors(factors)]
            expected_counts = {}
            for count_kind, face in (("unit_count", 1), ("face_count", pd)):
                record = ie_pair[count_kind]
                assert record["modulus"] == modulus and record["face"] == face
                assert record["complete_divisors_ref"] == str(modulus) and record["L"] == length
                total = sum(mu * (bhi // (k * face) - (blo - 1) // (k * face)) for k, mu in complete)
                assert record["integer_count"] == total
                assert record["eta"] == sum(abs(mu) for _, mu in complete)
                assert Fraction(record["delta"]) == Fraction(known_phi(modulus, factors), modulus)
                expected_counts[count_kind] = total
            outside = "prime" in name
            expected_card = expected_counts["unit_count"] - expected_counts["face_count"] if outside else expected_counts["unit_count"]
            assert ie_pair["outside_face"] == outside and cards[name] == ie_pair["actual_reference_count"] == expected_card
        beta = {entry["b"]: entry for entry in fiber["all_beta_physical_witnesses"]}
        assert len(beta) == fiber["A_beta"] and fiber["A_beta"] <= min(cards.values())
        for b, entry in beta.items():
            fc, fr, s, q = entry["prime_factors_c_r_s_q"]
            assert [fc, fr] == [c, r] and c < r < s <= a < q and b == s * q
            assert c * r <= a and c * s <= a < r * s < q and c * r * s > a
            m, j = d * b, n - d * b
            assert blo <= b <= bhi and entry["m"] == m and entry["j"] == j
            assert data["fixed_parameters"]["M"] <= m and m + data["fixed_parameters"]["Q"] < n
            assert gcd(m, n) == 1 and m % p != 0 and entry["physical_mask_has_no_candidate_prime_filter"] is True
            assert entry["candidate_prime_indicator"] == stored_prime_bit(j)
            assert entry["candidate_properpower"] == (list(proper[j]) if j in proper else None)
            assert m not in all_beta
            all_beta[m] = {"d": d, "c": c, "r": r, "b": b, "j": j, "factors": [c, r, s, q]}
        primes = fiber["all_prime_member_rows_j_b_mask_beta"]
        powers = fiber["all_properpower_member_rows_j_b_mask_beta_base_exponent"]
        expected_prime_jb, expected_power_jb = [], []
        for b in range(blo, bhi + 1):
            j = n - d * b
            if stored_prime_bit(j):
                expected_prime_jb.append([j, b])
            elif j in proper:
                expected_power_jb.append([j, b])
        assert [row[:2] for row in primes] == expected_prime_jb
        assert [row[:2] for row in powers] == expected_power_jb
        bases = {measure: {name: {} for name in ["beta"] + expected_reference_names}
                 for measure in ("theta", "raw", "properpower")}
        for measure, members in (("theta", primes), ("properpower", powers)):
            for row in members:
                j, b, mask, is_beta = row[:4]
                assert is_beta == int(b in beta)
                selected = {name: gcd(b, moduli[name]) == 1 and
                            (b % pd != 0 if "prime" in name else True) for name in expected_reference_names}
                assert mask == sum(1 << index for index, name in enumerate(expected_reference_names) if selected[name])
                assert b in beta or not is_beta
                if b in beta:
                    assert all(selected.values())
                raw_base = j if measure == "theta" else row[4]
                if measure == "properpower":
                    assert row[4:6] == list(proper[j]) and j == row[4] ** row[5]
                if gcd(j, n) != 1:
                    continue
                for name, active in [("beta", bool(is_beta)), *selected.items()]:
                    if active:
                        bases[measure][name][raw_base] = bases[measure][name].get(raw_base, 0) + 1
                        bases["raw"][name][raw_base] = bases["raw"][name].get(raw_base, 0) + 1
        mass = fiber["A_beta"]
        rho = {name: Fraction(mass, cards[name]) if cards[name] else Fraction(0) for name in expected_reference_names}
        assert all(cards[name] != 0 or mass == 0 for name in expected_reference_names)
        assert {name: Fraction(value) for name, value in fiber["coefficients_A_over_J_empty_zero"].items()} == rho
        expressions = {"Gamma0": {"beta": Fraction(1), "U0": -rho["U0"]},
                       "Gamma_rank": {"beta": Fraction(1), "Uprime": -rho["Uprime"]},
                       "E_unit": {"U": rho["U"], "U0": -rho["U0"]},
                       "L_rank": {"Uprime": rho["Uprime"], "U": -rho["U"]},
                       "Pi": {"Uprime": rho["Uprime"], "U0": -rho["U0"]}}
        for cutoff in (2, 17):
            expressions["Pi_small_R" + str(cutoff)] = {"Usprime" + str(cutoff): rho["Usprime" + str(cutoff)], "U0": -rho["U0"]}
            expressions["large_unit_difference_R" + str(cutoff)] = {"Uprime": rho["Uprime"], "Usprime" + str(cutoff): -rho["Usprime" + str(cutoff)]}
        vectors = {measure: {} for measure in bases}
        for measure in bases:
            assert set(fiber["actual_components"][measure]) == set(expressions)
            for component, expression in expressions.items():
                actual = fiber["actual_components"][measure][component]
                expected_expression = {name: value for name, value in expression.items() if value}
                assert {name: Fraction(value) for name, value in actual["exact_basis_expression"].items()} == expected_expression
                vector = {}
                for name, value in expected_expression.items():
                    add_coefficients(vector, bases[measure][name], value)
                assert coefficient_digest(vector) == actual["exact_prime_log_vector_sha256"]
                assert actual["inner_certificate"]["exact_zero"] == (not vector)
                vectors[measure][component] = vector
            combined = dict(vectors[measure]["Gamma_rank"])
            add_coefficients(combined, vectors[measure]["Pi"])
            assert combined == vectors[measure]["Gamma0"]
            combined = dict(vectors[measure]["E_unit"])
            add_coefficients(combined, vectors[measure]["L_rank"])
            assert combined == vectors[measure]["Pi"]
        for component in expressions:
            split = dict(vectors["theta"][component])
            add_coefficients(split, vectors["properpower"][component])
            assert split == vectors["raw"][component]
        for multiplier_text, record in fiber["AP_interval_catalog_by_b_multiplier"].items():
            multiplier = int(multiplier_text)
            assert record["module"] == d * multiplier and record["residue_N_mod_module"] == n % (d * multiplier)
            assert record["real_interval_nlo_nhi"] == [nlo, nhi] and record["X"] == xwidth
            members = [index for index, row in enumerate(primes) if row[1] % multiplier == 0]
            assert record["prime_member_indices"] == members and record["unmasked_theta_count"] == len(members)
            multiplier_factors = [ell for ell in sorted(set([3, 13, c, r, 7, 11, 23])) if multiplier % ell == 0]
            assert prod(multiplier_factors) == multiplier
            assert Fraction(record["X_over_phi_module"]) == Fraction(xwidth, known_phi(d * multiplier, [c, r] + multiplier_factors))
            assert record["prime_divisors_of_N_exception_mass"] == 0 and nlo > 5
        delta0 = Fraction(known_phi(n * h, n_factors + [3, 13]), n * h)
        a0 = sum((Fraction(mu, known_phi(d * k, [c, r] + [ell for ell in (3, 13) if k % ell == 0]))
                  for k, mu in known_factor_divisors([3, 13])), Fraction(0))
        pd_factors = [ell for ell in (7, 11, 23) if pd % ell == 0]
        phi_pd = known_phi(pd, pd_factors)
        chi = Fraction(pd - phi_pd, phi_pd * (pd - 1))
        main_mass = Fraction(mass * xwidth, length) * a0 / delta0
        assert Fraction(fiber["a0"]) == a0 and Fraction(fiber["delta0"]) == delta0
        assert Fraction(fiber["M_d"]) == main_mass and Fraction(fiber["chi_Pd"]) == chi
        assert Fraction(fiber["Pi_principal_inner"]) == -main_mass * chi
        for cutoff in (2, 17):
            cut = fiber["two_R_cuts"][str(cutoff)]
            small = [ell for ell in (c, r) if ell <= cutoff]
            ds = prod(small)
            assert cut["R"] == cutoff and cut["is_source_R"] == (cutoff == 2)
            assert cut["d_s"] == ds and cut["H_s"] == n * h * ds
            radical_factors = sorted(set([3, 13] + small))
            es = prod(radical_factors)
            assert cut["e_s"] == es and cut["Q_R_exact_integer_level"] == h * p * max(a * cutoff, cutoff ** 4)
            delta_small = Fraction(known_phi(n * h * ds, n_factors + [3, 13] + small), n * h * ds)
            a_small = sum((Fraction(mu, known_phi(d * k, [c, r] + [ell for ell in radical_factors if k % ell == 0]))
                           for k, mu in known_factor_divisors(radical_factors)), Fraction(0))
            assert Fraction(cut["delta_s"]) == delta_small and Fraction(cut["a_s"]) == a_small
            assert a_small / delta_small == a0 / delta0
            for kind, factors, face in (("T0", [3, 13], 1), ("Ts", radical_factors, 1), ("TFs", radical_factors, pd)):
                expansions = cut["IE_AP_expansions"][kind]
                divisors = known_factor_divisors(factors)
                assert [(entry["k"], entry["mu"]) for entry in expansions] == divisors
                for entry in expansions:
                    k, mu = entry["k"], entry["mu"]
                    assert entry["AP_multiplier_ref"] == str(k * face)
                    fixed_t = prod(ell for ell in (3, 13) if k % ell == 0)
                    ks, fixed_f = k // fixed_t, fixed_t * face
                    assert ds % ks == 0 and gcd(ks, h) == 1 and h * p % fixed_f == 0
                    assert d * ks <= max(a * cutoff, cutoff ** 4)
                    module = d * k * face
                    assert module == fixed_f * d * ks <= cut["Q_R_exact_integer_level"]
                    recovered_factors = [c, r] + [ell for ell in (c, r) if ks % ell == 0]
                    assert prod(recovered_factors) == d * ks and all(recovered_factors.count(ell) in (1, 2) for ell in (c, r))
                    assert prod(ell for ell in (c, r) if recovered_factors.count(ell) == 2) == ks
                    representation = {"kind": kind, "R": cutoff, "d": d, "c": c, "r": r, "k": k,
                                      "k_s": ks, "t_divisor39": fixed_t, "P_d": pd, "face_multiplier": face,
                                      "fixed_f_divisor39P": fixed_f, "mu_k": mu, "module": module,
                                      "factor_recovery_d_ks_verified": True}
                    expected_module_rows[str(cutoff)].setdefault(str(module), []).append(representation)
            lost = cards["Usprime" + str(cutoff)] - cards["Uprime"]
            large = [ell for ell in (c, r) if ell > cutoff]
            plus1 = sum((Fraction(length, ell) + 1 for ell in large), Fraction(0))
            sharpened = Fraction(mass * lost, cards["Usprime" + str(cutoff)]) if cards["Usprime" + str(cutoff)] else Fraction(0)
            assert cut["lost_integer_count"] == lost >= 0 and cut["large_primes_removed"] == large
            assert Fraction(cut["large_unit_plus1_bound"]) == plus1 >= lost
            assert plus1 <= 2 * (Fraction(length, cutoff) + 1)
            assert Fraction(cut["K6_sharpened_A_lost_over_Jsprime"]) == sharpened
            assert Fraction(cut["normalization_rho_sprime"]) == rho["Usprime" + str(cutoff)]
            assert Fraction(cut["normalization_rho0"]) == rho["U0"]
            assert Fraction(cut["principal_r_sprime"]) == Fraction(mass, length) / delta_small / (1 - Fraction(1, pd))
            assert Fraction(cut["principal_r0"]) == Fraction(mass, length) / delta0
        integer_axes += length
        prime_member_positions += len(primes)
        proper_member_positions += len(powers)
    assert integer_axes == data["counts"]["all_integer_b_axes"]
    assert len(all_beta) == data["counts"]["physical_beta_images"]
    assert data["physical_beta_union_unique"] == {str(m): entry for m, entry in sorted(all_beta.items())}
    multiplicities = {}
    for cutoff_text, expected in expected_module_rows.items():
        actual = data["all_AP_modules_representations_level_and_multiplicity"][cutoff_text]
        assert actual["all_module_representations"] == expected
        maximum = max((len(rows) for rows in expected.values()), default=0)
        assert actual["distinct_modules"] == len(expected)
        assert actual["max_actual_representation_multiplicity"] == maximum <= 40 <= 64
        multiplicities[cutoff_text] = maximum
    return {"all_conductor_fibers": len(fibers), "all_integer_b_axes": integer_axes,
            "stored_bitmap_integer_axes": width, "stored_bitmap_one_bits": bitmap["full_prime_count"],
            "stored_prime_member_positions": prime_member_positions,
            "stored_properpower_member_positions": proper_member_positions,
            "unique_physical_beta_images": len(all_beta), "combined_AP_multiplicities_both_R": multiplicities,
            "K4_and_raw_theta_PP_exact_coefficient_maps_checked": True,
            "complete_IE_divisor_products_with_mu0_checked": True,
            "bitmap_not_resieved_and_primality_not_retested": True,
            "no_new_factorization_kernel_log_sign_or_S_evaluation": True,
            "finite_data_does_not_close_K14_K18_BV_Gamma_or_ledger": True}


def author_failures(inputs):
    records = []
    totals = Counter()
    for relative in inputs["author_build_ledgers"]:
        ledger = load(bound(relative))
        for row in ledger["attempts"]:
            capture = row.get("source_capture", row.get("source_snapshot", row.get("snapshot")))
            capture_digest = row.get("source_capture_sha256", row.get("snapshot_sha256"))
            assert capture and sha(capture) == capture_digest == row["source_sha256"]
            assert sha(row["log"]) == row["log_sha256"]
            text = Path(row["log"]).read_text(encoding="utf-8", errors="replace")
            errors = [line for line in text.splitlines() if "error:" in line]
            warnings = [line for line in text.splitlines() if "warning:" in line]
            records.append({"ledger": relative, "attempt": row["attempt"], "exit_code": row["exit_code"],
                            "source": row["source"], "source_snapshot": capture, "source_sha256": row["source_sha256"],
                            "log": row["log"], "log_sha256": row["log_sha256"],
                            "actual_error_lines": errors, "actual_warning_lines": warnings,
                            "failed_log_contains_sorryAx": row["exit_code"] != 0 and "sorryAx" in text,
                            "failed_declarations_accepted": False, "analytic_parity_failure_inferred": False})
            totals["invocations"] += 1
            totals["failures"] += row["exit_code"] != 0
            totals["invocations_with_warnings"] += bool(warnings)
    launcher_events = [{"relative_path": p, "record": load(bound(p))}
                       for p in inputs["author_launcher_failure_receipts"]]
    return {"actual_Lean_records": records, "totals": dict(totals),
            "distinct_pre_Lean_launcher_events": launcher_events,
            "mathematical_or_parity_failure_invented": False}


def declarations(source, specification):
    text = source.read_text(encoding="utf-8")
    stripped = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
    stripped = re.sub(r"--[^\n]*", "", stripped)
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|sorryAx|trustMe)\b", stripped)
    stripped = re.sub(r"^\s*@\[[^\]]*\]\s*", "", stripped, flags=re.M)
    ds = re.findall(r"^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|structure|instance)\s+([A-Za-z_][\w\u0080-\uffff']*)", stripped, re.M)
    prints = re.findall(r"^\s*#print axioms\s+(\S+)", stripped, re.M)
    namespace = specification["namespace"]
    expected_declarations = [namespace + "." + name for _, name in ds]
    expected_prints = [name if name.startswith("GoldbachRound19.") else namespace + "." + name for name in prints]
    generated = specification["generated_axiom_prints"]
    assert Counter(expected_prints) == Counter(expected_declarations + generated)
    assert len(expected_prints) == len(set(expected_prints))
    imports = re.findall(r"^\s*import\s+(\S+)", stripped, re.M)
    counts = Counter("theorem" if kind == "lemma" else kind for kind, _ in ds)
    assert ds and imports
    return expected_declarations, expected_prints, imports, counts


def compile_new(inputs):
    build = HERE / "build"
    build.mkdir(exist_ok=False)
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(build), *inputs["historical_library_dirs"], *inputs["cache_library_dirs"]])
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    results, totals = [], Counter()
    new_modules = {Path(relative).stem for relative in inputs["new_module_source_order"]}
    for relative in inputs["new_module_source_order"]:
        original = bound(relative)
        module = original.stem
        source = build / original.name
        capture = Path(inputs["PREEXEC_captures"][relative]["snapshot"])
        with source.open("xb") as f:
            f.write(capture.read_bytes())
        snapshot = HERE / (module + "_source.lean.txt")
        with snapshot.open("xb") as f:
            f.write(source.read_bytes())
        names, print_names, imports, counts = declarations(source, inputs["module_specifications"][relative])
        for dependency in imports:
            if dependency == "Mathlib":
                continue
            if dependency in new_modules:
                assert (build / (dependency + ".olean")).is_file(), ("new_import_not_independently_built", dependency)
            else:
                assert any((Path(folder) / (dependency + ".olean")).is_file()
                           for folder in inputs["historical_library_dirs"]), ("readonly_import_missing", dependency)
        out, log = build / (module + ".olean"), HERE / (module + ".log")
        stdout_path, stderr_path = HERE / (module + ".stdout.bin"), HERE / (module + ".stderr.bin")
        command = [inputs["lean_executable"], "-o", str(out), str(source)]
        started = {"round": 19, "role": 5, "phase": "PREEXEC", "module": module, "started_utc": now(),
                   "source_original": str(original), "source": str(source), "source_snapshot": str(snapshot),
                   "source_sha256": sha(source), "command": command, "cwd": str(build),
                   "LEAN_PATH": env["LEAN_PATH"], "lean_sha256": sha(inputs["lean_executable"]),
                   "compiler_version_metadata": inputs["compiler_version_metadata"],
                   "input_manifest_sha256": sha(HERE / "input_manifest.json"),
                   "audit_source_sha256": sha(Path(__file__)),
                   "readonly_import_bindings": inputs["historical_dependencies_sha256"],
                   "fresh_import_olean_sha256": {row["module"]: row["olean_sha256"] for row in results}}
        exclusive(HERE / (module + "_started.json"), started)
        emit("ACTUAL_FRESH_NEW_LEAN_STARTED", module=module, explicit_declarations=len(names), axiom_prints=len(print_names))
        launch_error = None
        try:
            run = subprocess.run(command, cwd=build, env=env, capture_output=True)
            stdout, stderr, code = run.stdout, run.stderr, run.returncode
        except BaseException as exc:
            launch_error = repr(exc)
            stdout, stderr, code = b"", (launch_error + "\n").encode("utf-8"), None
        for target, data in ((stdout_path, stdout), (stderr_path, stderr), (log, stdout + stderr)):
            with target.open("xb") as f:
                f.write(data)
        text = log.read_text(encoding="utf-8", errors="replace")
        row = dict(started, phase="FINISHED", finished_utc=now(), exit_code=code,
                   subprocess_launch_error=launch_error, log=str(log), log_sha256=sha(log),
                   stdout=str(stdout_path), stdout_sha256=sha(stdout_path),
                   stderr=str(stderr_path), stderr_sha256=sha(stderr_path), olean=str(out),
                   declaration_counts=dict(counts), explicit_declarations=names,
                   requested_axiom_prints=print_names, imports=imports)
        exclusive(HERE / (module + "_actual_invocation.json"), row)
        assert code == 0 and out.is_file(), ("actual_Lean_or_launch_failure", module, code, launch_error)
        assert "error:" not in text and "sorryAx" not in text, ("invalid_Lean_success_log", module)
        parsed = {}
        for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
            assert match.group(1) not in parsed
            parsed[match.group(1)] = [item.strip() for item in match.group(2).split(",") if item.strip()]
        for match in re.finditer(r"'([^']+)' does not depend on any axioms", text):
            assert match.group(1) not in parsed
            parsed[match.group(1)] = []
        assert set(parsed) == set(print_names), ("axiom_print_inventory_mismatch", module)
        assert all(set(axioms) <= ALLOWED_AXIOMS for axioms in parsed.values()), ("nonstandard_axiom", module)
        assert original.read_bytes() == source.read_bytes() == snapshot.read_bytes() == capture.read_bytes()
        row.update(status="PASS_FRESH_NEW_INDEPENDENT_LEAN", olean_sha256=sha(out), axioms=parsed,
                   axiom_prints=len(parsed), generated_axiom_prints=inputs["module_specifications"][relative]["generated_axiom_prints"],
                   actual_warning_lines=[line for line in text.splitlines() if "warning:" in line])
        exclusive(HERE / (module + "_receipt.json"), row)
        results.append(row)
        totals.update(counts)
        emit("FRESH_NEW_INDEPENDENT_LEAN_PASS", module=module, olean_sha256=row["olean_sha256"], axiom_prints=len(parsed))
    return {"modules": results,
            "totals": {"modules": len(results), "theorems": totals["theorem"], "defs": totals["def"],
                       "structures": totals["structure"], "instances": totals["instance"],
                       "axiom_prints": sum(row["axiom_prints"] for row in results)},
            "historical_sources_compiled": False, "author19_oleans_used": False,
            "compiler_version_probe_invocations": 0}


def stage(name, function):
    global ACTIVE_STAGE
    ACTIVE_STAGE = name
    assert not (HERE / (name + "_PASS.json")).exists(), "No routine PASS stage replay"
    emit("STAGE_STARTED", name=name)
    result = function()
    exclusive(HERE / (name + "_PASS.json"), result)
    emit("STAGE_PASS", name=name, receipt_sha256=sha(HERE / (name + "_PASS.json")))
    return result


def main():
    inputs = load(HERE / "input_manifest.json")
    assert inputs["status"] == "FROZEN_PREEXEC_AFTER_EXPLICIT_ROOT_GATE"
    input_check(inputs)
    before = stage("01_preservation", preservation)
    numeric = stage("02_stored_numeric", lambda: stored_numeric(inputs))
    nonss = stage("03_nonss_stored_integers", lambda: nonss_stored_integer_audit(inputs))
    rank = stage("04_rank_stored_integers", lambda: rank_stored_integer_audit(inputs))
    authors = stage("05_author_actual_attempts", lambda: author_failures(inputs))
    lean = stage("06_fresh_independent_Lean", lambda: compile_new(inputs))
    input_check(inputs)
    after = stage("07_preservation_after", preservation)
    result = {"status": "PASS_INDEPENDENT_ROUND19_AUXILIARY_ONLY", "finished_utc": now(),
              "input_manifest_sha256": sha(HERE / "input_manifest.json"),
              "preservation_before": before, "preservation_after": after,
              "stored_numeric": numeric, "nonss_stored_integer_checks": nonss,
              "rank_stored_integer_checks": rank,
              "author_invocation_totals": authors["totals"], "independent_Lean": lean,
              "new_counts": lean["totals"], "previous_counts": {"modules": 30, "theorems": 507},
              "cumulative_counts": {"modules": 30 + lean["totals"]["modules"],
                                    "theorems": 507 + lean["totals"]["theorems"]},
              "semantic_obligations": inputs["semantic_obligations"],
              "source_onset_logN": "10^24", "written_rank3_local_onset_logN": "10^40",
              "all_numeric_data_finite_only": True, "source_onset_applied_to_N_10power8": False,
              "producer_kernel_log_or_new_sign_called": False,
              "old_Lean_or_PDF_or_preflight_script_executed": False,
              "score": 0, "victory": False, "parity_obstacle_bypass_proved": False,
              "full_fixed_D_N_ledger_paid": False}
    exclusive(HERE / "audit_receipt.json", result)
    emit("ACTUAL_JUDGE19_FINISHED", status=result["status"], new_counts=result["new_counts"], victory=False)


if __name__ == "__main__":
    try:
        main()
    except BaseException as exc:
        failure = {"status": "FAILED_ACTUAL_AUDIT_ATTEMPT", "failed_stage": ACTIVE_STAGE,
                   "finished_utc": now(), "error": repr(exc), "traceback": traceback.format_exc(),
                   "automatic_retry": False, "analytic_parity_failure_inferred": False,
                   "failed_sources_and_logs_preserved": True, "victory": False}
        if not (HERE / "audit_receipt.json").exists():
            exclusive(HERE / "audit_receipt.json", failure)
        traceback.print_exc()
        sys.exit(1)
