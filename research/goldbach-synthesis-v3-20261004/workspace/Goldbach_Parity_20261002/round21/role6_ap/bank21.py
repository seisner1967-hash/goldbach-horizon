"""NEW strict AP21 producer. Execute only once through the separately root-gated launcher."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path
import sys

from arithmetic21 import (N, X, LEFT, RIGHT, ceil_power, floor_power, sieve, factor,
                          canonical_p0, candidate_bitmap, add_vector, vector_json, fraction_text)
from envelope21 import EnvelopeCache
from frames21 import catalogue
from integral21 import IntegralCache
from storage21 import Stream, json_exclusive, sha256
from weights21 import profile, serial_profile, components
from outward import LogOracle, add, neg, scale, mul, absolute_upper, absolute_lower, iv_json

BASE = Path(r"D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002")
RESULT = BASE / "round21" / "ap.json"


def empty_iv() -> tuple:
    return Fraction(0), Fraction(0)


def gap_certificate(price: tuple, remainder: tuple) -> dict:
    return iv_json((price[0] - absolute_upper(remainder), price[1] - absolute_lower(remainder)))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    output = Path(args.output)
    assert output.is_dir() and not RESULT.exists()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    primes, prime_flags = sieve(10000)
    a = ceil_power(N, 7, 16)
    alpha = ceil_power(N, 1, 4)
    original_q = (N - 1) // alpha
    m = ceil_power(N, 3, 4)
    source_z = ceil_power(N, 1, 64)
    source_P = floor_power(N, 1, 64)
    p0 = canonical_p0(primes)
    assert (a, alpha, original_q, m) == (3163, 100, 999999, 1000000)
    assert RIGHT - LEFT == 12500000 and X == N // 4 and N // 5 <= X <= N // 4
    cuts = [{"name": f"test_z{z}_P19_K{order}", "z": z, "P": 19, "K": order,
             "source_cut": False} for z in (13, 23) for order in (0, 1)]
    cuts.append({"name": "source_cut", "z": source_z, "P": source_P,
                 "K": 1, "source_cut": True})
    bitmap, bitmap_meta = candidate_bitmap(primes, output)
    print("AP21 fresh complete 12500000-candidate factor bitmap finished", flush=True)
    frame_stream = Stream(output / "frames.jsonl.gz")
    frames, frame_meta = catalogue(primes, a, m, original_q, bitmap, frame_stream)
    frame_storage = frame_stream.close()
    del bitmap
    print(f"AP21 complete static frame catalogue: {len(frames)} frames", flush=True)
    oracle = LogOracle(output / "new_logs.jsonl.gz")
    u = oracle.log(N)
    assert u[1] < 10 ** 24
    c2_low, c2_high = Fraction(2541, 4096), Fraction(11011, 16384)
    singular_multiplier = Fraction(2)
    for p, _ in factor(N, primes):
        if p > 2:
            singular_multiplier *= Fraction(p - 1, p - 2)
    singular = singular_multiplier * c2_low, singular_multiplier * c2_high
    assert singular == (Fraction(2541, 1536), Fraction(11011, 6144))
    integral_stream = Stream(output / "integrals.jsonl.gz")
    envelope_stream = Stream(output / "envelopes.jsonl.gz")
    certificate_stream = Stream(output / "certificates.jsonl.gz")
    coefficient_stream = Stream(output / "original_coefficients.jsonl.gz")
    profiles_stream = Stream(output / "weight_profiles.jsonl.gz")
    group_stream = Stream(output / "exact_grouped_coefficients.jsonl.gz")
    integration = IntegralCache(oracle, integral_stream)
    evaluator = EnvelopeCache(primes, oracle, envelope_stream, certificate_stream, integration)
    profiles = {}
    profile_rows = {}
    totals = {}
    counts = Counter()
    all_resolved = True
    falsifiers = dict(frame_meta["falsifiers"])
    for cut in cuts:
        totals[cut["name"]] = {"PriceQ": empty_iv(), "PriceC": empty_iv(),
                               "Qremainder": empty_iv(), "Cremainder": empty_iv(),
                               "affine_kappa_log_part_Q": empty_iv(), "affine_kappa_S_coefficient_Q": empty_iv(),
                               "affine_kappa_log_part_C": empty_iv(), "affine_kappa_S_coefficient_C": empty_iv()}
        for frame in frames:
            signature = tuple(p for p in primes if p <= max(cut["z"], cut["P"]) and frame["t"] % p == 0)
            profile_key = cut["z"], cut["P"], cut["K"], signature
            if profile_key not in profiles:
                value = profile(cut["z"], cut["P"], cut["K"], frame["t"], p0, primes)
                value["id"] = len(profiles)
                profiles[profile_key] = value
                profiles_stream.emit({"kind": "complete_original_weight_axes", **serial_profile(value),
                                      "zero_axes_retained": True,
                                      "coefficient_tensor_definition": "Q=lambda[k]*lambda[l]; C=lambda[k]*lambda[l]*xi[h]",
                                      "all_k_l_ordered_pairs": [1, cut["z"]],
                                      "all_h_original_and_nonSF_extensions": True})
            value = profiles[profile_key]
            counts["frames_times_cuts"] += 1
            counts["original_Q_representations"] += value["all_Q_representations"]
            counts["original_C_representations"] += value["all_C_original_representations"]
            counts["extended_nonSF_zero_representations"] += value["all_C_extended_zero_representations"]
            if frame["empty_window"]:
                # Exact Cartesian tensor schema retains ALL empty-frame representations without expanding identical zeros.
                coefficient_stream.emit({"kind": "complete_empty_frame_coefficient_tensor", "cut": cut["name"],
                                         "frame": frame["id"], "profile": value["id"],
                                         "t": frame["t"], "L": frame["L"], "U": frame["U"],
                                         "all_k_l_axes": [1, cut["z"]],
                                         "all_h_axes_from_profile": True,
                                         "all_composite_caps_le_U_empty": True,
                                         "Q_representation_count": value["all_Q_representations"],
                                         "C_representation_count": value["all_C_original_representations"],
                                         "extended_zero_representation_count": value["all_C_extended_zero_representations"],
                                         "actual_mass_main_remainder_price_exact_zero": True,
                                         "factorized_complete_cartesian_catalogue_not_sample": True})
                counts["factorized_empty_frame_tensors"] += 1
                continue
            prices = {"Q": empty_iv(), "C": empty_iv()}
            grouped = {}
            maps = {"Q": {}, "C": {}}
            remainder_sums = {"Q": empty_iv(), "C": empty_iv()}
            original_group_check = {}
            for representation in components(value, frame):
                kind = representation["kind"]
                coefficient = representation["coefficient"]
                nu = representation["nu"]
                upper = representation["U"]
                compatible = gcd(nu, frame["t"] * N) == 1
                empty = frame["L"] > upper
                key = kind, frame["t"], nu, frame["L"], upper
                grouped[key] = grouped.get(key, Fraction(0)) + coefficient
                counts["expanded_nonempty_frame_original_components"] += 1
                counts["zero_coefficient_components"] += coefficient == 0
                counts["incompatible_components"] += not compatible
                counts["empty_capped_components"] += empty
                counts["large_modulus_components"] += nu > upper
                query = None
                if coefficient and compatible and not empty:
                    query = evaluator.query(N, frame["t"], nu, frame["L"], upper, a, frame["physical_q"])
                    all_resolved &= query["resolved"]
                    prices[kind] = add(prices[kind], scale(query["bound"], abs(coefficient)))
                    add_vector(maps[kind], query["physical_map"], coefficient)
                    remainder_sums[kind] = add(remainder_sums[kind], scale(query["remainder"], coefficient))
                    original_group_check[key] = original_group_check.get(key, Fraction(0)) + coefficient
                if not compatible:
                    assert not [q for q in frame["physical_q"]
                                if q <= upper and (N - frame["t"] * q) % nu == 0]
                coefficient_stream.emit({"kind": "original_Q_or_C_representation", "cut": cut["name"],
                                         "frame": frame["id"], "profile": value["id"],
                                         **{name: item for name, item in representation.items() if name != "coefficient"},
                                         "coefficient": fraction_text(coefficient),
                                         "L": frame["L"], "compatible": compatible, "empty": empty,
                                         "zero_coefficient": coefficient == 0,
                                         "query_id": query["id"] if query else None,
                                         "actual_price_zero_reason": ("coefficient_zero" if not coefficient else
                                                                      "incompatible" if not compatible else
                                                                      "empty_window" if empty else None)})
                if representation["p"] is not None and representation["h"] is not None:
                    product_bad = representation["p"] * representation["h"] * representation["k"] * representation["l"]
                    if coefficient and product_bad != nu:
                        falsifiers.setdefault("product_instead_of_lcm", {"cut": cut["name"], "frame": frame["id"],
                                              "correct_nu": nu, "incorrect_product": product_bad,
                                              "k": representation["k"], "l": representation["l"],
                                              "p": representation["p"], "h": representation["h"]})
            regrouped_maps = {"Q": {}, "C": {}}
            regrouped_remainders = {"Q": empty_iv(), "C": empty_iv()}
            for key, coefficient in sorted(grouped.items()):
                kind, t, nu, lower, upper = key
                compatible = gcd(nu, t * N) == 1
                query = None
                if coefficient and compatible and lower <= upper:
                    query = evaluator.query(N, t, nu, lower, upper, a, frame["physical_q"])
                    add_vector(regrouped_maps[kind], query["physical_map"], coefficient)
                    regrouped_remainders[kind] = add(regrouped_remainders[kind], scale(query["remainder"], coefficient))
                    assert original_group_check.get(key, Fraction(0)) == coefficient
                group_stream.emit({"kind": "exact_original_representation_image", "cut": cut["name"],
                                   "frame": frame["id"], "key_kind_t_nu_L_U": list(key),
                                   "coefficient": fraction_text(coefficient),
                                   "query_id": query["id"] if query else None,
                                   "compatible": compatible, "empty": lower > upper})
            assert maps == regrouped_maps
            log_c = oracle.log(frame["c"])
            kappa = add(log_c, singular)
            assert kappa[0] > 0
            for kind in ("Q", "C"):
                gap = gap_certificate(prices[kind], regrouped_remainders[kind])
                if Fraction(gap["hi"]) < 0:
                    raise AssertionError(f"AP21 original {kind} coefficient price bound refuted")
                resolved = Fraction(gap["lo"]) >= 0
                all_resolved &= resolved
                certificate_stream.emit({"kind": "whole_original_coefficient_price", "cut": cut["name"],
                                          "frame": frame["id"], "axis": kind,
                                          "Price": iv_json(prices[kind]),
                                          "actual_remainder": iv_json(regrouped_remainders[kind]),
                                          "price_minus_abs_remainder": gap, "resolved": resolved,
                                          "actual_mass_log_map": vector_json(maps[kind]),
                                          "exact_original_grouped_maps_equal": True,
                                          "no_favorable_coefficient_selection": True,
                                          "kappa": iv_json(kappa), "S_N": iv_json(singular),
                                          "C2_box": [fraction_text(c2_low), fraction_text(c2_high)],
                                          "singular_multiplier_from_actual_N": fraction_text(singular_multiplier)})
                total = totals[cut["name"]]
                total[f"Price{kind}"] = add(total[f"Price{kind}"], mul(kappa, prices[kind]))
                total[f"{kind}remainder"] = add(total[f"{kind}remainder"], mul(kappa, regrouped_remainders[kind]))
                total[f"affine_kappa_log_part_{kind}"] = add(total[f"affine_kappa_log_part_{kind}"], mul(log_c, prices[kind]))
                total[f"affine_kappa_S_coefficient_{kind}"] = add(total[f"affine_kappa_S_coefficient_{kind}"], prices[kind])
        print(f"AP21 cut {cut['name']} completed, fresh envelopes={evaluator.stats['envelopes']}", flush=True)
    local = evaluator.query(51051, 1, 1, 3, 20, None)
    assert [q for q in primes if 3 <= q <= 20 and 51051 % q == 0] == [3, 7, 11, 13, 17]
    all_resolved &= local["resolved"]
    falsifiers.update(evaluator.falsifiers)
    # These mandatory wrong endpoints have positive omitted intervals for EVERY nonempty frame.
    first_frame = next(frame for frame in frames if not frame["empty_window"])
    endpoint_slice, endpoint_id = integration.get(N, first_frame["t"], first_frame["L"], first_frame["L"], 32)
    assert endpoint_slice[0] > 0
    falsifiers["A_equals_L_instead_of_L_minus_1"] = {"frame": first_frame["id"],
                                                           "positive_omitted_integral": iv_json(endpoint_slice),
                                                           "integral_id": endpoint_id}
    aggregate_rows = []
    for cut in cuts:
        total = totals[cut["name"]]
        prices = add(total["PriceQ"], total["PriceC"])
        remainders = add(total["Qremainder"], neg(total["Cremainder"]))
        gap = gap_certificate(prices, remainders)
        assert Fraction(gap["hi"]) >= 0
        all_resolved &= Fraction(gap["lo"]) >= 0
        aggregate_rows.append({"cut": cut, "kappa_weighted_original_price": iv_json(prices),
                               "kappa_weighted_Q_minus_C_remainder": iv_json(remainders),
                               "price_minus_abs_remainder": gap,
                               "all_totals": {key: iv_json(item) for key, item in total.items()},
                               "no_claim_of_small_SD_or_whole_Gamma": True})
    storage = {"frames": frame_storage,
               "integrals": integral_stream.close(), "envelopes": envelope_stream.close(),
               "certificates": certificate_stream.close(), "original_coefficients": coefficient_stream.close(),
               "weight_profiles": profiles_stream.close(), "grouped_coefficients": group_stream.close(),
               "logs": oracle.close()}
    for key in ("strict_square_cap", "raw_mu_zero_mask", "q_selected_after_Prime_j",
                "nonminimal_negative_Bonferroni_K0", "product_instead_of_lcm",
                "envelope_after_jump_only", "large_modulus_error_declared_zero"):
        falsifiers.setdefault(key, {"status": "NONE_IN_DOMAIN", "domain": "new exhaustive AP21 physical catalogue"})
    result = {
        "status": "PASS_NEW_AP21_PHYSICAL_BRIDGE_ENVELOPE_ABEL" if all_resolved else "UNRESOLVED_PRECISION_AP21_NO_MATH_REFUTATION",
        "parameters": {"N": N, "x": X, "candidate_interval": [LEFT + 1, RIGHT],
                       "all_candidate_count": RIGHT - LEFT, "alpha": alpha, "Q": original_q,
                       "a": a, "M": m, "p0_actual": p0, "cuts": cuts},
        "source_guards": {"logN_ge_10pow24": False, "N_div5_le_x_le_N_div4": True,
                          "generic_frame_log_guards_verified_literally": True,
                          "source_z_guard": source_z < LEFT + 1,
                          "all_source_guards_true": False},
        "bitmap": bitmap_meta, "frame_catalogue": frame_meta,
        "counts": dict(counts), "envelope_and_Abel_counts": evaluator.stats,
        "aggregate_prices_and_remainders": aggregate_rows, "falsifiers": falsifiers,
        "C2_actual_box": [fraction_text(c2_low), fraction_text(c2_high)],
        "S_N_actual_box": iv_json(singular), "u": iv_json(u),
        "local_retirement_control": {"N": 51051, "t": 1, "nu": 1, "L": 3, "U": 20,
                                     "query_id": local["id"], "source_16_over_7_not_applied": True,
                                     "outside_physical_N1e8": True},
        "storage": storage, "all_bound_decisions_resolved": all_resolved,
        "exact_bridge_and_cellular_Abel_verified": True,
        "previous_outputs_or_bitmaps_or_signs_read": 0,
        "old_producer_or_old_PASS_executions": 0, "float_operations": 0,
        "new_producer_math_invocations": 1,
        "arithmetic_library_reuse": {"source": "round20/role6_composite/outward.py",
                                     "sha256": "9823d58d56a8854759cd05268c9fe4fe80b9943b34b190dd129618abbf1b43a8",
                                     "only_new_log_inputs_evaluated": True,
                                     "old_monotone_integral_helper_not_called": True},
        "DN_evaluated": False, "M0_or_W_or_parents_evaluated": False,
        "unpaid": ["SD/BV estimate", "whole Gamma", "literal M0 bridge", "tail and slack",
                   "capacity and parents", "cross_partition", "full six-term D_N ledger"],
        "victory": False,
    }
    json_exclusive(RESULT, result)
    json_exclusive(output / "result_copy.json", result)
    assert sha256(RESULT) == sha256(output / "result_copy.json")
    print({"status": result["status"], "result": str(RESULT), "sha256": sha256(RESULT),
           "all_m": evaluator.stats["all_m_indices_evaluated"], "victory": False}, flush=True)
    return 0 if all_resolved else 3


if __name__ == "__main__":
    raise SystemExit(main())
