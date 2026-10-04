"""NEW ordinary prime AP full-cell envelope, witness bridge and cellular Abel."""
from __future__ import annotations

from fractions import Fraction
from bisect import bisect_right
import hashlib
from math import gcd

from arithmetic21 import N, phi, add_vector, vector_json
from outward import SCALE, add, neg, scale, absolute_lower, absolute_upper, iv_json


class EnvelopeCache:
    def __init__(self, primes, oracle, envelope_stream, certificate_stream, integral_cache):
        self.primes = primes
        self.oracle = oracle
        self.envelope_stream = envelope_stream
        self.certificate_stream = certificate_stream
        self.integral_cache = integral_cache
        self.envelopes = {}
        self.queries = {}
        self.stats = {"envelopes": 0, "all_m_indices_evaluated": 0, "two_values_per_m": 0,
                      "queries": 0, "empty_prime_classes": 0, "modulus_gt_U": 0,
                      "left_limit_larger_than_after_only": 0,
                      "interior_affine_points": 0, "Abel_integer_cells": 0,
                      "bound_POS": 0, "bound_ZERO": 0, "bound_UNRESOLVED": 0,
                      "bound_NEG": 0, "retirement_prime_labels": 0}
        self.falsifiers = {}

    def envelope(self, n: int, t: int, nu: int, upper: int) -> dict:
        assert nu >= 1 and upper >= 0 and gcd(nu, t * n) == 1
        residue = 0 if nu == 1 else n * pow(t, -1, nu) % nu
        assert gcd(residue, nu) == 1
        key = n, t % nu, nu, upper
        if key in self.envelopes:
            return self.envelopes[key]
        totient = phi(nu, self.primes)
        assert totient >= 1
        class_primes = [q for q in self.primes if q <= upper and (t * q - n) % nu == 0]
        jumps = {q: self.oracle.scaled(q) for q in class_primes}
        theta_lo = theta_hi = 0
        maximum_lo = maximum_hi = 0
        after_lo = after_hi = 0
        runs = []
        run_start = 0
        digest = hashlib.sha256()
        rows = 0
        for m in range(upper + 1):
            if m in jumps:
                if run_start < m:
                    runs.append([run_start, m - 1, theta_lo, theta_hi])
                run_start = m
                theta_lo += jumps[m][0]
                theta_hi += jumps[m][1]
            before_scaled = theta_lo * totient - m * SCALE, theta_hi * totient - m * SCALE
            endpoint = min(m + 1, upper)
            left_scaled = theta_lo * totient - endpoint * SCALE, theta_hi * totient - endpoint * SCALE
            for pair, after_value in ((before_scaled, True), (left_scaled, False)):
                low = pair[0] if pair[0] > 0 else -pair[1] if pair[1] < 0 else 0
                high = max(abs(pair[0]), abs(pair[1]))
                maximum_lo = max(maximum_lo, low)
                maximum_hi = max(maximum_hi, high)
                if after_value:
                    after_lo = max(after_lo, low)
                    after_hi = max(after_hi, high)
                digest.update(pair[0].to_bytes(32, "little", signed=True))
                digest.update(pair[1].to_bytes(32, "little", signed=True))
                rows += 1
            if m < upper:
                for denominator in (2, 3):
                    numerator = m * denominator + 1
                    lo_num = theta_lo * totient * denominator - numerator * SCALE
                    hi_num = theta_hi * totient * denominator - numerator * SCALE
                    assert max(abs(lo_num), abs(hi_num)) <= maximum_hi * denominator or (
                        max(abs(lo_num), abs(hi_num)) <= max(
                            abs(before_scaled[0]), abs(before_scaled[1]),
                            abs(left_scaled[0]), abs(left_scaled[1])) * denominator)
                    self.stats["interior_affine_points"] += 1
        runs.append([run_start, upper, theta_lo, theta_hi])
        assert runs[0][0] == 0 and runs[-1][1] == upper
        assert all(runs[i][1] + 1 == runs[i + 1][0] for i in range(len(runs) - 1))
        maximum = Fraction(maximum_lo, SCALE * totient), Fraction(maximum_hi, SCALE * totient)
        after_max = Fraction(after_lo, SCALE * totient), Fraction(after_hi, SCALE * totient)
        identifier = len(self.envelopes)
        value = {"id": identifier, "nu": nu, "phi": totient, "U": upper, "residue": residue,
                 "E": maximum, "after_only_E": after_max, "class_primes": class_primes,
                 "prime_jump_set": set(class_primes)}
        self.envelopes[key] = value
        self.stats["envelopes"] += 1
        self.stats["all_m_indices_evaluated"] += upper + 1
        self.stats["two_values_per_m"] += rows
        self.stats["empty_prime_classes"] += not class_primes
        self.stats["modulus_gt_U"] += nu > upper
        if maximum[0] > after_max[1]:
            self.stats["left_limit_larger_than_after_only"] += 1
            self.falsifiers.setdefault("envelope_after_jump_only", {"envelope": identifier, "nu": nu,
                                       "U": upper, "E": iv_json(maximum), "after_only_E": iv_json(after_max)})
        if nu > upper and not class_primes:
            self.falsifiers.setdefault("large_modulus_error_declared_zero", {"envelope": identifier,
                                       "nu": nu, "U": upper, "E": iv_json(maximum)})
        self.envelope_stream.emit({"kind": "full_integer_cell_envelope", "id": identifier,
                                   "N": n, "t_mod_nu": t % nu, "nu": nu, "phi": totient,
                                   "residue": residue, "U": upper, "E": iv_json(maximum),
                                   "after_only_E": iv_json(after_max), "ordinary_prime_class": class_primes,
                                   "no_q_divides_N_mask_before_Theta": True,
                                   "compressed_Theta_runs_all_indices_0_to_U": runs,
                                   "run_denominator": SCALE,
                                   "each_m_two_interval_values_definition": [
                                       "[Theta_lo-m/phi,Theta_hi-m/phi]",
                                       "[Theta_lo-min(m+1,U)/phi,Theta_hi-min(m+1,U)/phi]"],
                                   "actually_evaluated_m_count": upper + 1,
                                   "actually_evaluated_value_count": rows,
                                   "all_four_signed_scaled_endpoints_i256_sha256": digest.hexdigest(),
                                   "run_partition_exact": True, "interior_affine_checks_denominators": [2, 3]})
        return value

    def query(self, n: int, t: int, nu: int, lower: int, upper: int,
              source_a: int | None, physical_q: list[int] | None = None) -> dict:
        key = n, t, nu, lower, upper, source_a
        if key in self.queries:
            value = self.queries[key]
            if physical_q is not None:
                expected = [q for q in physical_q if lower <= q <= upper and (n - t * q) % nu == 0]
                assert value["physical_q"] == expected
            return value
        assert lower <= upper and gcd(nu, t * n) == 1
        envelope = self.envelope(n, t, nu, upper)
        guard = self.integral_cache.guard(n, t, lower, upper, source_a)
        assert guard["generic_guards"] and not guard["empty"]
        all_window = [q for q in envelope["class_primes"] if lower <= q <= upper]
        retired = [q for q in all_window if n % q == 0]
        unit_window = [q for q in all_window if gcd(q, n) == 1]
        if physical_q is not None:
            expected = [q for q in physical_q if lower <= q <= upper and (n - t * q) % nu == 0]
            assert unit_window == expected
        unmasked_map = {n - t * q: 1 for q in all_window}
        correction_map = {n - t * q: 1 for q in retired}
        physical_map = {n - t * q: 1 for q in unit_window}
        difference = dict(unmasked_map)
        add_vector(difference, correction_map, -1)
        assert difference == physical_map
        # Exact cellular Abel normal form: prefix vector differences at EVERY integer cell.
        atom_primes = []
        previous_count = bisect_right(envelope["class_primes"], lower - 1)
        for m in range(lower, upper + 1):
            current_count = bisect_right(envelope["class_primes"], m)
            increment = current_count - previous_count
            expected = 1 if m in envelope["prime_jump_set"] else 0
            assert increment == expected
            if increment:
                atom_primes.append(m)
            previous_count = current_count
            self.stats["Abel_integer_cells"] += 1
        assert atom_primes == all_window
        # log(q)*f(q) simplifies to log(n-tq) using exactly the same positive log(q).
        abel_normal_form = {n - t * q: 1 for q in atom_primes}
        assert abel_normal_form == unmasked_map
        correction = self.oracle.vector(correction_map)
        self.stats["retirement_prime_labels"] += len(retired)
        if retired:
            self.falsifiers.setdefault("q_divides_N_retirement_deleted", {"N": n, "t": t,
                                       "nu": nu, "L": lower, "U": upper,
                                       "retired_primes": retired, "map": vector_json(correction_map),
                                       "local_outside_physical_N1e8": n != N})
        f_A = guard["f_interval"][0]
        retirement_bound = scale(self.oracle.log(n), f_A[0]), scale(self.oracle.log(n), f_A[1])
        assert correction[0] >= 0
        assert retirement_bound[1][1] >= correction[1]
        mass = self.oracle.vector(physical_map)
        pieces = 32
        while True:
            integral, integral_id = self.integral_cache.get(n, t, lower, upper, pieces)
            remainder = add(mass, neg(scale(integral, Fraction(1, envelope["phi"]))))
            general_bound = add(scale(envelope["E"], 2 * f_A[0]), correction)
            general_bound = (general_bound[0],
                             2 * f_A[1] * envelope["E"][1] + correction[1])
            bound = (add(scale(envelope["E"], Fraction(32, 7)), scale(self.oracle.log(n), Fraction(16, 7)))
                     if guard["source_16_over_7_applied"] else general_bound)
            gap = (bound[0] - absolute_upper(remainder), bound[1] - absolute_lower(remainder))
            if gap[0] >= 0 or gap[1] < 0 or pieces >= 4096:
                break
            pieces *= 2
        certificate = iv_json(gap)
        label = certificate["sign"]
        counter = ("bound_ZERO" if gap == (0, 0) else "bound_POS" if gap[0] >= 0
                   else "bound_NEG" if gap[1] < 0 else "bound_UNRESOLVED")
        self.stats[counter] += 1
        if gap[1] < 0:
            self.certificate_stream.emit({"kind": "MATHEMATICAL_B6_BOUND_REFUTED", "N": n, "t": t,
                                          "nu": nu, "L": lower, "U": upper, "gap": certificate})
            raise AssertionError(f"AP21 B6 refuted N={n} t={t} nu={nu} L={lower} U={upper}")
        identifier = len(self.queries)
        result = {"id": identifier, "E": envelope["E"], "bound": bound, "mass": mass,
                  "remainder": remainder, "physical_map": physical_map,
                  "physical_q": unit_window, "integral": integral, "phi": envelope["phi"],
                  "resolved": gap[0] >= 0, "gap": gap}
        self.queries[key] = result
        self.stats["queries"] += 1
        if all_window and lower <= upper:
            self.falsifiers.setdefault("one_q_zero_integral", {"query": identifier,
                                       "L": lower, "U": upper, "prime_count": len(all_window),
                                       "integral": iv_json(integral)})
        self.certificate_stream.emit({"kind": "physical_AP_Abel_B6", "id": identifier,
                                      "N": n, "t": t, "nu": nu, "L": lower, "U": upper,
                                      "envelope_id": envelope["id"], "integral_id": integral_id,
                                      "mass": iv_json(mass), "physical_log_map": vector_json(physical_map),
                                      "unmasked_log_map": vector_json(unmasked_map),
                                      "correction_log_map": vector_json(correction_map),
                                      "retired_primes": retired, "C_N": iv_json(correction),
                                      "remainder": iv_json(remainder), "bound": iv_json(bound),
                                      "bound_minus_abs_remainder": certificate, "resolved": gap[0] >= 0,
                                      "source_constant_applied": guard["source_16_over_7_applied"],
                                      "Abel_exact_cellular_normal_form_equal": True,
                                      "Abel_cells": upper - lower + 1,
                                      "physical_equals_unmasked_minus_C_N_exact_map": True,
                                      "wrong_lower_endpoint_if_used": lower,
                                      "correct_continuous_lower_endpoint": lower - 1,
                                      "local_outside_physical_N1e8": n != N})
        return result
