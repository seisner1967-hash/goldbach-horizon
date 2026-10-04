"""NEW exact Selberg/Bonferroni representations and finite prime AP profiles20."""
from __future__ import annotations

from fractions import Fraction
from math import gcd, lcm, comb

from arithmetic import N, actual_weights, bonferroni_catalog, factor, phi, frac
from outward import SCALE, add, neg, scale, iv_json, absolute_lower, absolute_upper


class TemplateBank:
    def __init__(self, primes, store):
        self.primes = primes
        self.store = store
        self.templates = {}
        self.phi_cache = {1: 1}
        self.complete_rows = 0

    def totient(self, value):
        if value not in self.phi_cache:
            self.phi_cache[value] = phi(value, self.primes)
        return self.phi_cache[value]

    def get(self, z, P, K, t, p0):
        signature = tuple(p for p, _ in factor(t, self.primes) if p <= max(z, P))
        key = (z, P, K, signature)
        weights = actual_weights(z, t, p0, self.primes)
        if key in self.templates:
            template = self.templates[key]
            assert weights["lambdas"] == template["weights"]["lambdas"]
            assert weights["G"] == template["weights"]["G"]
            assert weights["original"] == template["weights"]["original"]
            return template
        template_id = len(self.templates)
        active = weights["lambdas"]
        lower = {}
        q_groups = {}
        c_groups = {}
        q_original_counts = {}
        c_original_counts = {}
        start = self.store.count
        # Original k and l include every zero lambda and every nonsquarefree k.
        # Every original h (including xi=0) is serialized, even in empty windows.
        for k in range(1, z + 1):
            for l in range(1, z + 1):
                K0 = lcm(k, l)
                q_original_counts[K0] = q_original_counts.get(K0, 0) + 1
                coefficient = active.get(k, Fraction(0)) * active.get(l, Fraction(0))
                record = {"template": template_id, "kind": "Q", "k": k, "l": l,
                          "K0": K0, "nu": K0, "coefficient": frac(coefficient),
                          "zero_original_lambda": coefficient == 0,
                          "compatible_tN": gcd(K0, t * N) == 1}
                self.store.put(record)
                self.complete_rows += 1
                if coefficient:
                    q_groups[K0] = q_groups.get(K0, Fraction(0)) + coefficient
        for p in self.primes:
            if p > P:
                break
            catalog = bonferroni_catalog(p, t, K, self.primes)
            lower[p] = catalog
            for k in range(1, z + 1):
                for l in range(1, z + 1):
                    K0 = lcm(k, l)
                    Kp = K0 // gcd(K0, p)
                    for hrow in catalog["original"]:
                        h, xi = hrow["h"], hrow["xi"]
                        H = lcm(h, Kp)
                        nu = p * H
                        c_original_counts[(p, nu)] = c_original_counts.get((p, nu), 0) + 1
                        coefficient = active.get(k, Fraction(0)) * active.get(l, Fraction(0)) * xi
                        proof = None
                        if coefficient:
                            pf0 = [ell for ell, exponent in factor(K0, self.primes) if exponent == 1]
                            assert len(pf0) == len(factor(K0, self.primes))
                            pfKp = [ell for ell, _ in factor(Kp, self.primes)]
                            assert pfKp == [ell for ell in pf0 if ell != p]
                            pfH = [ell for ell, _ in factor(H, self.primes)]
                            assert set(pfH) == set(hrow["prime_factors"]) | set(pfKp)
                            assert p not in pfH
                            assert h < p ** (2 * K + 1)
                            assert nu <= p ** (2 * K + 2) * z * z
                            # Factor supports prove B5 simultaneously for every quotient v;
                            # no sampled q, artificial coprimality(p,v), or strict roughness.
                            proof = {"K0_squarefree_prime_support": pf0, "Kp_support": pfKp,
                                     "H_union_support": pfH, "nu_support": sorted(pfH + [p]),
                                     "B5_all_quotients_by_prime_divisibility": True,
                                     "B8_exact": True}
                            c_groups[(p, nu)] = c_groups.get((p, nu), Fraction(0)) + coefficient
                        self.store.put({"template": template_id, "kind": "Cminus", "p": p,
                                        "k": k, "l": l, "h": h, "xi": xi, "K0": K0,
                                        "Kp": Kp, "H": H, "nu": nu,
                                        "coefficient": frac(coefficient),
                                        "zero_original_lambda_or_xi": coefficient == 0,
                                        "compatible_tN": gcd(nu, t * N) == 1,
                                        "wrong_H_product_nu": p * h * Kp,
                                        "wrong_unshared_product_nu": p * h * k * l,
                                        "factor_support_proof": proof})
                        self.complete_rows += 1
        q_groups = {nu: value for nu, value in q_groups.items() if value}
        c_groups = {key: value for key, value in c_groups.items() if value}
        assert sum((value / self.totient(nu) for nu, value in q_groups.items()), Fraction(0)) == weights["Q"]
        header = {"id": template_id, "constructor_t": t, "key": [z, P, K, list(signature)],
                  "weights_original_all_k": weights["original"],
                  "G": frac(weights["G"]), "quadratic": frac(weights["Q"]),
                  "lambda1_exact1": True, "quadratic_equals1overG": True,
                  "Bonferroni_original_all_h": {str(p): cat["original"] for p, cat in lower.items()},
                  "Bonferroni_eligible_primes": {str(p): cat["eligible_primes"] for p, cat in lower.items()},
                  "representation_first_index": start, "representation_end_exclusive": self.store.count,
                  "representation_count": self.store.count - start,
                  "zero_originals_retained": True,
                  "same_signature_all_t_exact_weights_verified": True}
        all_nu = set(q_original_counts) | {nu for p, nu in c_original_counts}
        same_window = {nu: q_groups.get(nu, Fraction(0)) - sum(
            (value for (p, module), value in c_groups.items() if module == nu), Fraction(0)) for nu in all_nu}
        header["Q_all_grouped_coefficients_and_original_counts"] = [
            [nu, frac(q_groups.get(nu, Fraction(0))), count] for nu, count in sorted(q_original_counts.items())]
        header["C_all_grouped_coefficients_and_original_counts"] = [
            [p, nu, frac(c_groups.get((p, nu), Fraction(0))), count] for (p, nu), count in sorted(c_original_counts.items())]
        header["signed_coefficients_grouped_when_literal_windows_agree"] = [
            [nu, frac(same_window[nu]), q_original_counts.get(nu, 0) + sum(
                count for (p, module), count in c_original_counts.items() if module == nu)] for nu in sorted(all_nu)]
        unrestricted = actual_weights(z, t, 1, self.primes)
        header["finite_G_with_p0_admitted"] = frac(unrestricted["G"])
        header["finite_G_with_p0_excluded"] = frac(weights["G"])
        header["finite_G_ratio_not_forced_to_Euler_asymptotic"] = True
        template = {"id": template_id, "header": header, "weights": weights,
                    "lower": lower, "q_groups": q_groups, "c_groups": c_groups,
                    "q_original_counts": q_original_counts, "c_original_counts": c_original_counts}
        self.templates[key] = template
        return template


class FiniteAP:
    def __init__(self, primes, oracle, profile_store, query_store, templates, strict):
        self.primes = primes
        self.oracle = oracle
        self.profile_store = profile_store
        self.query_store = query_store
        self.templates = templates
        self.strict = strict
        self.profiles = {}
        self.queries = {}

    def profile(self, nu, residue):
        key = (nu, residue)
        if key in self.profiles:
            return self.profiles[key]
        assert gcd(residue, nu) == 1
        totient = self.templates.totient(nu)
        admitted = [q for q in self.primes if q % nu == residue]
        lower = upper = 0
        max_lower = max_upper = Fraction(0)
        states = []
        serialized = []
        future_profile_id = self.profile_store.count
        for q in admitted:
            before = (Fraction(lower, SCALE) - Fraction(q, totient),
                      Fraction(upper, SCALE) - Fraction(q, totient))
            lo, hi = self.oracle.scaled(q)
            lower += lo
            upper += hi
            after = (Fraction(lower, SCALE) - Fraction(q, totient),
                     Fraction(upper, SCALE) - Fraction(q, totient))
            max_lower = max(max_lower, absolute_lower(before), absolute_lower(after))
            max_upper = max(max_upper, absolute_upper(before), absolute_upper(after))
            states.append((q, lower, upper, max_lower, max_upper))
            before_cert = self.strict.interval(["AP_profile", future_profile_id, nu, residue, q, "left"], before,
                exact_expression={"theta_prime_keys_prefix_excluding_jump": admitted[:len(states) - 1],
                                  "minus_rational": f"{q}/{totient}"})
            after_cert = self.strict.interval(["AP_profile", future_profile_id, nu, residue, q, "right"], after,
                exact_expression={"theta_prime_keys_prefix_including_jump": admitted[:len(states)],
                                  "minus_rational": f"{q}/{totient}"})
            serialized.append({"prime_jump": q, "theta_prefix_scaled": [lower, upper],
                               "left_limit_error": before_cert, "right_error": after_cert,
                               "prefix_absolute_max": iv_json((max_lower, max_upper))})
        profile_id = self.profile_store.put({"nu": nu, "residue": residue,
                                              "phi": totient, "range": [0, 11000],
                                              "all_prime_jumps": serialized,
                                              "zero_endpoint": [0, 0],
                                              "q_dividing_N_retained_in_unmasked_theta": [q for q in admitted if N % q == 0],
                                              "not_global_Etheta_or_BV": True})
        profile = {"id": profile_id, "states": states, "phi": totient}
        self.profiles[key] = profile
        return profile

    def query(self, nu, residue, Y, qlo, qhi):
        key = (nu, residue, Y, qlo, qhi)
        if key in self.queries:
            return self.queries[key]
        profile = self.profile(nu, residue)
        lower = upper = 0
        max_lower = max_upper = Fraction(0)
        at_lo = (Fraction(0), Fraction(0))
        at_hi = (Fraction(0), Fraction(0))
        for q, lo, hi, ml, mh in profile["states"]:
            if q > Y:
                break
            lower, upper, max_lower, max_upper = lo, hi, ml, mh
            if q <= qlo - 1:
                at_lo = Fraction(lo, SCALE), Fraction(hi, SCALE)
            if q <= qhi:
                at_hi = Fraction(lo, SCALE), Fraction(hi, SCALE)
        endpoint = (Fraction(lower, SCALE) - Y / profile["phi"],
                    Fraction(upper, SCALE) - Y / profile["phi"])
        max_lower = max(max_lower, absolute_lower(endpoint))
        max_upper = max(max_upper, absolute_upper(endpoint))
        E = max_lower, max_upper
        assert max_lower <= max_upper
        endpoint_lo = add(at_lo, (-Fraction(qlo - 1, profile["phi"]),) * 2)
        endpoint_hi = add(at_hi, (-Fraction(qhi, profile["phi"]),) * 2)
        lo_cert = self.strict.interval(["AP_query", self.query_store.count, nu, residue, qlo - 1], endpoint_lo,
            exact_expression={"profile_ref": profile["id"], "y": qlo - 1, "phi": profile["phi"]})
        hi_cert = self.strict.interval(["AP_query", self.query_store.count, nu, residue, qhi], endpoint_hi,
            exact_expression={"profile_ref": profile["id"], "y": qhi, "phi": profile["phi"]})
        Y_cert = self.strict.interval(["AP_query", self.query_store.count, nu, residue, "Y"], endpoint,
            exact_expression={"profile_ref": profile["id"], "Y": frac(Y), "phi": profile["phi"]})
        E_cert = self.strict.interval(["AP_query", self.query_store.count, nu, residue, "finite_E"], E,
            exact_expression={"profile_ref": profile["id"], "Y": frac(Y), "all_jump_limits_and_Y_max": True})
        position = self.query_store.put({"profile_ref": profile["id"], "nu": nu,
                                         "residue": residue, "Y": frac(Y),
                                         "qlo_minus1": qlo - 1, "qhi": qhi,
                                         "theta_at_qlo_minus1": iv_json(at_lo),
                                         "theta_at_qhi": iv_json(at_hi),
                                         "endpoint_errors": [lo_cert, hi_cert],
                                         "Y_error": Y_cert, "finite_class_E": E_cert,
                                         "max_at_all_jumps_left_limits_and_Y": True,
                                         "module_greater_than_Y": nu > Y,
                                         "not_global_Etheta_or_BV": True})
        result = {"query_ref": position, "E": E, "profile_ref": profile["id"]}
        self.queries[key] = result
        return result


def candidate_cells(factors, j, t, Pmax, primes):
    output = []
    minimum = factors[0][0]
    for p, exponent in factors:
        if p * p > j:
            continue
        v = j // p
        v_factors = [[ell, power - (ell == p)] for ell, power in factors
                     if power - (ell == p) > 0]
        small_divisors = [ell for ell, power in v_factors if ell < p and gcd(ell, t * N) == 1]
        r = len(small_divisors)
        values = {}
        for K in (0, 1):
            value = sum((-1) ** i * comb(r, i) for i in range(min(r, 2 * K + 1) + 1))
            target = 1 if r == 0 else -comb(r - 1, 2 * K + 1)
            assert value == target and value <= (r == 0)
            if r == 0:
                assert p == minimum
            values[str(K)] = value
        output.append({"p": p, "v": v, "p_squared_le_j": True, "v_ge_p": v >= p,
                       "p_divides_v": v % p == 0, "gcd_p_v": gcd(p, v),
                       "v_factors_with_multiplicity": v_factors,
                       "eligible_prime_divisors_of_v": small_divisors, "r": r,
                       "rough_indicator": int(r == 0), "actual_minimum": p == minimum,
                       "L_K0_K1": values, "within_any_test_cut": p <= Pmax,
                       "all_eligible_primes_declared_predicate": "ell prime, ell<p, gcd(ell,t*N)=1"})
    return output
