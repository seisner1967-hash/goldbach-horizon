"""NEW literal whole-window reference M0; every b is visited, including A_d=0."""
from __future__ import annotations

from fractions import Fraction
from math import gcd

from arithmetic import N, LEFT, RIGHT, A, M, Q_ORIGINAL, H, ceildiv, all_divisors, mobius, frac, map_json
from outward import SCALE, add
from storage import binary_catalog


def evaluate_reference(pair, beta_b, flags, properpower, primes, oracle, templates, outdir, store, strict):
    c, r, d = pair
    bmin = ceildiv(N - RIGHT, d)
    bmax = ceildiv(N - LEFT, d) - 1
    L = max(0, bmax - bmin + 1)
    X = d * (L - 1) + 1 if L else 0
    assert X == (N - d * bmin) - (N - d * bmax) + 1 if L else X == 0
    assert all(bmin <= b <= bmax for b in beta_b)
    Ad = len(beta_b)
    bitmap = bytearray(L)
    J = 0
    theta_j = []
    pp_entries = []
    pp_map = {}
    lower = upper = 0
    physical_seen = 0
    for offset, b in enumerate(range(bmin, bmax + 1)):
        j = N - d * b
        assert LEFT < j <= RIGHT
        unit_N = gcd(b, N) == 1
        unit0 = gcd(b, N * H) == 1
        prime = bool(flags[j - LEFT - 1] & 1)
        power = properpower.get(j)
        beta = b in beta_b
        front = M <= d * b and d * b + Q_ORIGINAL < N
        unit_d = gcd(b, d) == 1
        bitmap[offset] = (int(unit0) | (int(prime) << 1) | (int(power is not None) << 2)
                          | (int(beta) << 3) | (int(unit_N) << 4) | (int(unit_d) << 5)
                          | (int(front) << 6) | (int(prime or power is not None) << 7))
        physical_seen += beta
        if not unit0:
            continue
        J += 1
        if prime:
            assert gcd(j, N) == 1
            theta_j.append(j)
            lo, hi = oracle.scaled(j)
            lower += lo
            upper += hi
        elif power is not None:
            assert gcd(j, N) == 1
            base, exponent = power
            pp_entries.append({"b": b, "j": j, "base_prime": base, "exponent": exponent,
                               "raw_uses_log_base": True, "theta_zero": True})
            pp_map[base] = pp_map.get(base, Fraction(0)) + 1
    assert physical_seen == Ad and len(bitmap) == L
    density = Fraction(Ad, J) if J else Fraction(0)
    theta_sum = Fraction(lower, SCALE), Fraction(upper, SCALE)
    pp_sum = oracle.vector(pp_map)
    theta_mass = theta_sum[0] * density, theta_sum[1] * density
    pp_mass = pp_sum[0] * density, pp_sum[1] * density
    raw_mass = add(theta_mass, pp_mass)
    e0 = 1
    for ell in (3, 13):
        if N % ell:
            e0 *= ell
    IE = [{"k": k, "mu": mobius(k, primes), "d_times_k": d * k,
           "phi_actual_dk": templates.totient(d * k)} for k in all_divisors(e0, primes)]
    a0 = sum((Fraction(row["mu"], row["phi_actual_dk"]) for row in IE), Fraction(0))
    delta0 = Fraction(templates.totient(N * H), N * H)
    Md = Fraction(Ad * X, L) * a0 / delta0 if L else Fraction(0)
    bitmap_info = binary_catalog(outdir / f"reference_b_axes_d{d}.bin.gz", bitmap,
                                {"first_b": bmin, "last_b": bmax, "count": L,
                                 "byte_bits": ["unit_Nh", "j_prime", "j_properpower", "physical_beta",
                                               "unit_N", "unit_d", "literal_bulk_front", "j_prime_or_properpower"],
                                 "one_byte_every_integer_before_masks": True, "A_zero_fibres_also_complete": True})
    record = {"c": c, "r": r, "d": d, "bmin": bmin, "bmax": bmax,
              "L": L, "X_literal_d_times_Lminus1_plus1": X,
              "forbidden_d_times_L": d * L, "front_difference": d * L - X,
              "all_b_bitmap": bitmap_info, "A_d_actual": Ad, "J_U0_actual": J,
              "reference_density": frac(density), "theta_logj_keys_all": theta_j,
              "properpower_entries_all": pp_entries, "properpower_logbase_map": map_json(pp_map),
              "M0_theta_expression": "(A_d/J_U0)*sum_{all b unit_Nh} theta_N(N-d*b)",
              "M0_raw_expression": "M0_theta + (A_d/J_U0)*properpower_logbase_sum",
              "M0_theta_interval": [frac(v) for v in theta_mass],
              "M0_PP_reference0_interval": [frac(v) for v in pp_mass],
              "M0_raw_interval": [frac(v) for v in raw_mass],
              "old_rank_price_not_reexecuted_or_credited": True,
              "e0_actual": e0, "a0_actual_IE": IE, "a0": frac(a0), "delta0": frac(delta0),
              "Md_model_principal_separate": frac(Md), "Md_not_M0_substitution": True,
              "all_b_visited": L, "raw_raccord_exact_coefficient_maps": True,
              "coefficient_map_compression": "theta keys all with single exact density; PP basis map all"}
    future_ref = store.count
    record["strict_M0theta_certificate"] = strict.interval(["reference", future_ref, d, "M0theta"], theta_mass,
        exact_zero=density == 0 or not theta_j,
        exact_expression={"reference_fibre_ref": future_ref, "density": frac(density), "theta_keys_all_stored": True})
    record["strict_PPref_certificate"] = strict.interval(["reference", future_ref, d, "PPref"], pp_mass,
        exact_zero=density == 0 or not pp_map,
        exact_expression={"reference_fibre_ref": future_ref, "density": frac(density), "all_PP_basis_coefficients": map_json(pp_map)})
    record["strict_M0raw_certificate"] = strict.interval(["reference", future_ref, d, "M0raw"], raw_mass,
        exact_zero=density == 0 or not theta_j and not pp_map,
        exact_expression={"reference_fibre_ref": future_ref, "M0raw_equals_theta_plus_PP": True})
    record["strict_separate_Md_rational_certificate"] = strict.interval(["reference", future_ref, d, "Md_model"], (Md, Md),
        exact_zero=Md == 0, exact_expression={"rational": frac(Md), "not_M0_substitution": True})
    position = store.put(record)
    return {"position": position, "theta": theta_mass, "pp": pp_mass, "raw": raw_mass,
            "Md": (Md, Md), "A": Ad, "J": J, "L": L, "bitmap": bitmap_info,
            "theta_positions": len(theta_j), "pp_positions": len(pp_entries),
            "c": c, "r": r, "d": d}
