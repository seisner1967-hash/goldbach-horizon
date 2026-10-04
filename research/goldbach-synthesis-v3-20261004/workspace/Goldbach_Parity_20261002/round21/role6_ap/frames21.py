"""NEW independent witness/frame catalogue and all physical candidates AP21."""
from __future__ import annotations

from bisect import bisect_left, bisect_right
from math import gcd

from arithmetic21 import N, X, LEFT, RIGHT, ceildiv, bitmap_observation, factor


def static_axes(c: int, r: int, s: int, a: int) -> bool:
    return (c < r < s <= a and c * r <= a and c * s <= a < r * s
            and a < c * r * s and gcd(c * r * s, N) == 1)


def witness(c: int, r: int, s: int, q: int, a: int, m: int, original_q: int, z: int,
            prime_q: bool = True) -> bool:
    """Literal independent fields; never inspects Prime(j)."""
    b = s * q
    candidate = N - c * r * b
    return (prime_q and static_axes(c, r, s, a) and s < q and a < q and r * s < q
            and gcd(c * r * b, N) == 1 and m <= c * r * b
            and c * r * b + original_q < N and 2 <= candidate
            and z < candidate and LEFT < candidate <= RIGHT)


def endpoints(t: int, r: int, s: int, a: int, m: int, original_q: int) -> tuple[int, int]:
    lower = max(a + 1, r * s + 1, ceildiv(N - X, t), ceildiv(m, t))
    upper = min((N - X // 2 - 1) // t, (N - original_q - 1) // t)
    return lower, upper


def cap(upper: int, p: int, t: int) -> tuple[int, bool]:
    return (0, True) if p * p > N else (min(upper, (N - p * p) // t), False)


def catalogue(primes: list[int], a: int, m: int, original_q: int,
              bitmap: dict, stream) -> tuple[list[dict], dict]:
    axes_primes = [p for p in primes if p <= a and gcd(p, N) == 1]
    q_primes = [p for p in primes if p < 10000]
    frames = []
    diagnostics = {"frames": 0, "empty_frames": 0, "physical_q_before_j_prime": 0,
                   "prime_j": 0, "composite_j": 0, "mu_zero_j": 0, "properpower_j": 0,
                   "repeated_minfac": 0, "nonminimal_negative_control_cells": 0,
                   "boundary_queries": 0}
    falsifiers = {}
    for c in axes_primes:
        for r in axes_primes:
            if r <= c or c * r > a:
                continue
            for s in axes_primes:
                if not static_axes(c, r, s, a):
                    continue
                t = c * r * s
                lower, upper = endpoints(t, r, s, a, m, original_q)
                assert upper < 10000
                physical = [q for q in q_primes if witness(c, r, s, q, a, m, original_q, 23)]
                interval = [q for q in q_primes if lower <= q <= upper and gcd(q, N) == 1]
                assert physical == interval
                for q in (lower - 1, lower, upper, upper + 1):
                    boundary_factors = factor(q, primes) if q >= 1 else []
                    boundary_prime = len(boundary_factors) == 1 and boundary_factors[0][1] == 1
                    assert witness(c, r, s, q, a, m, original_q, 23, boundary_prime) == (
                        boundary_prime and lower <= q <= upper and gcd(q, N) == 1)
                    diagnostics["boundary_queries"] += 1
                frame = {"id": len(frames), "c": c, "r": r, "s": s, "t": t,
                         "L": lower, "U": upper, "empty_window": lower > upper,
                         "physical_q": physical, "source_x_interval_true": N // 5 <= X <= N // 4}
                frames.append(frame)
                diagnostics["frames"] += 1
                diagnostics["empty_frames"] += lower > upper
                observations = []
                for q in physical:
                    observed = bitmap_observation(N - t * q, bitmap, primes)
                    observed["q"] = q
                    p = observed["minfac"]
                    capped, n_truncation = cap(upper, p, t)
                    assert not n_truncation or observed["prime"]
                    assert (q <= capped) == (p * p <= observed["j"])
                    diagnostics["physical_q_before_j_prime"] += 1
                    diagnostics["prime_j"] += observed["prime"]
                    diagnostics["composite_j"] += not observed["prime"]
                    diagnostics["mu_zero_j"] += observed["mu"] == 0
                    diagnostics["properpower_j"] += observed["properpower"]
                    diagnostics["repeated_minfac"] += not observed["prime"] and observed["j"] % (p * p) == 0
                    if observed["properpower"] and observed["mu"] == 0:
                        falsifiers.setdefault("raw_mu_zero_mask", {"frame": frame["id"], **observed})
                    if not observed["prime"]:
                        falsifiers.setdefault("q_selected_after_Prime_j", {"frame": frame["id"], **observed})
                        for bad_p, _ in observed["factors_with_multiplicity"][1:]:
                            if observed["j"] % bad_p == 0 and bad_p * bad_p <= observed["j"]:
                                smaller_distinct = sum(ell < bad_p for ell, _ in observed["factors_with_multiplicity"])
                                lower_K0 = 1 - smaller_distinct
                                diagnostics["nonminimal_negative_control_cells"] += lower_K0 < 0
                                if lower_K0 < 0:
                                    falsifiers.setdefault("nonminimal_negative_Bonferroni_K0", {
                                        "frame": frame["id"], "p": bad_p, "j": observed["j"],
                                        "eligible_divisors_below_p": smaller_distinct,
                                        "lower_K0": lower_K0})
                    if not observed["prime"] and observed["j"] == p * p:
                        falsifiers.setdefault("strict_square_cap", {"frame": frame["id"], **observed})
                    observations.append(observed)
                stream.emit({"kind": "full_static_frame_with_independent_bridge", "frame": frame,
                             "independent_domain_equal": True, "all_q_before_prime_j_mask": True,
                             "physical_candidate_observations": observations,
                             "composite_cap_control_prime_gt_sqrt_N": {"p": 10009,
                                                                         "cap": cap(upper, 10009, t)}})
    assert sum(len(frame["physical_q"]) for frame in frames) == diagnostics["physical_q_before_j_prime"]
    assert 3 * (a + 1) * 10000 > N - LEFT
    return frames, {"diagnostics": diagnostics, "falsifiers": falsifiers,
                    "q_sieve_bound_justification": "t>=3*(a+1), q<(N-LEFT)/t<10000",
                    "all_canonical_static_axes_retained": True,
                    "historical_overlap": {"round19": [LEFT + 1, 24_000_000],
                                           "round20": [24_000_001, RIGHT],
                                           "claimed_disjoint": False}}
