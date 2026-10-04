"""NEW AP21 actual rational Selberg profiles and complete coefficient axes."""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import gcd, lcm, prod

from arithmetic21 import N, factor, phi, mu, fraction_text


def profile(z: int, p_limit: int, order: int, t: int, p0: int, primes: list[int]) -> dict:
    original = []
    admitted = []
    for k in range(1, z + 1):
        squarefree = mu(k, primes) != 0
        unit = gcd(k, t * N * p0) == 1
        if squarefree and unit:
            admitted.append(k)
        original.append({"k": k, "mu": mu(k, primes), "squarefree": squarefree,
                         "unit_tNp0": unit, "prime_factors_with_multiplicity": factor(k, primes)})
    r_value = {e: prod(p - 2 for p, _ in factor(e, primes)) for e in admitted}
    assert all(value > 0 for value in r_value.values())
    normalization = sum((Fraction(1, r_value[e]) for e in admitted), Fraction(0))
    lambdas = {k: Fraction(0) for k in range(1, z + 1)}
    for k in admitted:
        lambdas[k] = Fraction(mu(k, primes) * phi(k, primes), 1) / normalization * sum(
            (Fraction(1, r_value[e]) for e in admitted if e % k == 0), Fraction(0))
    assert normalization > 0 and lambdas[1] == 1
    quadratic = sum((lambdas[k] * lambdas[l] / phi(lcm(k, l), primes)
                     for k in admitted for l in admitted), Fraction(0))
    assert quadratic == 1 / normalization
    for row in original:
        row["lambda"] = fraction_text(lambdas[row["k"]])
    composite_axes = []
    for p in primes:
        if p > p_limit:
            break
        eligible = [ell for ell in primes if ell < p and gcd(ell, t * N) == 1]
        h_rows = []
        for size in range(len(eligible) + 1):
            for subset in combinations(eligible, size):
                h_rows.append({"h": prod(subset), "mu": (-1) ** size, "omega": size,
                               "subset": list(subset), "xi": (-1) ** size if size <= 2 * order + 1 else 0,
                               "axis": "original_squarefree_primorial_divisor"})
        for ell in eligible:
            h_rows.append({"h": ell * ell, "mu": 0, "omega": 2, "subset": [ell, ell],
                           "xi": 0, "axis": "extended_nonSF_zero_control"})
        composite_axes.append({"p": p, "unit_p_tN": gcd(p, t * N) == 1,
                               "eligible_primes": eligible, "primorial": prod(eligible),
                               "all_h": h_rows})
    return {"z": z, "P": p_limit, "K": order, "t_unit_signature": [p for p in primes if p <= max(z, p_limit) and t % p == 0],
            "original_k": original, "lambdas": lambdas, "G": normalization,
            "quadratic": quadratic, "composite_axes": composite_axes,
            "all_Q_representations": z * z,
            "all_C_original_representations": z * z * sum(
                sum(h["axis"] == "original_squarefree_primorial_divisor" for h in row["all_h"])
                for row in composite_axes),
            "all_C_extended_zero_representations": z * z * sum(
                sum(h["axis"] == "extended_nonSF_zero_control" for h in row["all_h"])
                for row in composite_axes)}


def serial_profile(value: dict) -> dict:
    return {key: (fraction_text(item) if isinstance(item, Fraction) else item)
            for key, item in value.items() if key != "lambdas"}


def components(value: dict, frame: dict):
    """Every original k,l/h, INCLUDING every zero; no favorable-sign selection."""
    for k, lambda_k in value["lambdas"].items():
        for l, lambda_l in value["lambdas"].items():
            conductor = lcm(k, l)
            yield {"kind": "Q", "k": k, "l": l, "p": None, "h": None,
                   "coefficient": lambda_k * lambda_l, "nu": conductor, "U": frame["U"],
                   "p_unit": True, "h_axis": None}
            for axis in value["composite_axes"]:
                p = axis["p"]
                capped = 0 if p * p > N else min(frame["U"], (N - p * p) // frame["t"])
                for h in axis["all_h"]:
                    reduced = conductor // gcd(conductor, p)
                    nu = p * lcm(h["h"], reduced)
                    yield {"kind": "C", "k": k, "l": l, "p": p, "h": h["h"],
                           "coefficient": lambda_k * lambda_l * h["xi"], "nu": nu,
                           "U": capped, "p_unit": axis["unit_p_tN"], "h_axis": h["axis"]}
