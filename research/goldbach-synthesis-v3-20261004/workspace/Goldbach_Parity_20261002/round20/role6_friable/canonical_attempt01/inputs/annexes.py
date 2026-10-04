"""NEW complete finite Euler/Rankin and totient annexes, not source budgets."""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import prod

from core import Arithmetic, exp_interval, root_interval, strict_certificate, text
from outward import add, iv_json, mul, scale


def power(bounds, exponent):
    result = (Fraction(1), Fraction(1))
    for _ in range(exponent):
        result = mul(result, bounds)
    return result


def euler_rankin(arithmetic: Arithmetic) -> dict:
    primes = (2, 3, 5, 7)
    roots, parameters = [], []
    for p in primes:
        root, certificate = root_interval(p ** 3, 4)
        assert root[0] > 0
        t = (1 / root[1], 1 / root[0])
        assert 0 < t[0] <= t[1] < 1
        roots.append(certificate)
        parameters.append(t)
    rows = []
    polynomial = {}
    tau_polynomial = {}
    distinct_m = set()
    direct = direct_tau = (Fraction(0), Fraction(0))
    powers = [[power(t, e) for e in range(7)] for t in parameters]
    for exponents in product(range(7), repeat=4):
        m = prod(p ** e for p, e in zip(primes, exponents))
        tau = prod(e + 1 for e in exponents)
        assert m not in distinct_m
        distinct_m.add(m)
        expected_factors = tuple((p, e) for p, e in zip(primes, exponents) if e)
        assert arithmetic.factors(m) == expected_factors
        assert len(arithmetic.divisors(m)) == tau
        term = (Fraction(1), Fraction(1))
        for values, e in zip(powers, exponents):
            term = mul(term, values[e])
        weighted = scale(term, tau)
        direct = add(direct, term)
        direct_tau = add(direct_tau, weighted)
        polynomial[exponents] = 1
        tau_polynomial[exponents] = tau
        rows.append({"exponents": list(exponents), "m": m, "tau": tau,
                     "factors_with_repetitions": [[p, e] for p, e in expected_factors],
                     "term_interval": strict_certificate(term), "tau_term_interval": strict_certificate(weighted)})
    expanded = {(): 1}
    expanded_tau = {(): 1}
    for _ in primes:
        expanded = {old + (e,): coefficient for old, coefficient in expanded.items() for e in range(7)}
        expanded_tau = {old + (e,): coefficient * (e + 1)
                        for old, coefficient in expanded_tau.items() for e in range(7)}
    assert expanded == polynomial and expanded_tau == tau_polynomial and len(rows) == 2401
    factor_product = factor_tau = infinite_plus = infinite_tau = (Fraction(1), Fraction(1))
    for t, values in zip(parameters, powers):
        finite = (sum((v[0] for v in values), Fraction(0)), sum((v[1] for v in values), Fraction(0)))
        weighted = (sum(((e + 1) * v[0] for e, v in enumerate(values)), Fraction(0)),
                    sum(((e + 1) * v[1] for e, v in enumerate(values)), Fraction(0)))
        factor_product = mul(factor_product, finite)
        factor_tau = mul(factor_tau, weighted)
        infinite = (1 / (1 - t[0]), 1 / (1 - t[1]))
        infinite_plus = mul(infinite_plus, infinite)
        infinite_tau = mul(infinite_tau, mul(infinite, infinite))
    assert direct == factor_product and direct_tau == factor_tau
    assert direct[1] < infinite_plus[0] and direct_tau[1] < infinite_tau[0]
    enumerations = []
    for upper in (64, 112):
        integers = []
        members = []
        for n in range(1, upper + 1):
            row = arithmetic.record(n)
            smooth = row["largestPrime"] <= 7
            selected = 16 <= n <= upper and smooth
            integers.append({"n": n, "factors": row["factors"], "tau": row["tau"],
                             "smooth7": smooth, "selected": selected})
            if selected:
                members.append(n)
                assert n in distinct_m
        inverse_sum = sum((Fraction(1, n) for n in members), Fraction(0))
        tau_sum = sum(arithmetic.record(n)["tau"] for n in members)
        rankin = scale(infinite_plus, Fraction(1, 2))
        tau_rankin = scale(infinite_tau, Fraction(upper, 2))
        assert inverse_sum <= rankin[0]
        assert len(members) <= upper * inverse_sum
        assert tau_sum <= tau_rankin[0]
        enumerations.append({"upper": upper, "full_integer_axes": upper, "all_integer_rows": integers,
                             "B_members": members, "inverse_sum": text(inverse_sum), "card": len(members),
                             "tau_sum": tau_sum, "D_minus_sigma": "1/2", "rankin_bound": iv_json(rankin),
                             "rankin_gap": strict_certificate((rankin[0] - inverse_sum, rankin[1] - inverse_sum)),
                             "card_bound_gap": text(upper * inverse_sum - len(members)),
                             "tau_rankin_bound": iv_json(tau_rankin),
                             "tau_rankin_gap": strict_certificate((tau_rankin[0] - tau_sum, tau_rankin[1] - tau_sum)),
                             "not_source_B_D": True})
    return {"Y_E": 7, "D_E": 16, "K_E": 6, "sigma_E": "1/4", "tuples": rows,
            "tuple_count": len(rows), "fourth_root_certificates": roots,
            "geometric_parameters": [iv_json(t) for t in parameters],
            "polynomial_product_identity_exact": True, "tau_polynomial_product_identity_exact": True,
            "truncated_geometric_sum": iv_json(direct), "truncated_tau_sum": iv_json(direct_tau),
            "finite_Eplus_interval": iv_json(infinite_plus), "finite_Eplus_square_interval": iv_json(infinite_tau),
            "positive_infinite_tail_gap": strict_certificate((infinite_plus[0] - direct[1], infinite_plus[1] - direct[0])),
            "positive_tau_infinite_tail_gap": strict_certificate((infinite_tau[0] - direct_tau[1], infinite_tau[1] - direct_tau[0])),
            "full_integer_enumerations": enumerations, "source_exponents_27_37_33_39_not_certified": True}


def totient_annex(arithmetic: Arithmetic) -> dict:
    bound = 4096
    harmonic = [Fraction(0)]
    tk = [Fraction(0)]
    rows = []
    sf_inverse = Fraction(0)
    euler = Fraction(1)
    for p in arithmetic.primes:
        if p > bound:
            break
        euler *= 1 + Fraction(1, p * (p - 1))
    for n in range(1, bound + 1):
        divisors = arithmetic.divisors(n)
        sf_divisors = [d for d in divisors if arithmetic.mu[d] != 0]
        inverse = sum((Fraction(1, arithmetic.phi[d]) for d in sf_divisors), Fraction(0))
        assert inverse == Fraction(n, arithmetic.phi[n])
        harmonic.append(harmonic[-1] + Fraction(1, n))
        tk.append(tk[-1] + Fraction(1, arithmetic.phi[n]))
        if arithmetic.mu[n]:
            sf_inverse += Fraction(1, n * arithmetic.phi[n])
        log = arithmetic.oracle.log(n)
        envelope = (3 * (1 + log[0]), 3 * (1 + log[1]))
        assert tk[-1] <= envelope[0]
        rows.append({"n": n, "phi": int(arithmetic.phi[n]), "mu": int(arithmetic.mu[n]),
                     "divisors": divisors, "SF_divisors": sf_divisors, "actual_n_over_phi": text(inverse),
                     "finite_TK": text(tk[-1]), "TK_bound": iv_json(envelope),
                     "TK_gap": strict_certificate((envelope[0] - tk[-1], envelope[1] - tk[-1]))})
    exchanged = sum((Fraction(1, d * arithmetic.phi[d]) * harmonic[bound // d]
                     for d in range(1, bound + 1) if arithmetic.mu[d]), Fraction(0))
    assert exchanged == tk[bound]
    telescope = sum((Fraction(1, j * (j - 1)) for j in range(2, bound + 1)), Fraction(0))
    assert telescope == 1 - Fraction(1, bound)
    exp_telescope = exp_interval((telescope, telescope))
    exp_one = exp_interval((Fraction(1), Fraction(1)))
    assert sf_inverse <= euler < exp_telescope[0]
    assert exp_telescope[1] < exp_one[0] and exp_one[1] < 3
    assert harmonic[bound] <= 1 + arithmetic.oracle.log(bound)[0]
    return {"all_n1through4096": rows, "integer_axes": bound,
            "n_over_phi_SF_divisor_identity_all_exact": True,
            "TK_exchange_actual": text(exchanged), "TK_actual": text(tk[bound]),
            "harmonic_actual": text(harmonic[bound]), "SF_inverse_dphi_sum": text(sf_inverse),
            "positive_SF_Euler_product": text(euler), "SF_sum_le_Euler_exact": True,
            "telescope_actual": text(telescope), "telescope_equals1minus1overX": True,
            "exp_telescope_interval": iv_json(exp_telescope), "exp1_interval": iv_json(exp_one),
            "exp1_lt3_certified": True, "uniform_TK_Lean_theorem_not_claimed": True}
