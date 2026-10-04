"""SOURCE ONLY: one exact rational upper bound for a scalar Mellin radius.

NUMERIC_RADIUS_BOUND_ONLY_NOT_IDENTITY_OR_LEAN_PROOF

This file has not been executed, imported, parsed by a candidate tool, or
prepared. An independent SOURCE review and a ROOT gate are required before
any future mathematical invocation. All arithmetic below is exact integer
or fractions.Fraction arithmetic. No float, Decimal, exp, quadrature, prime
enumeration, Dirichlet-series evaluation, or coefficient evaluation occurs.

Conditional real-number inputs, explained in source_contract22.md:
  U(1/N) <= N**2, d(1/N) >= 1/(8*N), pi > 3, exp(1) < 3.
They imply epsilon <= 64*N**3*exp(-H/(8*N)). At the fixed point H/(8*N)=125,
the positive Taylor partial sum S bounds exp(125) from below, so q=1/S
bounds exp(-125) from above and q*q bounds exp(-250) from above.

Only the scalar closed-radius upper bound is compared to tau. A future
successful comparison does not prove the underlying real inequalities in
Lean, establish C_N or D_N, or validate the SOURCE34DECL module/imports.
All prime powers remain in the objects of the upstream mathematical contract.
"""

from fractions import Fraction
import json


SCOPE = "NUMERIC_RADIUS_BOUND_ONLY_NOT_IDENTITY_OR_LEAN_PROOF"
UPSTREAM_SOURCE_SHA256 = (
    "bf9b8257760a20d33dd21714221401cd8fd327596f72e56c4d024200b2cb6c4c"
)
N = 100_000_000
H = 100_000_000_000
TAU = Fraction(1, 1_000_000)
TAYLOR_DEGREE = 150


def positive_taylor_lower(x: Fraction, degree: int) -> Fraction:
    """Return exactly sum(x**k/k!, k=0..degree); x must be nonnegative.

    For real x >= 0, positivity of the exponential Taylor series gives
    exp(x) >= this finite rational sum. There is no estimated remainder.
    """
    if x < 0 or degree < 0:
        raise ValueError("Nonnegative Taylor argument and degree required")
    term = Fraction(1)
    total = term
    for k in range(1, degree + 1):
        term = term * x / k
        total += term
    return total


def exact_fraction(value: Fraction) -> dict:
    """Decimal strings encode exact integers, never rounded decimals."""
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
    }


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def build_radius_bound() -> dict:
    a = Fraction(1, N)
    exponent = Fraction(H, 8 * N)
    d_lower = Fraction(1, 8 * N)
    require(N > 0 and H >= 0 and TAU > 0, "Fixed-point domain violated")
    require(a * N == 1, "The exp(a*N) < 3 substitution is unavailable")
    require(exponent == 125, "This SOURCE supports only exponent 125")
    require(TAYLOR_DEGREE == 6 * 25, "Fixed Taylor-degree witness changed")

    taylor_sum = positive_taylor_lower(exponent, TAYLOR_DEGREE)
    require(taylor_sum > 0, "Positive reciprocal denominator required")

    # Justification for the fixed degree, not an adaptive search:
    # S_6(5)^25 <= S_150(125), since each product multi-index has total
    # degree <= 150 and the multinomial identity embeds its positive terms
    # in the coefficients of exp(25*5). Also S_6(5) > 100, exactly.
    # These checks supply a conservative rational witness S_150(125)>10^50.
    block_sum = positive_taylor_lower(Fraction(5), 6)
    block_product = block_sum ** 25
    require(block_sum > 100, "The fixed positive block witness failed")
    require(taylor_sum >= block_product, "Multinomial lower-bound check failed")
    require(taylor_sum > 10 ** 50, "The fixed-degree lower witness failed")

    q = Fraction(1) / taylor_sum
    q_squared = q * q
    u_upper = Fraction(N ** 2)
    epsilon_upper = 64 * N ** 3 * q
    radius_upper = 3 * (2 * u_upper * epsilon_upper + epsilon_upper ** 2)
    expanded_upper = 3 * (128 * N ** 5 * q + 4096 * N ** 6 * q_squared)
    require(radius_upper == expanded_upper, "Exact algebraic expansion failed")
    require(radius_upper > 0, "A positive majorant is required")

    # Strict comparison is also exposed as a checkable integer inequality.
    cross_left = radius_upper.numerator * TAU.denominator
    cross_right = TAU.numerator * radius_upper.denominator
    below_target = cross_left < cross_right
    require(below_target == (radius_upper < TAU), "Comparison mismatch")

    return {
        "schema": "ROUND22_EXACT_SCALAR_RADIUS_BOUND_OUTPUT",
        "scope": SCOPE,
        "comparison_status": (
            "RATIONAL_UPPER_BOUND_LT_TAU" if below_target
            else "RATIONAL_UPPER_BOUND_NOT_LT_TAU"
        ),
        "upstream_source_sha256": UPSTREAM_SOURCE_SHA256,
        "upstream_source_status": "SOURCE34DECL_NO_PASS_CREDIT_FROM_THIS_TOOL",
        "parameters": {
            "N": N,
            "a": exact_fraction(a),
            "H": H,
            "tau": exact_fraction(TAU),
            "d_lower": exact_fraction(d_lower),
            "H_over_8N": exact_fraction(exponent),
            "taylor_degree": TAYLOR_DEGREE,
        },
        "positive_taylor_sum_lower_for_exp_125": exact_fraction(taylor_sum),
        "fixed_degree_witness": {
            "S6_at_5": exact_fraction(block_sum),
            "S6_at_5_power_25": exact_fraction(block_product),
            "S6_at_5_gt_100": block_sum > 100,
            "S150_at_125_ge_block_product": taylor_sum >= block_product,
            "S150_at_125_gt_10_power_50": taylor_sum > 10 ** 50,
        },
        "upper_for_exp_minus_125": exact_fraction(q),
        "upper_for_exp_minus_250": exact_fraction(q_squared),
        "U_upper": exact_fraction(u_upper),
        "epsilon_upper": exact_fraction(epsilon_upper),
        "closed_radius_upper": exact_fraction(radius_upper),
        "strict_comparison_integer_witness": {
            "left_radius_numerator_times_tau_denominator": str(cross_left),
            "right_tau_numerator_times_radius_denominator": str(cross_right),
            "left_lt_right": below_target,
        },
        "conditional_real_inputs": [
            "U(1/N) <= N^2",
            "d(1/N) >= 1/(8N)",
            "pi > 3",
            "exp(1) < 3",
            "Positive exponential Taylor series and exp(-250)=exp(-125)^2",
        ],
        "limits": {
            "real_inputs_machine_verified_in_Lean": False,
            "closed_radius_itself_evaluated": False,
            "coefficient_identity_tested": False,
            "C_N_evaluated": False,
            "D_N_evaluated": False,
            "prime_powers_removed": False,
            "D_truncation_error_paid": False,
            "inner_or_outer_quadrature_error_paid": False,
            "kernel_or_node_or_weight_error_paid": False,
            "upstream_Lean_elaboration_established": False,
            "WIN_established": False,
        },
    }


def main() -> int:
    result = build_radius_bound()
    print(json.dumps(result, ensure_ascii=True, indent=2, sort_keys=True))
    return 0 if result["comparison_status"] == "RATIONAL_UPPER_BOUND_LT_TAU" else 2


if __name__ == "__main__":
    raise SystemExit(main())
