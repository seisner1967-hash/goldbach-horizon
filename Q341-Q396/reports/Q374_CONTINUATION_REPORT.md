# Q374 continuation — source polynomial and remainder boundary

Verdict: `Q374_CONTINUATION_STRUCTURAL_AND_CONDITIONAL_PROGRESS`

## Proven in Lean

- Independent Cauchy Taylor tail defined by `tsum`, not by subtraction.
- Exact finite-sum-plus-tail identity on every valid Cauchy disk.
- Local `K = 0` agreement between the primary polynomial and Cauchy
  polynomial, with `g - P_0` equal to that independent local tail.
- Exact 2024 definitions of the physicists' Hermite basis, `U_k`, `P_k`, and
  the finite primary polynomial.
- Degree bounds `deg H_n <= n`, `deg U_k <= 3k`, `deg P_k <= 3k`.
- Exact source normalization `defUk` and coefficient support.
- Exact rational recurrences `coef_d1` (both forms) and exceptional `coef_d2`,
  transported from Q365 by the published `(-1)^k` convention.
- Hermite derivative and multiplication identities used by the source.
- A theorem converting the isolated primary-remainder equality into the full
  Q376 outer-contour binding.

## Classification

```text
Q374_PRIMARY_POLYNOMIAL_SPINE_PASS             : PROVEN_IN_LEAN
Q374_PRIMARY_COEFFICIENT_RECURRENCE_PASS        : PROVEN_IN_LEAN
Q374_LOCAL_CAUCHY_TAYLOR_IDENTITY_PASS          : PROVEN_IN_LEAN
Q374_K0_LOCAL_PRIMARY_COEFFICIENT_PASS          : PROVEN_IN_LEAN
Q374_TAYLOR_TO_LINE_CONNECTOR_PASS              : CONDITIONAL
Q374_SOURCE_RGK_SUBSTITUTION_PASS               : NOT_OBTAINED
Q374_SOURCE_RS_REMAINDER_RECONSTRUCTION_PASS    : NOT_OBTAINED
Q374_SOURCE_RSFORMULA_PASS                      : NOT_OBTAINED
Q374_COEFFICIENT_COMPATIBILITY_PASS             : NOT_OBTAINED
Q374_DISTINCT_EXPANSIONS_CONFIRMED              : PROVENANCE_BOUNDARY_PRESERVED
Q374_NORMALIZED_HARDY_Z_SOURCE_DECOMPOSITION    : NOT_ATTEMPTED
```

The recurrence agreement does not yet prove that the named `P_k` are the
Taylor coefficients of `sourcePrimaryGRegular` for every `k`. It also does not
prove the inner contour transformation from the analytic Taylor remainder to
the independent `sourceRgK` line integral. These are the exact remaining
source-level leaves before `RSformula`.
