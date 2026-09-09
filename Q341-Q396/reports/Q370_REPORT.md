# Q370 Report - Arias Remainder Bound Preparation

## Verdict

```text
Q370_ANALYTIC_BOUND_INFRASTRUCTURE_PARTIAL_PASS
Q370_ARIAS_RAW_REMAINDER_BOUND_PASS : NOT_OBTAINED
Q370_EXPLICIT_ARIAS_BOUND_PASS      : NOT_OBTAINED
```

## Compiled results within the original window

```text
Q370_COMBINED_EXPONENT_IDENTITY_PASS
Q370_GAUSSIAN_DOMINATION_CONDITIONAL_PASS
Q370_RESIDUAL_FACTORIZATION_PASS
Q370_POLYNOMIAL_PREFACTOR_BOUND_PASS
Q370_SEPARABLE_PRODUCT_MAJORANT_CONDITIONAL_PASS
Q370_PRODUCT_INTEGRABILITY_PASS
Q370_FUBINI_FROM_UNIFORM_WITNESSES_PASS
```

The exact outer quadratic exponent, the `sourceF` contribution, the Cauchy
prefactor, moving-pole distance, cosine denominator, and inner inverse powers are
factorized explicitly. Both one-dimensional majorants are integrable.

## Post-deadline technical completion

After explicit user continuation on 2026-08-22, Lean compiled:

```text
Q370_OUTER_COSINE_COERCIVITY_POST_DEADLINE_PASS
Q370_OUTER_COSINE_UNIFORM_LOWER_BOUND_POST_DEADLINE_PASS
```

The theorem `sourceOuterCosineLowerBound` proves a positive uniform lower bound
for the true complex cosine denominator. It uses exact imaginary-part growth at
both ends, `|sinh(Im z)| <= ||cos z||`, continuity, and Q369 pointwise
nonvanishing. This result is not reclassified as a within-timebox pass.

## Remaining analytic leaf

The sole uninhabited premise in the separable product estimate is:

```lean
Q370Probe.SourceFRealGap theta phi
```

It requires a uniform `a > 0` satisfying

```text
a <= 1 + re(sourceF(sourceLinePoint (1/2) phi y))
```

for every real `y`. The primary proof invokes a harmonic/minimum-principle
argument. No specialized axiom, oracle, or circular definition was introduced.

Consequently the semantic Arias bound remains open.
