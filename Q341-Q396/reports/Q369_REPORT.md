# Q369 Report - Targeted RSformula Transport

## Verdict

```text
Q369_ANALYTIC_PARTIAL_PASS
Q369_SOURCE_RSFORMULA_PASS                 : NOT_OBTAINED
Q369_NORMALIZED_HARDY_Z_DECOMPOSITION_PASS: NOT_OBTAINED
```

## Compiled results

The following source-specific layers compile against Lean 4.15.0 and the pinned
Mathlib revision:

```text
Q369_AFFINE_LINE_GEOMETRY_PASS
Q369_GAMMA_REGIME_POLE_AVOIDANCE_PASS
Q369_PRINCIPAL_BRANCH_AVOIDANCE_PASS
Q369_INNER_DENOMINATOR_NONZERO_PASS
Q369_RGK_MEASURABLE_PASS
Q369_RGK_ABSOLUTELY_INTEGRABLE_PASS
Q369_TRUNCATED_RECTANGLE_CAUCHY_PASS
Q369_TRANSVERSE_SIDE_DECAY_REDUCTION_PASS
Q369_AFFINE_DEFORMATION_REDUCTION_PASS
```

The inner `Rg_(K+1)` integrand is proved absolutely integrable for every `K`
under the exact primary-source parameters. The exact double kernel is measurable,
and its iterated integral is definitionally connected to the independent
`sourceRSRemainder` from Q366.

The contour layer proves Cauchy's theorem on each truncated rectangle and a
parallel-line deformation theorem from explicit line integrability and scalar
side envelopes tending to zero.

## Conditional gates

The following results are sound but retain visible premises:

```text
Q369_DOUBLE_KERNEL_PRODUCT_BOUND_CONDITIONAL_PASS
Q369_FUBINI_CONDITIONAL_PASS
Q369_PARALLEL_LINE_DEFORMATION_CONDITIONAL_PASS
```

The product majorant and Fubini theorem require `Q370Probe.SourceFRealGap` and
`Q370Probe.OuterCosineLowerBound`. The cosine premise is now inhabited by a
post-deadline theorem; `SourceFRealGap` is not.

The source-specific transverse-side bounds are not inhabited, so the infinite
parallel-line deformation and the full source `RSformula` remain open.

## Not obtained

```text
Q369_DOUBLE_KERNEL_PRODUCT_BOUND_PASS : NOT_OBTAINED
Q369_FUBINI_INTERCHANGE_PASS          : NOT_OBTAINED
Q369_TRANSVERSE_SIDES_VANISH_PASS     : NOT_OBTAINED
Q369_PARALLEL_LINE_DEFORMATION_PASS   : NOT_OBTAINED
Q369_SOURCE_RSFORMULA_PASS            : NOT_OBTAINED
Q369_AUXILIARY_TO_ZETA_PASS           : NOT_OBTAINED
Q369_CRITICAL_PHASE_TRANSPORT_PASS    : NOT_OBTAINED
Q369_NORMALIZED_HARDY_Z_DECOMPOSITION_PASS : NOT_OBTAINED
```

No equality with Hardy Z is claimed.
