# Q377 - Primary Taylor remainder to `sourceRgK`

## Verdict

```text
RS5H_ANALYTIC_PARTIAL_FAIL_CLOSED
Q377 : PARTIAL / POST_DEADLINE_CONTINUATION
```

The authorized post-deadline continuation closes the all-order coefficient
gate and the analytic-continuation infrastructure in the Taylor parameter.
It does not close the remaining local transformed-circle-to-source-line
contour theorem.

## Results proved in Lean

The pre-existing Q377 campaign and this continuation prove:

```text
Q377_PRIMARY_TAYLOR_COEFFICIENT_ALL_K_PASS
Q377_EXACT_CAUCHY_REMAINDER_FORMULA_PASS
Q377_CAUCHY_CIRCLE_TRANSPORT_PASS
Q377_LOCAL_REMAINDER_TO_TRANSFORMED_CIRCLE_PASS
Q377_TRANSFORMED_CIRCLE_DOMAIN_GEOMETRY_PASS
Q377_INNER_FAR_FIELD_DECAY_PASS

Q377_TAU_CONTINUATION_DOMAIN_OPEN_PASS
Q377_TAU_CONTINUATION_DOMAIN_PRECONNECTED_PASS
Q377_TAU_LOCAL_DENOMINATOR_GAP_PASS
Q377_SOURCE_RGK_TAU_POINTWISE_DERIVATIVE_PASS
Q377_SOURCE_RGK_TAU_DERIVATIVE_MAJORANT_PASS
Q377_SOURCE_RGK_TAU_DIFFERENTIATION_UNDER_INTEGRAL_PASS
Q377_SOURCE_RGK_TAU_ANALYTIC_PASS
Q377_PRIMARY_REMAINDER_TAU_ANALYTIC_PASS
Q377_IDENTITY_THEOREM_CONNECTOR_PASS
```

The new terminal analytic theorems include:

```lean
hasDerivAt_sourceRgKLineIntegral_tau

analyticOnNhd_sourceRgK_tau

sourcePrimaryRemainder_eq_sourceRgK_on_continuationDomain
```

The last theorem is a sound conditional connector. It consumes a real local
analytic germ:

```lean
SourceLocalCircleLineGerm K z phi
```

and then propagates the equality over the open preconnected continuation
domain by the identity theorem.

## Exact fail-closed boundary

The remaining mathematical obligation is not parameter analyticity. It is the
local contour identity between the transformed Cauchy circle and the complete
source line in a neighborhood of `tau = 0`.

```text
Q377_LOCAL_CIRCLE_LINE_GERM               : NOT_OBTAINED
Q377_INNER_CLOSED_CONTOUR_TO_LINE         : NOT_OBTAINED
SourcePrimaryRemainderOnFinalLine          : UNINHABITED
Q376_SOURCE_RGK_DEFORMATION                : NOT_OBTAINED
Q374_SOURCE_RSFORMULA                      : NOT_OBTAINED
Q375_EXPLICIT_ARIAS_BOUND                  : DEFERRED
BRIDGE_A                                   : OPEN
CARRIER_MEMBERSHIP                         : UNPROVED
TS340_UNCONDITIONAL                        : OPEN_FROZEN
```

Equality only at `tau = 0` would not suffice. A genuine neighborhood equality
must come from the source's Cauchy deformation around the two enclosed poles
`0` and `-2*i*z*tau` while avoiding the principal-log cut `[1,+infinity)`.

## Verification

```text
Q377 root build       : PASS, graph 2330
Q377 source modules   : 39/39 imported by Q377Probe.lean
Axiom audit           : propext, Classical.choice, Quot.sound
Forbidden source scan : EMPTY
git diff --check      : PASS
HEAD                  : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
origin/main           : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
Worktree              : DETACHED
Permanent Git action  : NONE
Active Lean/Lake/Python processes : 0
```

All results added on 2026-08-24 are classified
`POST_DEADLINE_CONTINUATION`.
