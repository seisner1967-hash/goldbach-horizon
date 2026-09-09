# Q383 report - Mordell to auxiliary-zeta Mellin transport

## Verdict

```text
Q383_ANALYTIC_PARTIAL_FAIL_CLOSED
Classification : POST_DEADLINE_USER_AUTHORIZED
Original timebox: OVERRUN
```

Q383 closes the analytic infrastructure on the theta/Mellin side, including
the exact justified exchange between the theta series and its line integral.
It does not close the independent transport from the primary auxiliary Mordell
contour to the theta representation `E:Rthetados`.

## Proven in Lean

```text
Q383_MORDELL_REGULARIZED_EXTENSION_PASS
Q383_MORDELL_ZERO_VALUE_EQ_NEG_HALF_PASS
Q383_MELLIN_SEED_DOMAIN_OPEN_PASS
Q383_MELLIN_SEED_DOMAIN_NONEMPTY_PASS
Q383_THETA_NEAR_ZERO_MAJORANT_PASS
Q383_THETA_FAR_FIELD_MAJORANT_PASS
Q383_THETA_LINE_INTEGRABILITY_PASS
Q383_THETA_ABSOLUTE_SERIES_MAJORANT_PASS
Q383_THETA_SUM_INTEGRAL_EXCHANGE_PASS
Q383_GAUSSIAN_MELLIN_TERM_PASS
Q383_MELLIN_SUM_EQ_DIRICHLET_SERIES_PASS
Q383_GAMMA_PI_NORMALIZATION_PASS
Q383_GAUSSIAN_MELLIN_EQ_COMPLETED_ZETA_ON_SEED_PASS
```

The central compiled theta-side theorems are:

```lean
sourceRThetaLineIntegral_eq_tsum_integrals
sourceGaussianMellin_eq_sourceCompletedZeta_on_seed
```

The Mordell closed form has also been regularized at zero as a single analytic
combination, with removable value `-1/2`:

```lean
sourceMordellRegularizedKernel_analyticAt
sourceMordellRegularizedKernel_zero
sourceMordellClosedForm_tendsto_neg_half
```

## Conditional connector

`AuxiliaryThetaGap.lean` defines the proposition:

```lean
SourceAuxiliaryThetaSeed
```

and proves:

```lean
sourceAuxiliaryPair_eq_sourceCompletedZeta_on_seed_of_theta_seed
```

This theorem consumes an explicit inhabitant of `SourceAuxiliaryThetaSeed`.
No such inhabitant is constructed by Q383.

## Exact open leaf

The missing primary step is the Kuzmin/Mittag-Leffler transport from the
auxiliary Mordell contour to the source identity `E:Rthetados`. The remaining
states are therefore:

```text
Q383_MORDELL_MELLIN_DOUBLE_KERNEL              : NOT_OBTAINED
SourceCompletedAuxiliaryRThetaSeed              : NOT_OBTAINED
SourceAuxiliaryThetaSeed                        : NOT_OBTAINED
Q383_AUXILIARY_PAIR_EQ_COMPLETED_ZETA_ON_SEED   : NOT_OBTAINED
Q381_PRIMARY_AUXILIARY_TO_ZETA                  : OPEN
CARRIER_MEMBERSHIP                              : UNPROVED
BRIDGE_A                                        : OPEN
```

The Q381 Hardy connector, the explicit Arias bound, the semantic production
endpoint, and Bridge A closure were not attempted because this gate remained
open.

## Verification

```text
Lean direct Q383 modules : 15/15 PASS
Q383 root build          : PASS
Q374-Q383 aggregate      : 3271/3271 PASS
Axiom audit              : propext, Classical.choice, Quot.sound
Forbidden source scan    : EMPTY
git diff --check         : PASS
HEAD = origin/main       : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
Permanent Git operation  : NONE
```

