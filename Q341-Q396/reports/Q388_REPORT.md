# Q388 / RS16H report

## Verdict

```text
Q388_ANALYTIC_PARTIAL_FAIL_CLOSED
```

The sprint closes the exact reduction of the exceptional completed value, but
does not close the full-line integral evaluation.

## Results obtained

```text
Q388_EXCEPTIONAL_POINT_NEGATIVE_REAL_PART_PASS
Q388_FULL_LINE_INTEGRABILITY_PASS
Q388_FULL_LINE_SPLIT_PASS
Q388_CONSTANT_MODE_EXACT_PASS
Q388_Q386_HALF_VALUE_CONNECTOR_PASS
Q388_ZERO_IFF_RESIDUAL_CANCELLATION_PASS
Q388_Q386_VALUE_IDENTITY_PASS
Q388_AXIOM_AUDIT_PASS
Q388_FORBIDDEN_SCAN_PASS
```

The main exact theorem is the decomposition

```text
full integral = residual source line integral
              - (2 / exceptional point) * I^(exceptional point / 2)
```

with the Q386 completed value equal to one half of that expression. Lean also
proves the corresponding iff: the completed value is zero precisely when the
residual line integral equals the explicit constant mode with the opposite
sign.

## What remains open

```text
Q388_FULL_LINE_INTEGRAL_CLOSED_FORM : NOT_OBTAINED
Q388_EXCEPTIONAL_VALUE_NONZERO      : NOT_OBTAINED
Q388_RESIDUAL_LINE_EVALUATION       : NOT_OBTAINED
SourceAuxiliaryThetaSeed            : OPEN
Q381_PRIMARY_AUXILIARY_TO_ZETA      : OPEN
BRIDGE_A                            : OPEN
```

This is a structural analytic result, not a numerical certificate. In
particular, no value from Arb or FLINT has been imported as evidence, and no
trivial-zero theorem for zeta has been used to force the residual integral to
vanish.

## Verification

```text
Lean target Q388Probe : PASS, 3344/3344 tasks
Axioms                : propext, Classical.choice, Quot.sound
Forbidden scan        : EMPTY
HEAD                  : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
origin/main           : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
Permanent Git action  : NONE
```

The complete source specification is in `Q388_FULL_LINE_INTEGRAL_SPEC.md`.
