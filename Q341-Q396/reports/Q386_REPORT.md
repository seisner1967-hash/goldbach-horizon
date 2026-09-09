# Q386 - Regularized Exceptional Values

Date: 2026-09-02
Mode: fail-closed, additive, no permanent Git operation

## Verdict

```text
Q386_NEGATIVE_EVEN_POINT_AUDIT_PASS
Q386_COMPLETED_VALUE_REGULARITY_PASS
Q386_COMPLETED_EXACT_LINE_INTEGRAL_REPRESENTATION_PASS
Q386_ENTIRE_AUXILIARY_TRIVIAL_ZERO_PASS
Q386_COMPLETED_ZERO_LAURENT_CLOSED_FORM_NOT_OBTAINED
Q386_COMPLETED_NONZERO_VALUE_NOT_OBTAINED
Q386_OLD_COMPLETED_ZERO_CONNECTOR_NOT_INSTANTIATED
```

## Result

The source definitions distinguish two functions:

```text
sourceRThetaCompletedAuxiliary
sourceRThetaAuxiliaryEntire
```

For `negativeEvenPoint n = -2 * (n + 1)`, Q386 proves:

```lean
Q383Probe.sourceRThetaCompletedAuxiliary (negativeEvenPoint n)
  = Q386Probe.completedNegativeEvenValue n
```

where the right-hand side is the exact integral representation

```lean
Q384Probe.sourceRThetaFullLineIntegral (negativeEvenPoint n) / 2
```

The completed expression is differentiable at every such point. Therefore
these points are not poles of the completed expression and no Gamma Laurent
division is needed to define its value there.

Independently, Q386 replays the Q385 result:

```lean
Q384Probe.sourceRThetaAuxiliaryEntire (negativeEvenPoint n) = 0
```

This zero comes from the reciprocal Gamma factor. It is not transported to
the completed expression.

Q386 also proves that the completed-zero statement is equivalent to the
vanishing of the exact full-line integral representation. No proof of that
vanishing, no proof of non-vanishing, and no elementary closed form for the
integral was obtained.

## Boundary

```text
Q386_REGULARIZED_EXCEPTIONAL_VALUE : CLOSED
Q386_COMPLETED_ZERO                : OPEN
Q386_COMPLETED_NONZERO_VALUE       : OPEN
Q381_PRIMARY_AUXILIARY_TO_ZETA     : OPEN
Q375_EXPLICIT_ARIAS_BOUND           : OPEN
BRIDGE_A                            : OPEN
```

The former Q384 connector requiring completed theta zeros remains unused. No
zeta trivial-zero theorem was used to fill it.

## Verification

```text
Lean target build      : PASS
Lean axiom audit       : PASS
Forbidden scan         : EMPTY on production sources
Manifest replay        : PASS 9/9
ZIP integrity          : PASS, 11 entries
Git permanent action   : NONE
```

Q386 is therefore a structural correction and regularity pass, not a closure
of the original completed-zero or auxiliary-to-zeta obligation.
