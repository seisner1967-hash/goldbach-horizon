# Q381 - Primary auxiliary to Riemann zeta

## Verdict

```text
RS9H_ANALYTIC_PARTIAL_FAIL_CLOSED
Q381_ORIGINAL_TIMEBOX                         : OVERRUN
Q381_POST_DEADLINE_USER_AUTHORIZED            : PASS

Q381_COMPLETED_OBJECTS_DEFINITION_PASS
Q381_GAMMA_R_CONJUGATION_PASS
Q381_REFLECTED_CONTOUR_CONJUGATION_PASS
Q381_REFLECTED_CONTOUR_ORIENTATION_PASS
Q381_SOURCE_AUXILIARY_ENTIRE_PASS
Q381_CRITICAL_LINE_SELF_REFLECTION_PASS
Q381_AUXILIARY_PAIR_EQ_TWO_REAL_PART_PASS

Q381_PRIMARY_AUXILIARY_TO_ZETA                : NOT_OBTAINED
Q381_NORMALIZED_HARDY_Z_SOURCE_DECOMPOSITION  : CONDITIONAL_ONLY
CARRIER_MEMBERSHIP                            : UNPROVED
BRIDGE_A                                      : OPEN
```

## Proven in Lean

The completed objects use Mathlib's exact `Complex.GammaR` convention. Lean
proves conjugation of this factor and the exact binding with
`completedRiemannZeta` away from its excluded points.

The reflected contour is independently defined. The principal-log branch,
the denominator sign, the tangent orientation, and the substitution
`u -> -u` are all discharged in Lean:

```lean
theorem sourceReflectedAuxiliaryIntegral_eq_conj (s : Complex) :
    sourceReflectedAuxiliaryIntegral s =
      star (Q380Probe.sourceAuxiliaryR (1 - star s))
```

The primary auxiliary function is proved entire by differentiation under its
defining integral, using an explicit local Gaussian majorant:

```lean
sourceAuxiliaryR_differentiable :
  Differentiable Complex Q380Probe.sourceAuxiliaryR

sourceAuxiliaryR_analyticAt (s : Complex) :
  AnalyticAt Complex Q380Probe.sourceAuxiliaryR s
```

On the critical line, Lean proves exact self-reflection and reduction of the
completed auxiliary pair to twice a real part.

## Conditional connector

The theorem

```lean
normalizedHardyZ_eq_sourceNormalizedAuxiliaryCarrier_of_completed_identity
```

is compiled but explicitly assumes the missing completed
auxiliary-to-zeta identity. It is not a semantic proof of that identity and
does not justify `CARRIER_MEMBERSHIP_PASS`.

## First open analytic leaf

The retained primary source states `E:RiemSiegel`, but refers its independent
derivation to Riemann/Siegel. The first missing seed is the Mordell integral
`E:riemcomputed`, or an equivalent proof that both sides equal a common
theta-Mellin representation.

Pinned Mathlib contains neither the Mordell integral nor a relation involving
Riemann's auxiliary function. Functional equations and identity theorems can
propagate an equality only after this independent seed is proved; they cannot
create it.

```text
Q381_MORDELL_RIEMANN_COMPUTED       : NOT_OBTAINED
Q381_AUXILIARY_PAIR_THETA_MELLIN    : NOT_OBTAINED
Q381_PRIMARY_AUXILIARY_TO_ZETA      : NOT_OBTAINED
```

## Verification

```text
Direct Lean targets  : 6/6 PASS
Lake Q381 aggregate  : 3221/3221 PASS
Axioms               : propext, Classical.choice, Quot.sound
Forbidden scan       : EMPTY
git diff --check     : PASS
HEAD = origin/main   : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
Permanent Git action : NONE
```

The original deadline was `2026-08-26T16:16:04+02:00`. Results completed
after it are classified `POST_DEADLINE_USER_AUTHORIZED` following the user's
explicit continuation request.
