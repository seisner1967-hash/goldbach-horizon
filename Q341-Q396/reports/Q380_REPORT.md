# Q380 / RS8H report

## Verdict

```text
Q380_SOURCE_AUXILIARY_CAUCHY_REPRESENTATION : PASS
Q374_SOURCE_RSFORMULA                       : PASS
Q380_ORIGINAL_TIMEBOX                       : OVERRUN
Q380_POST_DEADLINE_USER_AUTHORIZED          : PASS

Q380_AUXILIARY_TO_ZETA                      : NOT_OBTAINED
Q380_NORMALIZED_HARDY_Z_DECOMPOSITION       : NOT_OBTAINED
Q375_EXPLICIT_ARIAS_BOUND                   : NOT_OBTAINED
BRIDGE_A                                    : OPEN
```

The technical Q380 and source-level Riemann--Siegel results were completed on
2026-08-26 during a continuation explicitly authorized by the user.  They do
not rewrite the original four-hour timebox verdict.

## Proven in Lean

The primary auxiliary function is independently defined by the original
meromorphic contour integral.  Lean proves its integrability, the complete
integer pole set, simple poles, the exact local coefficient, branch
compatibility, and the affine saddle substitution.

The post-deadline continuation additionally proves:

```lean
sourceDisplacedAuxiliaryIntegral_one_pole_shift :
  sourceDisplacedAuxiliaryIntegral s (n - 1) -
    sourceDisplacedAuxiliaryIntegral s n =
    sourcePrincipalPower (n : Complex) s

sourceAuxiliaryR_eq_prefix_add_displaced :
  sourceAuxiliaryR s =
    sourceDirichletPrefix ell s +
      sourceDisplacedAuxiliaryIntegral s ell

sourceAuxiliaryR_eq_prefix_add_transformed :
  sourceAuxiliaryR s =
    sourceDirichletPrefix ell s +
      sourceAuxiliaryTransformPrefactor s ell xi *
        Q379Probe.sourceInitialDirectGIntegral xi q

sourceAuxiliaryR_eq_RSformula :
  sourceAuxiliaryR s =
    sourceDirichletPrefix ell s +
      sourceAuxiliaryTransformPrefactor s ell xi *
        (Q379Probe.sourcePrimaryFiniteCorrection K xi q +
          Q366Probe.sourceRSRemainder K ...)
```

The one-pole theorem is obtained without a general residue oracle.  The pole
is removed by `Complex.dslope`; the complete integrand has Gaussian transverse
decay, its principal part has uniform `1/R` decay, the exact principal jump is
`2 * pi * I`, and the cell identities telescope over the finite pole set.

## Build and trust audit

```text
Q380 root build                 : PASS (2390 jobs)
Q380 executable source modules : 19
Forbidden-token scan           : EMPTY
git diff --check               : PASS
Terminal axioms                : propext, Classical.choice, Quot.sound
HEAD                            : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
origin/main                     : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
Permanent Git operation        : NONE
Residual Lean/Lake/Python      : NONE
```

## Exact fail-closed frontier

The retained primary source states

```text
Gamma_R(s) * zeta(s)
  = Gamma_R(s) * sourceAuxiliaryR(s)
    + Gamma_R(1-s) * conjugate(sourceAuxiliaryR(1-conjugate(s))).
```

This is equation `E:RiemSiegel` / `E:zetaRzeta` in
`Q366RResearch/2406.02403/166-RzetaBasic.tex`.  It is not available in the
pinned Mathlib revision, and the retained TeX states it without supplying the
needed formal derivation.  Q380 does not introduce it as an axiom or an
uninhabited semantic witness.

Consequently the source formula is closed, while transport to
`Q343Probe.normalizedHardyZ`, the explicit 2011 Arias bound, a semantic
production endpoint, and Bridge A all remain open.
