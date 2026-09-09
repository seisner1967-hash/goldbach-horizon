# Q389 / RS17H report

## Verdict

```text
Q389_CRITICAL_LINE_AUXILIARY_TO_ZETA_PASS
Q389_NORMALIZED_HARDY_Z_TRANSPORT_PASS
Q389_CANONICAL_HARDY_RS_DECOMPOSITION_PASS
Q389_GENERIC_RS_CHECKER_SOUND_PASS
Q389_GENERIC_ANALYTIC_LEAF_CONNECTOR_PASS

BRIDGE_A_OPEN_AT_EXPLICIT_REMAINDER_OR_CARRIER_GATE
```

Q389 is a strong analytic success. It removes the exceptional theta seed from
the Bridge A critical path and proves the auxiliary-zeta identity on the full
critical line. It does not claim a concrete production endpoint or close
Bridge A.

## Main theorem

Lean 4.15.0 proves, for every real `t`:

```lean
theorem sourceAuxiliaryPair_eq_sourceCompletedZeta_critical (t : Real) :
    Q381Probe.sourceAuxiliaryPair (Q343Probe.criticalPoint t) =
      Q381Probe.sourceCompletedZeta (Q343Probe.criticalPoint t)
```

and consequently:

```lean
theorem normalizedHardyZ_eq_sourceNormalizedAuxiliaryCarrier (t : Real) :
    Q343Probe.normalizedHardyZ t =
      Q381Probe.sourceNormalizedAuxiliaryCarrier t
```

## Analytic route

Q389 defines the required open, convex and preconnected upper and lower
transport domains. It proves explicit analytic interfaces for the auxiliary
pair and completed zeta there.

The continuation itself uses the proper theta pair. Q384 already supplies the
upper-half-plane identity from the regular Mordell-Mellin strip; Q389 proves
the reflected lower-half-plane theorem from the seed point `3/2 - i`. Off the
real axis, nonvanishing of `GammaR` identifies these proper representatives
with the historical auxiliary and completed-zeta expressions.

At `t = 0`, Q389 approaches `criticalPoint 0` through the sequence
`criticalPoint (1/(n+1))` and uses continuity plus uniqueness of limits. A
trichotomy on `t` then covers the full critical line.

No exceptional negative-even value, old global seed, or Q388 numerical
diagnostic is used.

## Riemann-Siegel and checker cascade

The critical transport is substituted directly into the existing source
Riemann-Siegel theorem. Q389 proves the exact decomposition

```text
normalizedHardyZ = source finite part + independent source remainder.
```

The Q368 rational checker is then connected to this decomposition using the
strongest current integral-free, scale-preserving source remainder bound.
Finally, Q389 exports a generic constructor for the Q347 `AnalyticLeaf`
boundary.

This constructor is not a concrete leaf. Its premises still require:

1. checked enclosures for every finite-part atom;
2. equality between the replayed arithmetic expression and the exact finite
   Riemann-Siegel term;
3. a proved rational radius dominating the closed analytic remainder bound.

## First open production gate

The exact analytic inequality still needing concrete certification is:

```lean
2 * norm (sourceAuxiliaryTransformPrefactor (criticalPoint t) ell xi) *
  sourceSharpClosedIntegralBound K regime (abs xi)
    theta phi gap.a cosBound.M
<= cert.remainderRadius
```

The current general witnesses `gap.a` and `cosBound.M` are partly obtained by
compactness and are not yet a complete rational production certificate.
`Q375_EXPLICIT_ARIAS_BOUND` therefore remains open. No production endpoint or
first production bracket is instantiated.

## Checks

```text
Direct Lean modules            : PASS 8/8
lake build Q389Probe           : PASS 3389/3389
aggregate Q374Probe-Q389Probe  : PASS 3423/3423
Axioms                         : propext, Classical.choice, Quot.sound
Forbidden scan                 : EMPTY
git diff --check               : PASS
Residual Lean/Lake processes   : 0
HEAD = origin/main             : 433e29e
Permanent Git operations       : NONE
```

The worktree contains the accumulated untracked probe history and is not
reported as clean.

## Frontier

```text
Q381_PRIMARY_AUXILIARY_TO_ZETA_GLOBAL : OPEN / NOT_REQUIRED_BY_Q389
Q375_EXPLICIT_ARIAS_BOUND              : OPEN
Q389_CARRIER_MEMBERSHIP                : UNPROVED
Q389_CANONICAL_ENDPOINT                : NOT_OBTAINED
Q389_FIRST_PRODUCTION_BRACKET          : NOT_OBTAINED
BRIDGE_A                               : OPEN
TS340_UNCONDITIONAL                    : OPEN_FROZEN
Q390                                   : NOT_AUTHORIZED
```

Development froze at `2026-09-04T14:53:29+02:00`, well before the absolute
deadline.

