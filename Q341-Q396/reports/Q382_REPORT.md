# Q382 - Independent auxiliary-zeta analytic seed

## Verdict

```text
RS10H_ANALYTIC_PARTIAL_FAIL_CLOSED
Q382_MORDELL_RIEMANN_COMPUTED_PASS
Q382_INDEPENDENT_AUXILIARY_ZETA_SEED_NOT_OBTAINED
Q381_PRIMARY_AUXILIARY_TO_ZETA_NOT_OBTAINED
CARRIER_MEMBERSHIP_UNPROVED
BRIDGE_A_OPEN
```

## Proven in Lean

The primary Mordell route is formalized independently of zeta:

```lean
theorem sourceMordellIntegral_eq_closedForm
    (z : Complex) (hz : Complex.exp (-z) != 1) :
    sourceMordellIntegral z = sourceMordellClosedForm z
```

This includes the exact affine contour, denominator nonvanishing, parameter
analyticity, one-pole contour shift, transverse decay, the functional
translation, square completion, and the exact oblique complex Gaussian
integral.  The resulting closed form is the source equation
`E:riemcomputed`.

## Route selection

Both Mordell and theta-Mellin API probes compiled.  Mordell was selected because
Q380 already supplied the contour, pole, and side-decay infrastructure, while
Mathlib supplied the required complex Gaussian integral.  The theta-Mellin
route remains viable but was not developed beyond the API and normalization
audit.

## Exact open leaf

The missing result is the independent Mellin/contour transport from the proved
Mordell closed form to an equality between `sourceAuxiliaryPair` and
`sourceCompletedZeta` on a nonempty open set (or on the full critical line).
No conditional Q381 connector was used as proof of this premise.

The next proof must justify the Mellin transform, all exchanges of integrals,
the source polar term, and the exact Gamma/pi normalization.  Until then:

```text
Q382_INDEPENDENT_AUXILIARY_ZETA_SEED : OPEN
Q381_PRIMARY_AUXILIARY_TO_ZETA       : OPEN
Q381_NORMALIZED_HARDY_Z_DECOMPOSITION: CONDITIONAL_ONLY
Q375_EXPLICIT_ARIAS_BOUND            : OPEN
BRIDGE_A                             : OPEN
```

## Governance

T0 was `2026-08-26T18:18:15+02:00`.  The recommended freeze at
`22:03:15+02:00` was exceeded while finishing the nearly compiled algebraic
tail of the Mordell theorem.  The theorem and closeout were completed before
the absolute deadline `22:18:15+02:00`.  This is classified
`FREEZE_OVERRUN_PRE_DEADLINE`, not post-deadline work.

No permanent Git operation was performed.  `HEAD` and `origin/main` remain at
`433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`.

