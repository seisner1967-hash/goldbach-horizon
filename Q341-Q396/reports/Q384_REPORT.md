# Q384 / RS12H progress report

Date: 2026-09-02
Baseline: `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`

## Verdict

```text
Q384_CANONICAL_CRITICAL_POINT_DATA_PASS
Q384_CANONICAL_REGIME_ROUTER_PASS
Q384_REGULAR_STRIP_TRANSPORT_PASS
Q384_REFLECTED_GAMMA_EXCEPTION_CHARACTERIZATION_PASS
Q384_REGULAR_DOMAIN_TRANSPORT_PASS
Q384_EXCEPTIONAL_POINT_CONNECTOR_PASS

Q384_SOURCE_AUXILIARY_THETA_SEED_GLOBAL : NOT_OBTAINED
Q384_PRODUCTION_WITNESS                : NOT_OBTAINED
BRIDGE_A                               : OPEN
```

## Proven results

`Q384Probe.SeedTransportClosure` now records an unconditional seed identity on
the Kuzmin regular strip and a second identity on the full Mellin seed domain
provided the reflected real Gamma factor is nonzero.

The new characterization is:

```lean
Gammaℝ (1 - star s) = 0 ↔
  ∃ n : Nat, s = (1 : Complex) + 2 * n
```

Consequently, the auxiliary-to-theta identity is available on the seed domain
with the discrete positive-odd set removed.  This is a genuine theorem about
the totalized Mathlib Gamma function; it is not a numerical or analytic
assumption.

The remaining exceptional points are isolated behind the conditional
proposition:

```lean
SourceRThetaNegativeEvenTrivialZeros :=
  ∀ n, sourceRThetaCompletedAuxiliary (-(2 : Complex) * n) = 0
```

Lean proves that this proposition implies the original global
`SourceAuxiliaryThetaSeed`.  The proposition itself is deliberately not
postulated or marked as proved.

## Boundary

The remaining obligation is to prove the negative-even trivial zeros of the
regularized theta auxiliary function, then invoke the conditional connector.
The global proposition `Q383Probe.SourceAuxiliaryThetaSeed` remains
uninhabited in this work.

The downstream identities to `sourceCompletedZeta`, `normalizedHardyZ`, the
explicit Arias bound, and `BRIDGE_A` remain open.

## Integrity

- No Git operation was performed.
- No permanent commit, branch, tag, push, merge, or pull request was created.
- The source scan for forbidden proof shortcuts is empty for the new closure.
- The proof audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Package

The package and its external hash attestations are produced after the final
source snapshot.  The hash files are kept outside the ZIP to avoid a circular
dependency between archived metadata and the archive digest.
