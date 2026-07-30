# TS323 Audit - Certified Rational Trace-Budget Packaging

## Scope

TS323 closes the complete conditional route from the TS322 real finite-core
estimate to the TS313 normalized rational budget and the TS312/TS181 adapter.
It introduces one certificate structure whose fields record every rational
upper bound and arithmetic allocation needed by the existing APIs.

The module does not construct a concrete inhabitant of that certificate.
Consequently it does not claim an unconditional half-budget, OTSA, or
Goldbach.

## Main declarations

```lean
TS323.Goldbach.CertifiedRationalTraceBudgetData

TS323.Goldbach.CertifiedRationalTraceBudgetData.pairMajorant_nonnegative
TS323.Goldbach.CertifiedRationalTraceBudgetData.weightedClosePairEnvelopeBound
TS323.Goldbach.CertifiedRationalTraceBudgetData.diagonalZeroCorrelationBound
TS323.Goldbach.CertifiedRationalTraceBudgetData.weightedOffDiagonalCorrelationBound
TS323.Goldbach.CertifiedRationalTraceBudgetData.finiteQuadraticSpectralMomentBound
TS323.Goldbach.CertifiedRationalTraceBudgetData.exists_good_scale_spectral_bound
TS323.Goldbach.CertifiedRationalTraceBudgetData.exists_normalizedTraceBudget
TS323.Goldbach.CertifiedRationalTraceBudgetData.normalizedTraceBudgetData
TS323.Goldbach.CertifiedRationalTraceBudgetData.toTS181TraceBudgetAdapterData

TS323.Goldbach.TS323Ledger
TS323.Goldbach.ts323Ledger
```

## Certificate boundary

The structure stores heights `H <= T`, a positive dyadic scale `X`, and the
non-aliasing condition `4*T <= X`.  Its rational components certify upper
bounds for:

```text
finiteWeightedLocalCore H
effectiveWeightedTailError H
4 * globalQuadraticSpectralMass
normalizedSpectralTailEnvelope T
the normalized exceptional residue on every x in dyadicWindow X
the normalized fixed-left residue on every x in dyadicWindow X.
```

The residual bounds must be uniform because TS314 chooses the final scale
existentially after the moment estimate is established.

## Pair and moment routing

TS322 gives

```text
weightedClosePairEnvelope T
  <= finiteWeightedLocalCore H + effectiveWeightedTailError H.
```

The two rational bounds weaken this to `coreMajorant + tailMajorant`.  TS320
then supplies the absolute pointwise kernel constant `96`, and the TS317
reduction gives the exact TS315 off-diagonal contract with majorant

```text
96 * (coreMajorant + tailMajorant).
```

Independently, TS316 supplies the exact diagonal majorant
`4 * globalQuadraticSpectralMass`, which is weakened to the certified
`diagonalMajorant`.  The certificate requires precisely

```text
diagonalMajorant + 96 * (coreMajorant + tailMajorant) <= qMoment^2.
```

TS315 therefore proves the finite quadratic moment statement expected by
TS314.  The factors `4` and `96` each occur exactly once.

## Good scale and rational budget

TS314 selects `x` in `dyadicWindow X` and constructs the rational spectral
majorant

```text
qMoment + truncationTailMajorant.
```

The uniform residual certificates are specialized to this selected `x`.
TS323 then fills every field of `TS313.NormalizedTraceBudgetData`, including
the exact component inequality

```text
qMoment + truncationTailMajorant
  + exceptionalMajorant + leftMajorant <= traceBudget <= 1/2.
```

The existing TS313 constructor converts the chosen normalized package to
`TS312.TS181TraceBudgetAdapterData` without further analytic input.

## Fail-closed boundary

TS323 proves an implication from a fully certified rational input.  It does
not prove that such an input exists or that the current analytic constants
permit a half-budget.  In particular:

```text
no finite zero core is evaluated numerically
no real finite sum is converted by an uncertified rounding operation
no global zero-spacing or RH assumption is introduced
no negative non-existence theorem is asserted
```

The only remaining quantitative object is a concrete inhabitant of
`CertifiedRationalTraceBudgetData`.

## Verification

```text
Targeted build: 3044/3044
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
