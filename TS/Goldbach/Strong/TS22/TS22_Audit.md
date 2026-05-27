# TS22 - Energy Scale Renormalization

## Status

TS22 introduces an explicit normalization scale for the short-interval energy.
It avoids changing the historical TS15/TS16 definitions in place and instead
adds a scale-parametrized interface.

Status: `repo_committed_relative`.

## Mathematical Correction

The raw energy

```text
sum_n localCount(n)^2
```

has the natural scale `(x+1) * B^2` under a uniform local-window bound
`localCount(n) <= B`. Dividing the raw energy by `h` would not preserve the
TS16 pair-count comparison for all close pairs, because a pair at distance
exactly `h` can be present in only one window.

Therefore TS22 keeps the raw energy and renormalizes the comparison target by
making the scale explicit.

## Lean Files

- `EnergyScale.lean`:
  - defines `ShortIntervalScale`;
  - defines `Problem_E1Scale S K`;
  - defines `ShortIntervalPrimeSecondMomentScale S`;
  - proves the TS16 transport from scaled second moment to scaled pair count;
  - proves monotonicity in the constant and in the scale.
- `BrunTitchmarshScaleDischarge.lean`:
  - turns `TS21.BrunTitchmarshLocalWindowBudget` into a scale;
  - proves a scaled second-moment estimate with constant `1`;
  - proves the corresponding scaled pair-count estimate;
  - defines `BrunTitchmarshScaleBridge` for future closed-form domination.
- `ClosedFormScales.lean`:
  - defines a closed-form Brun-Titchmarsh scale
    `(x+1) * (4 * intervalScale x Q / log Q)^2`;
  - packages it as a `ShortIntervalScale`.
- `BrunTitchmarshIntervalBridge.lean`:
  - defines the elementary interval count `primeIntervalCard`;
  - defines the ceiling budget `brunTitchmarshCeilBudget`;
  - proves that TS15 local windows are subcounts of the corresponding prime
    interval;
  - shows that an interval-count Brun-Titchmarsh theorem instantiates
    `BrunTitchmarshLocalWindowBudget`.
- `ScaledLargeSieveDischarge.lean`:
  - defines `ScaledLargeSieveInfrastructure`;
  - combines `DirichletCharacterBridge` with a scale-aware large-sieve bound;
  - proves `Problem_E1Scale_from_scaledLargeSieve`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS22.EnergyScale `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge `
  TS.Goldbach.Strong.TS22.ClosedFormScales `
  TS.Goldbach.Strong.TS22.BrunTitchmarshIntervalBridge `
  TS.Goldbach.Strong.TS22.ScaledLargeSieveDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS22
rg -n "a[x]iom" TS\Goldbach\Strong\TS22
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS22-S1 | `ShortIntervalScale` | `repo_committed` | scale abstraction |
| TS22-E1 | `Problem_E1Scale_from_second_moment_scale` | `repo_committed` | TS16 transport for any scale |
| TS22-BT1 | `Problem_E1Scale_from_localWindowBudget` | `repo_committed_relative` | relative to local BT window budget |
| TS22-BT2 | `BrunTitchmarshScaleBridge` | `analytic_infrastructure_obligation` | dominates exact integer budget by closed-form scale |
| TS22-CF1 | `brunTitchmarshClosedFormScale` | `repo_committed` | proposed natural BT scale |
| TS22-I1 | `BrunTitchmarshNatIntervalBound` | `analytic_infrastructure_obligation` | interval-count BT theorem |
| TS22-I2 | `Problem_E1Scale_from_natIntervalBound` | `repo_committed_relative` | bridges interval BT to scaled pair count |
| TS22-LS1 | `ScaledLargeSieveInfrastructure` | `analytic_infrastructure_obligation` | scale-aware large sieve |
| TS22-LS2 | `Problem_E1Scale_from_scaledLargeSieve` | `repo_committed_relative` | TS18 bridge plus scaled sieve implies scaled E1 |

## Conclusion

TS22 resolves the scale mismatch without weakening the Lean audit discipline.
The correct path is now:

```text
BrunTitchmarshLocalWindowBudget
  => Problem_E1Scale (localWindowBudgetScale BT) 1
  +  BrunTitchmarshScaleBridge
  => Problem_E1Scale brunTitchmarshClosedFormScale 1
```

The remaining analytic work is to instantiate the local window budget and prove
that a chosen closed-form scale dominates the exact integer budget scale.

## Mathlib Note

In the Lean 4.15.0 / Mathlib v4.15.0 baseline used here,
`Mathlib.NumberTheory.Sieve.Selberg` is not present. The Selberg sieve and the
Brun-Titchmarsh theorem must therefore be contributed separately or supplied as
a local interval-count theorem satisfying `BrunTitchmarshNatIntervalBound`.
