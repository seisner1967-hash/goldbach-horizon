# TS151 Audit - Dependent Selberg Scale Split Interface

## Status

`repo_committed_relative`

TS151 proves an unconditional obstruction in the fixed-level TS140/TS150
route and replaces it with a dependent-level head/tail interface.

## Unconditional obstruction

`LargePrimeAdmissibleIntervalSieveTheorem level` requires `level < n` for
every `n < x + 1`.  Taking `x = 16` and `n = 0` gives `level < 0`.
Therefore the package is uninhabited for every natural level.

Main declarations:

```lean
TS151.Goldbach.largePrimeAdmissibleIntervalSieveTheorem_uninhabited
TS151.Goldbach.refinedSelbergBudgetScaleLedger_uninhabited
```

## Corrected interface

TS151 introduces a level selection depending on `(x,Q)` and separates the
remaining TS22 theorem into:

1. a finite-head bound for `n <= level x Q`;
2. the TS140 large-prime argument for `level x Q < n`.

Main declarations:

```lean
TS151.Goldbach.SelbergLevelSelection
TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison
TS151.Goldbach.FiniteHeadPrimeIntervalBudget
TS151.Goldbach.primeIntervalCard_le_brunTitchmarshCeilBudget_of_dependentLevel
TS151.Goldbach.brunTitchmarshNatIntervalBound_of_dependentScaleSplit
TS151.Goldbach.brunTitchmarshFinalInputLedger_of_dependentScaleSplit
TS151.Goldbach.DependentSelbergScaleSplitLedger
TS151.Goldbach.dependentSelbergScaleSplitBridgeTarget
```

## Remaining obligations

TS151 does not select a concrete level and does not prove a growth statement
for the TS122 denominator.  The remaining inputs are explicit:

```text
dependent refined-budget comparison
finite-head interval bound
```

Once supplied, TS151 constructs the exact
`TS22.Goldbach.BrunTitchmarshNatIntervalBound` and the
`TS97.Goldbach.BrunTitchmarshFinalInputLedger`.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS151.DependentSelbergScaleSplitInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS151
git diff --check -- README.md TS\Goldbach\Strong\TS151
```

Expected result: build succeeds and both audit commands report no issue.
