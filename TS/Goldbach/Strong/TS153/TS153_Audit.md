# TS153 Audit - Dependent Selberg Budget Feasibility Probe

## Status

`repo_committed_relative`

TS153 extracts exact necessary conditions from the dependent TS150 budget
comparison.  It does not assert a growth estimate for the TS122 denominator.

## Exact decomposition

The refined TS150 budget is split into:

```text
main  = (intervalScale x Q + 1) / D(level)
error = (level / D(level))^2
```

Main declarations:

```lean
TS153.Goldbach.refinedSelbergMainTermRat
TS153.Goldbach.refinedSelbergErrorTermRat
TS153.Goldbach.refinedSelbergBudgetRat_eq_main_add_error
```

## Necessary comparison conditions

A supplied TS150 comparison implies separately:

```text
main  <= brunTitchmarshCeilBudget
error <= brunTitchmarshCeilBudget
```

and forces the exact ceiling-aware denominator threshold:

```text
(intervalScale x Q + 1) / brunTitchmarshCeilBudget x Q
  <= D(level)
```

Main declarations:

```lean
TS153.Goldbach.refinedSelbergBudgetRat_le_brunTitchmarshCeil_cast
TS153.Goldbach.refinedSelbergMainTermRat_le_brunTitchmarshCeil_cast
TS153.Goldbach.refinedSelbergErrorTermRat_le_brunTitchmarshCeil_cast
TS153.Goldbach.brunTitchmarshCeilBudget_pos_of_refinedComparison
TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat
TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat_le_denominator
```

## Dependent package

```lean
TS153.Goldbach.DependentSelbergBudgetNecessaryConditions
TS153.Goldbach.dependentSelbergBudgetNecessaryConditions
TS153.Goldbach.DependentSelbergBudgetFeasibilityLedger
TS153.Goldbach.dependentSelbergBudgetFeasibilityTarget
```

## Remaining work

TS154 should compare the exact necessary threshold with proved upper and lower
bounds for `D(level)`.  Only after that diagnostic should the project select a
concrete dependent level or refactor the budget.

The cumulative finite-head prime-count obligation from TS152 remains separate.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS153.DependentSelbergBudgetFeasibilityProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS153
git diff --check -- README.md TS\Goldbach\Strong\TS153
```

Expected result: build succeeds and both audit commands report no issue.
