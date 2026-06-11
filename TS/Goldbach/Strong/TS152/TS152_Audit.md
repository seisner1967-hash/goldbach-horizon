# TS152 Audit - Finite Head Prime Interval Budget Reduction

## Status

`repo_committed_relative`

TS152 closes the finite set manipulations behind the TS151 head branch.  It
does not assert that the crude interval cardinality fits the TS22
Brun-Titchmarsh budget.

## Unconditional results

```lean
TS152.Goldbach.primeIntervalCard_le_intervalLength_add_one
TS152.Goldbach.primeIntervalCard_le_cumulativeHead
TS152.Goldbach.cumulativeHeadPrimeIntervalCard_le_cardinality
```

They prove:

```text
primeIntervalCard n h <= h + 1

n <= level
  -> primeIntervalCard n h
       <= primeIntervalCard 0 (level + h)
```

## Finite-head discharge interfaces

The coarse route is:

```lean
TS152.Goldbach.TrivialFiniteHeadBudgetCondition
TS152.Goldbach.finiteHeadPrimeIntervalBudget_of_trivialCardinality
```

The sharper route reduces all head windows to one cumulative count:

```lean
TS152.Goldbach.CumulativeFiniteHeadPrimeBudget
TS152.Goldbach.finiteHeadPrimeIntervalBudget_of_cumulative
TS152.Goldbach.FiniteHeadPrimeIntervalBudgetReductionLedger
TS152.Goldbach.finiteHeadPrimeIntervalBudgetReductionTarget
```

## Remaining obligation

The remaining head input is now a one-variable cumulative prime-count bound:

```text
primeIntervalCard 0 (level x Q + intervalScale x Q)
  <= brunTitchmarshCeilBudget x Q
```

The crude sufficient comparison

```text
intervalScale x Q + 1 <= brunTitchmarshCeilBudget x Q
```

is intentionally not proved.  Since the TS22 budget is
`ceil (4 * intervalScale / log (Q+1))`, the total interval cardinality is not
a uniformly safe replacement for prime counting when `Q` grows.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS152.FiniteHeadPrimeIntervalBudgetReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS152
git diff --check -- README.md TS\Goldbach\Strong\TS152
```

Expected result: build succeeds and both audit commands report no issue.
