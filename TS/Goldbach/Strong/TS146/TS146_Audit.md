# TS146 Audit

## Scope

TS146 aggregates the pointwise LCM multiplicity error bound from TS143 over
the finite TS122 Selberg support. It also combines that global error estimate
with the unconditional main-term budget proved in TS145.

## Finite L1 budget

```text
TS146.Goldbach.selbergConcreteLambdaL1Rat
TS146.Goldbach.selbergWeightedLCMErrorPairBudgetRat
TS146.Goldbach.selbergWeightedLCMErrorPairBudget_eq_l1_sq
```

The pairwise absolute budget factors exactly as

```text
sum_d1 sum_d2 |lambda(d1)| |lambda(d2)|
  = (sum_d |lambda(d)|)^2.
```

## Weighted local and global errors

```text
TS146.Goldbach.WeightedLCMLocalErrorBound
TS146.Goldbach.weightedLCMLocalError_abs_le
TS146.Goldbach.selbergFractionalErrorTerm_abs_le_pairBudget
TS146.Goldbach.selbergFractionalErrorTerm_abs_le_l1_sq
```

For supported `d1,d2`, TS143 gives absolute local error at most one. Triangle
inequalities and monotonicity of finite sums then prove

```text
|fractionalErrorTerm| <= (sum_d |lambda(d)|)^2.
```

No cancellation assumption is used.

## Combined square-majorant budget

```text
TS146.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_l1_sq
TS146.Goldbach.WeightedLCMErrorAggregation
TS146.Goldbach.weightedLCMErrorAggregation
TS146.Goldbach.weightedLCMErrorAggregationTarget
```

For every positive Selberg level, the concrete rational square majorant now
satisfies

```text
squareMajorant <= intervalLength / D + (sum_d |lambda(d)|)^2.
```

The first term is supplied unconditionally by TS145 and the second term is the
unconditional finite aggregation proved in TS146.

## Remaining work

TS146 does not yet estimate the finite `L1` norm of the reconstructed weights,
estimate the optimization denominator effectively, or compare the combined
bound with the final Brun-Titchmarsh ceiling budget.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS146.WeightedLCMErrorAggregation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS146
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
