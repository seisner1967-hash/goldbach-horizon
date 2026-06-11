# TS150 Audit

## Scope

TS150 packages the unconditional TS149 rational bound as a refined Selberg
budget, proves the ceiling bridge to the TS138 natural majorant, and isolates
the remaining Brun-Titchmarsh comparison as one parametric scale contract.

The sprint does not choose a final Selberg level and does not assert any false
growth estimate for the TS122 denominator.

Status: `repo_committed_relative`.

## Refined budget

```text
TS150.Goldbach.refinedSelbergBudgetRat
TS150.Goldbach.refinedSelbergBudgetCeil
TS150.Goldbach.selbergConcreteSquareMajorantRat_le_refinedSelbergBudgetRat
```

The rational budget is

```text
intervalLength / D(level) + (level / D(level))^2.
```

TS149 proves that the TS138 rational square majorant is bounded by this value
for every positive level.

## Ceiling bridge

```text
TS150.Goldbach.selbergConcreteMajorantValue_le_refinedSelbergBudgetCeil
```

The TS138 natural majorant is already the ceiling of the rational square sum.
Monotonicity of `Nat.ceil` therefore gives

```text
selbergConcreteMajorantValue <= refinedSelbergBudgetCeil.
```

This passage is unconditional and contains no additional analytic estimate.

## Parametric Brun-Titchmarsh contract

```text
TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh
TS150.Goldbach.selbergConcreteMajorantValue_le_brunTitchmarshCeilBudget
TS150.Goldbach.RefinedSelbergBudgetScaleComparison
```

The only remaining scale inequality is named as

```text
ceil(refinedSelbergBudgetRat level x Q)
  <= brunTitchmarshCeilBudget x Q.
```

The uniform package requests this comparison only in the parameter regime
used by TS139. The budget is independent of the interval left endpoint `n`.

## High-level assembly

```text
TS150.Goldbach.concreteSelbergSquareBudgetComparison
TS150.Goldbach.concreteSelbergIntervalSieveTheoremLedger
TS150.Goldbach.selbergSieveWeightInfrastructure
TS150.Goldbach.brunTitchmarshFinalInputLedger
TS150.Goldbach.RefinedSelbergBudgetScaleLedger
TS150.Goldbach.refinedSelbergBudgetScaleBridgeTarget
```

A TS140 large-prime admissibility package plus the TS150 scale comparison now
construct the complete TS139 interval-sieve ledger. The resulting object
exposes the TS99 Selberg weight infrastructure and the TS97 final
Brun-Titchmarsh input.

## Remaining work

TS150 does not select `level` as a function of `x` and `Q`, prove the refined
ceiling comparison, or discharge the geometric condition `level < n` required
by TS140. Those are now explicit and separate parametric inputs.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS150.RefinedSelbergBudgetScaleInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS150
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
