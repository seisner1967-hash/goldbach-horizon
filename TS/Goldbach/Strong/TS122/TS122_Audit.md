# TS122 Audit - Selberg Diagonal Optimization Ledger

## Status

`repo_committed_relative`

TS122 starts the analytic optimization layer above the corrected Selberg
dense-to-diagonal identity closed in TS121. It proves a genuine finite
weighted Cauchy inequality over `Rat`, then specializes it to the corrected
Jordan-two diagonal side.

## Added file

```text
TS/Goldbach/Strong/TS122/SelbergDiagonalOptimizationLedger.lean
```

## Main declarations

```lean
TS122.Goldbach.finite_weighted_cauchy_rat
TS122.Goldbach.selbergOptimizationSupport
TS122.Goldbach.selbergMobiusRatCoefficient
TS122.Goldbach.selbergJordanTwoPenalty
TS122.Goldbach.selbergDiagonalEnergy
TS122.Goldbach.selbergMobiusLinearForm
TS122.Goldbach.selbergOptimizationDenominator
TS122.Goldbach.selbergDiagonalWeightedCauchy
TS122.Goldbach.selbergDiagonalEnergy_lower_bound_of_constraint
TS122.Goldbach.SelbergDiagonalOptimization
TS122.Goldbach.selbergDiagonalOptimization
TS122.Goldbach.SelbergDiagonalOptimizationTarget
TS122.Goldbach.selbergDiagonalOptimizationTarget
TS122.Goldbach.selbergJordanTwoFiniteSupportCollapseTarget
```

## Concrete proofs

### TS122-R1: finite weighted Cauchy over `Rat`

```lean
finite_weighted_cauchy_rat
```

proves, for a finite support and positive weights `penalty`,

```text
(sum_i c_i y_i)^2
<=
(sum_i c_i^2 / penalty_i) * (sum_i penalty_i y_i^2).
```

The proof uses Mathlib's finite Cauchy-Schwarz lemma
`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`, plus rational field
normalization.

### TS122-R2: Selberg Jordan-two specialization

```lean
selbergDiagonalWeightedCauchy
```

specializes the generic weighted Cauchy inequality to the corrected Selberg
diagonal form

```text
sum_d J2(d) y_d^2
```

on the positive finite support from TS121.

### TS122-R3: constrained lower bound

```lean
selbergDiagonalEnergy_lower_bound_of_constraint
```

proves that, if the Mobius linear constraint is normalized to `1`, then

```text
1 / denominator <= diagonal energy.
```

This is the finite weighted-Cauchy optimization inequality expected in the
Selberg diagonal layer.

## Remaining obligations

TS122 does not yet prove:

- positivity of `J2(d)` on the positive finite support;
- positivity/non-vanishing of the optimization denominator;
- construction of the attaining optimal vector;
- Selberg's sieve bound;
- Brun-Titchmarsh;
- any prime-count estimate.

Those are kept as explicit local obligations in
`SelbergDiagonalOptimization`.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS122\SelbergDiagonalOptimizationLedger.lean
lake build TS.Goldbach.Strong.TS122.SelbergDiagonalOptimizationLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS122
git diff --check -- README.md TS\Goldbach\Strong\TS122\SelbergDiagonalOptimizationLedger.lean TS\Goldbach\Strong\TS122\TS122_Audit.md
```

## Verdict

TS122 is the first post-TS121 analytic optimization step. It does not merely
refine architecture: it proves the finite weighted Cauchy inequality that will
control the corrected diagonal Selberg energy once the remaining arithmetic
positivity facts for `J2` are supplied.
