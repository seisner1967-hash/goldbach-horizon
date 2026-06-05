# TS128 Audit - Selberg Optimal Vector Normalization

## Scope

TS128 closes the finite optimal-vector algebra for the TS122 weighted Cauchy
optimization layer.

It defines the optimal diagonal vector

```text
y_d = mobius(d) / (D * J2(d))
```

where

```text
D = sum_d mobius(d)^2 / J2(d)
```

over the TS122 finite optimization support.

## Concrete Lean objects

The sprint adds:

```lean
TS128.Goldbach.finiteWeightedCauchyDenominator
TS128.Goldbach.finiteWeightedCauchyOptimalVector
TS128.Goldbach.finiteWeightedCauchyOptimalVector_linear_constraint
TS128.Goldbach.finiteWeightedCauchyOptimalVector_energy_eq
TS128.Goldbach.selbergOptimalDiagonalVector
TS128.Goldbach.selbergOptimalDiagonalVector_eq_candidate
TS128.Goldbach.finiteWeightedCauchyDenominator_selberg
TS128.Goldbach.selbergJordanTwoPenalty_ne_on_support
TS128.Goldbach.selbergOptimizationDenominator_ne
TS128.Goldbach.selbergOptimalDiagonalVector_linear_constraint
TS128.Goldbach.selbergOptimalDiagonalVector_energy_eq
TS128.Goldbach.selbergOptimalDiagonalVector_lower_bound_sharp
TS128.Goldbach.SelbergOptimalVectorNormalization
TS128.Goldbach.selbergOptimalVectorNormalization
TS128.Goldbach.SelbergOptimalVectorNormalizationTarget
TS128.Goldbach.selbergOptimalVectorNormalizationTarget
TS128.Goldbach.selbergJordanTwoFullPositivityDischargeTarget
```

## What is proved

TS128 first proves two generic rational identities for a finite weighted Cauchy
problem. If every penalty is nonzero on the support and the denominator is
nonzero, then the vector

```text
y_i = c_i / (D * a_i)
```

has linear form `1` and energy `1 / D`.

The Selberg specialization uses:

```text
c_d = TS122.Goldbach.selbergMobiusRatCoefficient d
a_d = TS122.Goldbach.selbergJordanTwoPenalty d
D   = TS122.Goldbach.selbergOptimizationDenominator level
```

The required nonzero facts come from TS127: `J2(d) > 0` on the support and
`D > 0` for `0 < level`.

Thus TS128 proves, for `0 < level`:

```text
TS122.Goldbach.selbergMobiusLinearForm level optimalVector = 1
TS122.Goldbach.selbergDiagonalEnergy level optimalVector = 1 / D
```

where `optimalVector` is definitionally the TS123 candidate.

## Remaining obligations

TS128 does not prove the Selberg sieve bound, Brun-Titchmarsh, the spectral
trace package, or the Mellin-tail package.

## Verification

Expected checks:

```text
lake build TS.Goldbach.Strong.TS128.SelbergOptimalVectorNormalization
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS128
git diff --check -- README.md TS\Goldbach\Strong\TS128\SelbergOptimalVectorNormalization.lean TS\Goldbach\Strong\TS128\TS128_Audit.md
```
