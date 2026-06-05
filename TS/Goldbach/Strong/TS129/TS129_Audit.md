# TS129 Audit - Selberg Diagonal Budget Majorant Ledger

## Scope

TS129 connects the corrected dense-to-diagonal identity from TS121 with the
optimal diagonal-vector algebra from TS128.

It does not prove the interval Selberg sieve bound. Instead, it proves the
finite diagonal budget statements that must feed that future sieve-majorant
step.

## Concrete Lean objects

The sprint adds:

```lean
TS129.Goldbach.selbergAbsorbedDiagonalVector
TS129.Goldbach.selbergAbsorbedDiagonalVector_zero
TS129.Goldbach.selbergCorrectedJordanDiagonalSide_eq_diagonalEnergy
TS129.Goldbach.selbergOriginalDenseSide_eq_absorbedDiagonalEnergy
TS129.Goldbach.selbergDenseSide_budget_lower_bound_of_mobius_constraint
TS129.Goldbach.selbergDenseSide_eq_optimal_budget_of_absorbedVector_eq_optimal
TS129.Goldbach.SelbergDiagonalBudgetMajorant
TS129.Goldbach.selbergDiagonalBudgetMajorant
TS129.Goldbach.SelbergSieveMajorantFromDiagonalBudget
TS129.Goldbach.selbergSieveWeightInfrastructure_of_diagonalBudget
TS129.Goldbach.SelbergDiagonalBudgetMajorantTarget
TS129.Goldbach.selbergDiagonalBudgetMajorantTarget
TS129.Goldbach.SelbergSieveMajorantFromDiagonalBudgetTarget
TS129.Goldbach.selbergSieveWeightInfrastructureTarget_of_diagonalBudgetTarget
TS129.Goldbach.selbergOptimalVectorNormalizationTarget
```

## What is proved

TS129 defines the absorbed diagonal vector

```text
Y_d = sum_m 1_{d | m} * (weight(m) / m)
```

using the corrected TS119 transformed-weight function applied to the TS118
absorbed weights.

It proves that the zero divisor coordinate vanishes:

```text
Y_0 = 0.
```

This allows the full TS119 diagonal side, whose support includes zero, to be
identified with the TS122 positive-support diagonal energy:

```text
corrected Jordan diagonal side
=
TS122 diagonal energy of Y.
```

Combining this with TS121 gives the concrete bridge:

```text
original dense gcd/lcm side
=
TS122 diagonal energy of Y.
```

Finally, TS129 proves the budget consequence: if `0 < level` and the absorbed
diagonal vector satisfies the Mobius constraint, then the original dense side
is bounded below by the optimal TS122 denominator budget:

```text
1 / D <= original dense side.
```

It also proves that if the absorbed diagonal vector is exactly the TS128 optimal
vector, then the original dense side is exactly:

```text
1 / D.
```

## Remaining obligations

TS129 does not prove:

```text
* the construction of original Selberg weights realizing the optimal diagonal
  vector;
* the interval Selberg sieve majorant;
* the Selberg majorant budget comparison;
* Brun-Titchmarsh;
* any prime-count estimate;
* the spectral trace package;
* the Mellin-tail package.
```

Those are kept as local package fields in
`SelbergSieveMajorantFromDiagonalBudget`, which feeds the existing TS99
Selberg-weight infrastructure once the interval majorant, sieve theorem, and
budget comparison are supplied.

## Verification

Expected checks:

```text
lake build TS.Goldbach.Strong.TS129.SelbergDiagonalBudgetMajorantLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS129
git diff --check -- README.md TS\Goldbach\Strong\TS129\SelbergDiagonalBudgetMajorantLedger.lean TS\Goldbach\Strong\TS129\TS129_Audit.md
```
