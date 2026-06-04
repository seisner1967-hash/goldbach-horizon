# TS119 Audit - Selberg Jordan-Two GCD-Square Diagonalization Ledger

## Status

`repo_committed_relative`

TS119 opens the corrected diagonalization layer after TS118. It introduces the
Jordan totient coefficient of order two as an arithmetic function over `Rat`:

```text
J2 = moebius * pow 2
```

and proves the local divisor-sum collapse:

```text
sum_{d | g} J2(d) = g^2
```

using Mathlib's `ArithmeticFunction` convolution API.

The sprint also defines the corrected diagonal side for the absorbed
gcd-square dense form. It does not yet prove the global finite reindexing
identity between the absorbed dense side and the Jordan-two diagonal side.
That global equality remains a proposition-valued obligation.

This sprint does not prove the corrected dense-to-diagonal identity,
square-sum majorant, Selberg's sieve, Brun-Titchmarsh, interval majorant,
budget comparison, or any prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS119/SelbergJordanTwoGcdSquareDiagonalizationLedger.lean
```

## Key declarations

```lean
TS119.Goldbach.selbergJordanTwoFunction
TS119.Goldbach.selbergJordanTwoCoefficient
TS119.Goldbach.selbergJordanTwoFunction_eq_moebius_mul_pow_two
TS119.Goldbach.zeta_mul_selbergJordanTwoFunction
TS119.Goldbach.selbergJordanTwoCoefficient_divisor_sum_eq_square
TS119.Goldbach.selbergGcdSquareTransformedWeight
TS119.Goldbach.selbergGcdSquareTransformedWeight_expansion
TS119.Goldbach.selbergJordanTwoDiagonalSquareTerm
TS119.Goldbach.selbergJordanTwoDiagonalSide
TS119.Goldbach.selbergJordanTwoDiagonalSide_expansion
TS119.Goldbach.SelbergGcdSquareDiagonalization
TS119.Goldbach.selbergGcdSquareDiagonalization
TS119.Goldbach.SelbergGcdSquareDiagonalizationTarget
TS119.Goldbach.selbergGcdSquareDiagonalizationTarget
TS119.Goldbach.selbergLCMAbsorptionBridgeTarget
```

## Proof summary

The theorem

```lean
TS119.Goldbach.zeta_mul_selbergJordanTwoFunction
```

proves:

```text
zeta * J2 = pow 2
```

where `J2 = moebius * pow 2`. The proof uses associativity of Dirichlet
convolution and Mathlib's theorem
`ArithmeticFunction.coe_zeta_mul_coe_moebius`.

The theorem

```lean
TS119.Goldbach.selbergJordanTwoCoefficient_divisor_sum_eq_square
```

evaluates the previous arithmetic-function identity at `g` and rewrites the
zeta convolution with `ArithmeticFunction.coe_zeta_mul_apply`, giving:

```text
sum_{d | g} J2(d) = g^2
```

The structure

```lean
TS119.Goldbach.SelbergGcdSquareDiagonalization
```

packages the TS118 lcm-absorption bridge, the absorbed weight, the corrected
gcd-square dense side, the Jordan-two transformed weight, the corrected
diagonal side, the proved local `J2` collapse, and the remaining global
finite-reindexing obligation.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS119.SelbergJordanTwoGcdSquareDiagonalizationLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS119
rg -n "a[x]iom" TS\Goldbach\Strong\TS119
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS119
git diff --check -- README.md TS\Goldbach\Strong\TS119\SelbergJordanTwoGcdSquareDiagonalizationLedger.lean TS\Goldbach\Strong\TS119\TS119_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS119-R1 | `zeta_mul_selbergJordanTwoFunction` | `repo_committed` | proves `zeta * J2 = pow 2` by Mathlib convolution |
| TS119-R2 | `selbergJordanTwoCoefficient_divisor_sum_eq_square` | `repo_committed` | proves `sum_{d | g} J2(d) = g^2` |
| TS119-R3 | `selbergJordanTwoDiagonalSide_expansion` | `repo_committed` | exposes the corrected finite diagonal side |
| TS119-I1 | `SelbergGcdSquareDiagonalization` | `repo_committed_relative` | packages the corrected diagonalization layer and the remaining global identity |
| TS119-T1 | `selbergLCMAbsorptionBridgeTarget` | `repo_committed` | keeps the TS118 lcm-absorption target available |

## Remaining work

The next local task is to prove the finite reindexing identity:

```text
sum_{m,n} a(m) a(n) * gcd(m,n)^2
=
sum_d J2(d) * (sum_{d | m} a(m))^2
```

where `a(m) = w(m)/m` is the absorbed weight from TS118. Once that is
discharged, the arithmetic route can move to the square-sum majorant and the
Selberg sieve bound.
