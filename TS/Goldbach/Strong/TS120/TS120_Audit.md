# TS120 Audit - Selberg GCD-Square Global Reindexing Ledger

## Status

`repo_committed_relative`

TS120 opens the corrected global reindexing layer after TS118 and TS119. It
works only with the corrected absorbed gcd-square route, not with the older
gcd/lcm diagonalization path diagnosed as obstructed by TS117.

The sprint proves concrete finite-sum transformations:

```text
corrected Jordan-two diagonal side
= diagonal-first triple sum
= gcd-filtered triple sum
= pair-first local-coefficient sum
```

The remaining local coefficient collapse is kept as a proposition-valued
obligation:

```text
sum_{d in support, d | gcd(m,n)} J2(d) = gcd(m,n)^2
```

on the finite TS108 support window. If this local collapse is supplied, TS120
proves that the corrected absorbed gcd-square dense side equals the corrected
Jordan-two diagonal side.

This sprint does not yet prove the support-sensitive local coefficient
collapse, the full corrected dense-to-diagonal identity unconditionally, the
square-sum majorant, Selberg's sieve, Brun-Titchmarsh, interval majorant,
budget comparison, or any prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS120/SelbergGcdSquareGlobalReindexingLedger.lean
```

## Key declarations

```lean
TS120.Goldbach.selbergJordanTwoDiagonalFilterTerm
TS120.Goldbach.selbergJordanTwoDiagonalTripleTerm
TS120.Goldbach.selbergJordanTwoDiagonalTripleSum
TS120.Goldbach.selbergJordanTwoDiagonalSquareTerm_triple_expansion
TS120.Goldbach.selbergJordanTwoDiagonalSide_triple_expansion
TS120.Goldbach.selbergJordanTwoDivisorPairFilter
TS120.Goldbach.selbergJordanTwoGcdFilterTerm
TS120.Goldbach.selbergJordanTwoDiagonalFilterTerm_mul_eq_pairFilter
TS120.Goldbach.selbergJordanTwoDivisorPairFilter_eq_gcdFilter
TS120.Goldbach.selbergJordanTwoDiagonalTripleTerm_eq_gcdFilter
TS120.Goldbach.selbergJordanTwoGcdFilteredTripleSum
TS120.Goldbach.selbergJordanTwoDiagonalTripleSum_eq_gcdFilteredTripleSum
TS120.Goldbach.selbergJordanTwoPairCoefficient
TS120.Goldbach.selbergJordanTwoPairFirstTerm
TS120.Goldbach.selbergJordanTwoPairFirstSide
TS120.Goldbach.selbergJordanTwoInnerGcdSum_factor
TS120.Goldbach.selbergJordanTwoGcdFilteredTripleSum_reordered
TS120.Goldbach.selbergJordanTwoDiagonalSide_eq_pairFirst
TS120.Goldbach.SelbergJordanTwoLocalCoefficientCollapse
TS120.Goldbach.selbergJordanTwoPairFirstSide_eq_gcdSquareDenseSide_of_localCollapse
TS120.Goldbach.selbergGcdSquareDenseSide_eq_jordanDiagonalSide_of_localCollapse
TS120.Goldbach.SelbergGcdSquareGlobalReindexing
TS120.Goldbach.selbergGcdSquareGlobalReindexing
TS120.Goldbach.SelbergGcdSquareGlobalReindexingTarget
TS120.Goldbach.selbergGcdSquareGlobalReindexingTarget
TS120.Goldbach.selbergGcdSquareDiagonalizationTarget
TS120.Goldbach.selbergLCMAbsorptionBridgeTarget
```

## Proof summary

The theorem

```lean
TS120.Goldbach.selbergJordanTwoDiagonalSquareTerm_triple_expansion
```

expands one corrected Jordan-two diagonal square by `Finset.sum_mul_sum`.

The theorem

```lean
TS120.Goldbach.selbergJordanTwoDivisorPairFilter_eq_gcdFilter
```

proves the finite divisor-filter rewrite:

```text
d | m and d | n  <->  d | gcd(m,n)
```

using `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, and `Nat.dvd_gcd`.

The theorem

```lean
TS120.Goldbach.selbergJordanTwoGcdFilteredTripleSum_reordered
```

uses `Finset.sum_comm` to reorder the corrected gcd-filtered triple sum into
pair-first order and isolates the local coefficient.

Finally,

```lean
TS120.Goldbach.selbergGcdSquareDenseSide_eq_jordanDiagonalSide_of_localCollapse
```

shows that a support-local coefficient collapse is sufficient to close the
corrected absorbed dense-to-diagonal identity.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS120.SelbergGcdSquareGlobalReindexingLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS120
rg -n "a[x]iom" TS\Goldbach\Strong\TS120
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS120
git diff --check -- README.md TS\Goldbach\Strong\TS120\SelbergGcdSquareGlobalReindexingLedger.lean TS\Goldbach\Strong\TS120\TS120_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS120-R1 | `selbergJordanTwoDiagonalSquareTerm_triple_expansion` | `repo_committed` | expands one corrected diagonal square to a double sum |
| TS120-R2 | `selbergJordanTwoDiagonalSide_triple_expansion` | `repo_committed` | expands the corrected diagonal side to a triple sum |
| TS120-R3 | `selbergJordanTwoDiagonalTripleSum_eq_gcdFilteredTripleSum` | `repo_committed` | rewrites pair divisibility filters as one gcd filter |
| TS120-R4 | `selbergJordanTwoGcdFilteredTripleSum_reordered` | `repo_committed` | reorders the corrected triple sum pair-first |
| TS120-R5 | `selbergJordanTwoDiagonalSide_eq_pairFirst` | `repo_committed` | identifies the corrected diagonal side with the pair-first coefficient side |
| TS120-I1 | `SelbergJordanTwoLocalCoefficientCollapse` | `repo_committed_relative` | support-local coefficient collapse still needed for the dense side |
| TS120-I2 | `SelbergGcdSquareGlobalReindexing` | `repo_committed_relative` | packages the corrected global reindexing and remaining local collapse |
| TS120-T1 | `selbergGcdSquareDiagonalizationTarget` | `repo_committed` | keeps the TS119 corrected diagonalization target available |
| TS120-T2 | `selbergLCMAbsorptionBridgeTarget` | `repo_committed` | keeps the TS118 lcm-absorption target available |

## Remaining work

The next local task is to discharge:

```text
sum_{d in support, d | gcd(m,n)} J2(d) = gcd(m,n)^2
```

on the finite support window used by TS108/TS120. This must handle the
support-bound and zero-index cases explicitly. Once it is proved, the corrected
absorbed gcd-square dense side equals the corrected Jordan-two diagonal side.
