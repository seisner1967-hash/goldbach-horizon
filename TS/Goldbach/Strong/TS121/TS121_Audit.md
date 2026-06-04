# TS121 Audit - Selberg Jordan-Two Finite Support Collapse

## Status

`repo_committed`

TS121 discharges the finite-support issue left by TS120 for the corrected
TS118--TS119 gcd-square route.

It proves the local coefficient collapse on the positive part of the finite
support window and then uses the absorbed weights from TS118 to handle the
zero index. Since

```text
selbergLCMAbsorbedWeight weight 0 = 0
```

the zero-index pair terms vanish in the weighted pair-first sum. The positive
terms use the fact that every divisor of `gcd(m,n)` lies in
`range (level + 1)` whenever `0 < m` and `m` is in that support. This converts
the TS120 finite filtered coefficient to the full divisor sum from TS119.

Consequently TS121 proves:

```text
original dense gcd/lcm side
= corrected Jordan-two diagonal side with absorbed weights
```

for every finite level and weight.

This sprint does not prove the square-sum majorant, Selberg's sieve,
Brun-Titchmarsh, interval majorant, budget comparison, or any prime-count
estimate.

## File

```text
TS/Goldbach/Strong/TS121/SelbergJordanTwoFiniteSupportCollapse.lean
```

## Key declarations

```lean
TS121.Goldbach.selbergPositiveQuadraticSupport
TS121.Goldbach.mem_selbergPositiveQuadraticSupport
TS121.Goldbach.selbergJordanTwoPairCoefficient_eq_filter
TS121.Goldbach.selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left
TS121.Goldbach.selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left
TS121.Goldbach.SelbergJordanTwoPositiveLocalCoefficientCollapse
TS121.Goldbach.selbergJordanTwoPositiveLocalCoefficientCollapse
TS121.Goldbach.selbergLCMAbsorbedWeight_zero
TS121.Goldbach.selbergAbsorbedPairCoefficientTerm_eq_gcdSquareTerm
TS121.Goldbach.selbergJordanTwoPairFirstSide_absorbed_eq_gcdSquareDenseSide
TS121.Goldbach.selbergGcdSquareDenseSide_absorbed_eq_jordanDiagonalSide
TS121.Goldbach.selbergOriginalDenseSide_eq_correctedJordanDiagonalSide
TS121.Goldbach.SelbergJordanTwoFiniteSupportCollapse
TS121.Goldbach.selbergJordanTwoFiniteSupportCollapse
TS121.Goldbach.SelbergJordanTwoFiniteSupportCollapseTarget
TS121.Goldbach.selbergJordanTwoFiniteSupportCollapseTarget
TS121.Goldbach.selbergGcdSquareGlobalReindexingTarget
```

## Proof summary

The theorem

```lean
TS121.Goldbach.selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left
```

shows that, for positive `m` in the TS108 support, filtering the level support
by divisibility into `gcd(m,n)` gives exactly `(Nat.gcd m n).divisors`.

The theorem

```lean
TS121.Goldbach.selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left
```

combines that support equality with the TS119 Jordan-two identity:

```text
sum_{d | g} J2(d) = g^2
```

to prove the positive local coefficient collapse.

The theorem

```lean
TS121.Goldbach.selbergAbsorbedPairCoefficientTerm_eq_gcdSquareTerm
```

handles all pair terms for absorbed weights. If `m = 0`, the absorbed weight is
zero; if `0 < m`, the positive local coefficient collapse applies.

The theorem

```lean
TS121.Goldbach.selbergOriginalDenseSide_eq_correctedJordanDiagonalSide
```

combines TS118 lcm absorption with the TS120 reindexing and the TS121
finite-support collapse to close the corrected dense-to-diagonal identity.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS121.SelbergJordanTwoFiniteSupportCollapse
rg -n "s[o]rry" TS\Goldbach\Strong\TS121
rg -n "a[x]iom" TS\Goldbach\Strong\TS121
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS121
git diff --check -- README.md TS\Goldbach\Strong\TS121\SelbergJordanTwoFiniteSupportCollapse.lean TS\Goldbach\Strong\TS121\TS121_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS121-R1 | `selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left` | `repo_committed` | proves finite support contains all divisors of the positive gcd |
| TS121-R2 | `selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left` | `repo_committed` | proves the positive local coefficient collapse |
| TS121-R3 | `selbergLCMAbsorbedWeight_zero` | `repo_committed` | proves the absorbed zero-index weight vanishes |
| TS121-R4 | `selbergAbsorbedPairCoefficientTerm_eq_gcdSquareTerm` | `repo_committed` | proves the weighted pair-term collapse, including zero |
| TS121-R5 | `selbergOriginalDenseSide_eq_correctedJordanDiagonalSide` | `repo_committed` | closes the corrected dense-to-diagonal identity with absorbed weights |
| TS121-I1 | `SelbergJordanTwoFiniteSupportCollapse` | `repo_committed` | packages TS120 reindexing plus the finite-support discharge |
| TS121-T1 | `selbergGcdSquareGlobalReindexingTarget` | `repo_committed` | keeps the TS120 corrected global reindexing target available |

## Remaining work

The arithmetic route can now move past corrected dense-to-diagonal reindexing.
The next local task is the square-sum majorant for the corrected Jordan-two
diagonal side, followed by the Selberg sieve interval bound and the
Brun-Titchmarsh budget comparison.
