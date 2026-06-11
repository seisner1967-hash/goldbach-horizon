# TS145 Audit

## Scope

TS145 discharges the two arithmetic inputs isolated by TS144:

```text
TS144.Goldbach.SelbergGcdEulerTotientDiagonalization
TS144.Goldbach.SelbergEulerTotientLeJordanTwoOnSupport
```

The corrected `1/lcm` main-term budget is therefore unconditional for every
positive Selberg level.

## Euler diagonalization

```text
TS145.Goldbach.absorbedDiagonalVector_eq_eulerTransformedWeight
TS145.Goldbach.eulerDiagonalSide_eq_tripleSum
TS145.Goldbach.eulerDiagonalTripleSum_eq_pairFirst
TS145.Goldbach.optimizationSupport_filter_dvd_gcd_eq_divisors
TS145.Goldbach.eulerPairCoefficient_eq_gcd
TS145.Goldbach.eulerPairFirstSide_eq_gcdDenseSide
TS145.Goldbach.gcdEulerTotientDiagonalization
```

The proof expands the diagonal square, performs finite Fubini reindexing, and
uses Mathlib's Gauss identity

```text
sum_{r | g} Nat.totient r = g.
```

Support closure is proved explicitly from the positive bounded TS122 support.

## Jordan domination

```text
TS145.Goldbach.totient_prime_pow_le_jordanTwo
TS145.Goldbach.totient_le_jordanTwo
TS145.Goldbach.eulerTotientLeJordanTwoOnSupport
```

The prime-power inequality compares

```text
totient(p^(k+1)) = p^k * (p-1)
J2(p^(k+1)) = p^(2k) * (p^2-1).
```

The global theorem multiplies these inequalities over `Nat.factorization`,
using the multiplicativity infrastructure from TS126.

## Closed budget

```text
TS145.Goldbach.selbergLCMDenseSideBudgetUpperBound
TS145.Goldbach.selbergFractionalMainTerm_le_optimalBudget
TS145.Goldbach.EulerTotientJordanDominationDischarge
TS145.Goldbach.eulerTotientJordanDominationDischargeTarget
```

For every `0 < level`, TS145 now proves

```text
selbergLCMDenseSideRat(level) <= 1 / optimizationDenominator(level)
```

and the corresponding interval-length upper bound for the TS142 fractional
main term.

## Remaining work

TS145 does not aggregate the weighted TS143 error term, estimate the
optimization denominator asymptotically, or prove the Brun-Titchmarsh budget
comparison.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS145.EulerTotientDiagonalizationJordanDomination
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS145
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
