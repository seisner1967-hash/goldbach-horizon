# TS144 Audit

## Scope

TS144 corrects the exact-budget premise left in TS142.  The TS142 main-term
kernel is `1/lcm`, while the exact TS136 budget concerns `gcd/lcm`; these
kernels cannot be identified silently.

## Concrete proofs

```text
TS144.Goldbach.one_div_lcm_ne_gcd_div_lcm_at_two
TS144.Goldbach.selbergLCMDenseSideBudgetUpperBound_of_exact
TS144.Goldbach.one_div_lcm_eq_gcd_div_mul
TS144.Goldbach.selbergLCMDenseSide_eq_gcdAbsorbedDenseSide
TS144.Goldbach.selbergEulerTotientDiagonalSide_le_jordanEnergy
TS144.Goldbach.selbergOptimalAbsorbedJordanEnergy_eq_budget
TS144.Goldbach.selbergLCMDenseSideBudgetUpperBound_of_totient_route
TS144.Goldbach.selbergFractionalMainTerm_le_optimalBudget
TS144.Goldbach.lcmDenseSideBudgetRefactorTarget
```

The pointwise diagnostic at `(2,2)` proves that `1/lcm` and `gcd/lcm` are
different kernels.  The positive-support identity

```text
1 / lcm(d1,d2) = gcd(d1,d2) / (d1*d2)
```

then rewrites the TS142 quadratic form as an absorbed gcd-kernel form.

## Corrected contract

TS144 replaces the obstructed exact premise by the sufficient upper bound

```text
selbergLCMDenseSideRat(level) <= 1 / optimizationDenominator(level).
```

It proves that this bound follows from two explicit arithmetic inputs:

```text
SelbergGcdEulerTotientDiagonalization
SelbergEulerTotientLeJordanTwoOnSupport
```

The first is the finite diagonalization of `gcd` with Euler's totient.  The
second compares that diagonal energy with the Jordan-two energy already
proved equal to `1 / D` by TS129/TS136.

## Remaining inputs

TS144 does not yet prove the Euler-totient diagonalization, the coefficientwise
`totient <= J2` comparison, the weighted aggregation of the TS143 local error,
the denominator asymptotic, or the Brun-Titchmarsh budget comparison.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS144.LCMDenseSideBudgetRefactor
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS144
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
