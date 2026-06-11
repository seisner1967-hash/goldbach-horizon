# TS143 Audit

## Scope

TS143 discharges the local interval-counting obligation left by TS142:

```text
abs(lcmMultiplicityErrorRat x Q n d1 d2) <= 1
```

for every positive modulus `lcm(d1,d2)`.

## Concrete proofs

```text
TS143.Goldbach.closedIntervalMultipleCount_eq_ceil_sub_ceil
TS143.Goldbach.closedIntervalMultipleCount_error_abs_le_one
TS143.Goldbach.lcmMultiplicityErrorRat_abs_le_one
TS143.Goldbach.lcmMultiplicityErrorBound
TS143.Goldbach.lcmMultiplicityErrorBoundDischargeTarget
```

The proof rewrites the closed interval `[n,n+h]` as the half-open interval
`[n,n+h+1)`, applies Mathlib's exact `Nat.Ico_filter_modEq_card` theorem, and
uses the bounds

```text
q <= ceil(q) < q + 1
```

at the two interval endpoints.  Their difference has absolute value at most
one.

## Remaining input

```text
TS142.Goldbach.SelbergLCMDenseSideExactBudget
```

TS143 does not identify the `1/lcm` quadratic form with the TS122 optimization
budget, aggregate the weighted error term, estimate the denominator, or prove
the Brun-Titchmarsh budget comparison.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS143.LCMMultiplicityErrorBoundDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS143
git diff --check
```

Expected result: build succeeds and the audit searches return no matches.
