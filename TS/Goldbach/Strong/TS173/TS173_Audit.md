# TS173 Audit - Triangle Spline Fourier Identification Discharge

## Sprint Scope

TS173 closes the TS168 branch-integral route by assembling the four local
obligations already proved in TS169 through TS172.

This sprint proves:

```lean
TS166.Goldbach.TriangleSplineFourierIdentificationStatement
```

It does not prove Plancherel, the Riemann-von Mangoldt explicit formula, or any
Goldbach conclusion.

## Main Declarations

- `TS173.Goldbach.triangleSplineFourierIdentification`
- `TS173.Goldbach.TriangleSplineFourierIdentificationLedger`
- `TS173.Goldbach.triangleSplineFourierIdentificationLedger`
- `TS173.Goldbach.TriangleSplineFourierIdentificationTarget`
- `TS173.Goldbach.triangleSplineFourierIdentificationTarget`

## What Is Proved

TS173 applies:

```lean
TS168.Goldbach.branchIntegralRoute_implies_ts166
```

to the four discharged obligations:

```lean
TS172.Goldbach.branchSplitFourier
TS171.Goldbach.leftBranchIntegralEvaluation
TS170.Goldbach.rightBranchIntegralEvaluation
TS169.Goldbach.branchClosedFormRecombination
```

This gives the full pointwise Fourier-identification statement from TS166.  In
words, Mathlib's Fourier integral of the complexified triangle spline is the
pi-scale squared-sinc candidate selected by TS165 and TS166.

## Explicit Non-Claims

TS173 does not prove:

- Plancherel;
- the Riemann-von Mangoldt explicit formula;
- any Goldbach theorem.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS173.TriangleSplineFourierIdentificationDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS173
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
