# TS172 Audit - Triangle Spline Fourier Branch Split

## Sprint Scope

TS172 discharges the remaining topological obligation in the TS168 fallback
branch route: the global Fourier integral of the triangle spline splits into
the two directed branch integrals over `[-1,0]` and `[0,1]`.

This sprint proves only
`TS168.Goldbach.BranchSplitFourierStatement`.  It deliberately does not yet
assemble the full TS166 Fourier identification, and it does not prove
Plancherel or the explicit formula.

## Main Declarations

- `TS172.Goldbach.globalBranchIntegrand`
- `TS172.Goldbach.triangleSplineMathlibFourier_eq_globalIntegral`
- `TS172.Goldbach.globalBranchIntegrand_eq_zero_of_not_mem_Ioc`
- `TS172.Goldbach.globalIntegral_eq_intervalIntegral`
- `TS172.Goldbach.leftBranchFourierIntegrand_continuous`
- `TS172.Goldbach.rightBranchFourierIntegrand_continuous`
- `TS172.Goldbach.globalBranchIntegrand_intervalIntegrable_left`
- `TS172.Goldbach.globalBranchIntegrand_intervalIntegrable_right`
- `TS172.Goldbach.globalIntervalIntegral_left_eq_leftBranch`
- `TS172.Goldbach.globalIntervalIntegral_right_eq_rightBranch`
- `TS172.Goldbach.branchSplitFourier`
- `TS172.Goldbach.TriangleSplineFourierBranchSplitLedger`
- `TS172.Goldbach.triangleSplineFourierBranchSplitLedger`
- `TS172.Goldbach.TriangleSplineFourierBranchSplitTarget`
- `TS172.Goldbach.triangleSplineFourierBranchSplitTarget`

## What Is Proved

TS172 proves:

```lean
TS168.Goldbach.BranchSplitFourierStatement
```

That is, for every `xi : Real`,

```lean
TS166.Goldbach.triangleSplineMathlibFourier xi =
  TS168.Goldbach.leftBranchFourierIntegral xi +
    TS168.Goldbach.rightBranchFourierIntegral xi
```

The proof first rewrites `Real.fourierIntegral` as Mathlib's explicit global
Bochner integral with the TS168 forward kernel.  It then restricts the global
integral to `Set.Ioc (-1) 1` using the spline support vanishing from TS162,
rewrites this restricted integral as the directed interval integral over
`[-1,1]`, splits the interval at `0`, and identifies the two resulting
interval integrals with the TS168 left and right affine branch integrals using
the branch formulae from TS56.

## Explicit Non-Claims

TS172 does not prove:

- the full TS166 Fourier identification;
- Plancherel;
- the Riemann-von Mangoldt explicit formula.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS172.TriangleSplineFourierBranchSplit
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS172
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
