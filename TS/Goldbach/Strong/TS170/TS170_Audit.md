# TS170 Audit - Triangle Spline Right Branch Integral Evaluation

## Sprint Scope

TS170 discharges one analytic obligation in the TS168 fallback branch route:
the right branch integral over `[0,1]`.

This sprint proves only
`TS168.Goldbach.RightBranchIntegralEvaluationStatement`.  It deliberately does
not prove the left branch integral, the global branch split, the full TS166
Fourier identification, Plancherel, or the explicit formula.

## Main Declarations

- `TS170.Goldbach.rightBranchA`
- `TS170.Goldbach.rightBranchPrimitive`
- `TS170.Goldbach.rightBranchAffine_hasDerivAt`
- `TS170.Goldbach.rightBranchPrimitive_hasDerivAt`
- `TS170.Goldbach.rightBranchPrimitive_intervalIntegral`
- `TS170.Goldbach.rightBranchAffineIntegral_zero`
- `TS170.Goldbach.rightBranchFourierIntegral_zero`
- `TS170.Goldbach.branchAngularFrequency_ne_zero`
- `TS170.Goldbach.rightBranchA_ne_zero`
- `TS170.Goldbach.rightBranchFourierIntegral_eq_primitiveIntegral`
- `TS170.Goldbach.rightBranchPrimitive_value_eq_closedForm`
- `TS170.Goldbach.rightBranchIntegralEvaluation`
- `TS170.Goldbach.TriangleSplineRightBranchIntegralEvaluationLedger`
- `TS170.Goldbach.triangleSplineRightBranchIntegralEvaluationLedger`
- `TS170.Goldbach.TriangleSplineRightBranchIntegralEvaluationTarget`
- `TS170.Goldbach.triangleSplineRightBranchIntegralEvaluationTarget`

## What Is Proved

TS170 proves:

```lean
TS168.Goldbach.RightBranchIntegralEvaluationStatement
```

That is, for every `xi : Real`,

```lean
rightBranchFourierIntegral xi = rightBranchClosedForm xi
```

The proof splits the zero-frequency case from the nonzero-frequency case.  At
zero frequency it reduces the integral to the elementary affine integral of
`1 - x` over `[0,1]`.  Away from zero frequency it introduces an explicit
complex primitive, proves its derivative, applies the interval-integral
fundamental theorem of calculus, and normalizes the endpoint value to the TS168
right closed form.

## Explicit Non-Claims

TS170 does not prove:

- the branch split of the Fourier integral;
- the left branch integral evaluation;
- the full TS166 Fourier identification;
- Plancherel;
- the Riemann-von Mangoldt explicit formula.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS170.TriangleSplineRightBranchIntegralEvaluation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS170
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
