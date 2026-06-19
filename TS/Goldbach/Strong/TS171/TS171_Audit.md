# TS171 Audit - Triangle Spline Left Branch Integral Evaluation

## Sprint Scope

TS171 discharges the left analytic obligation in the TS168 fallback branch
route: the left branch integral over `[-1,0]`.

This sprint proves only
`TS168.Goldbach.LeftBranchIntegralEvaluationStatement`.  It deliberately does
not prove the global branch split, the full TS166 Fourier identification,
Plancherel, or the explicit formula.

## Main Declarations

- `TS171.Goldbach.leftBranchA`
- `TS171.Goldbach.leftBranchPrimitive`
- `TS171.Goldbach.leftBranchAffine_hasDerivAt`
- `TS171.Goldbach.leftBranchPrimitive_hasDerivAt`
- `TS171.Goldbach.leftBranchPrimitive_intervalIntegral`
- `TS171.Goldbach.leftBranchAffineIntegral_zero`
- `TS171.Goldbach.leftBranchFourierIntegral_zero`
- `TS171.Goldbach.leftBranchA_ne_zero`
- `TS171.Goldbach.leftBranchFourierIntegral_eq_primitiveIntegral`
- `TS171.Goldbach.leftBranchPrimitive_value_eq_closedForm`
- `TS171.Goldbach.leftBranchIntegralEvaluation`
- `TS171.Goldbach.TriangleSplineLeftBranchIntegralEvaluationLedger`
- `TS171.Goldbach.triangleSplineLeftBranchIntegralEvaluationLedger`
- `TS171.Goldbach.TriangleSplineLeftBranchIntegralEvaluationTarget`
- `TS171.Goldbach.triangleSplineLeftBranchIntegralEvaluationTarget`

## What Is Proved

TS171 proves:

```lean
TS168.Goldbach.LeftBranchIntegralEvaluationStatement
```

That is, for every `xi : Real`,

```lean
leftBranchFourierIntegral xi = leftBranchClosedForm xi
```

The proof mirrors TS170.  At zero frequency it reduces the integral to the
elementary affine integral of `1 + x` over `[-1,0]`.  Away from zero frequency
it introduces an explicit complex primitive, proves its derivative, applies the
interval-integral fundamental theorem of calculus, and normalizes the endpoint
value to the TS168 left closed form.

## Explicit Non-Claims

TS171 does not prove:

- the branch split of the Fourier integral;
- the full TS166 Fourier identification;
- Plancherel;
- the Riemann-von Mangoldt explicit formula.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS171.TriangleSplineLeftBranchIntegralEvaluation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS171
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
