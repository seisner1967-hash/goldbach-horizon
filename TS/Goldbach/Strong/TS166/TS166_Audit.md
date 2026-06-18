# TS166 Audit - Triangle Spline Fourier Identification Reduction

## Sprint Scope

TS166 fixes the exact Lean statement for the future Fourier identification of
the TS42 triangle spline with the TS165 Mathlib-scaled squared-sinc candidate.

The sprint is a reduction ledger only.  It verifies that the Fourier statement
is well-typed with Mathlib's `Real.fourierIntegral`, complex coercions, and the
selected `Real.pi` scale from TS165, but it does not prove that statement.

## Main Declarations

- `TS166.Goldbach.FourierIdentificationRoute`
- `TS166.Goldbach.triangleSplineAsComplex`
- `TS166.Goldbach.triangleSplineMathlibFourier`
- `TS166.Goldbach.triangleSplineScaledSincCandidate`
- `TS166.Goldbach.TriangleSplineFourierIdentificationStatement`
- `TS166.Goldbach.TriangleSplineFourierIdentificationReductionLedger`
- `TS166.Goldbach.triangleSplineFourierIdentificationReductionLedger`
- `TS166.Goldbach.TriangleSplineFourierIdentificationReductionTarget`
- `TS166.Goldbach.triangleSplineFourierIdentificationReductionTarget`

## What Is Proved

TS166 proves that the reduction ledger is inhabited.

More importantly, it compiles the future pointwise Fourier statement:

```lean
forall xi : Real,
  triangleSplineMathlibFourier xi =
    triangleSplineScaledSincCandidate xi
```

This forces Lean to check:

- `Real.fourierIntegral` accepts the complex-valued triangle spline;
- the Fourier output is `Complex`;
- `TS164.Goldbach.scaledSincSq` at the TS165 target scale coerces to `Complex`;
- the TS165 selected scale is available as
  `TS165.Goldbach.mathlibFourierTargetScale`.

## Explicit Non-Claims

TS166 does not prove:

- the triangle-spline Fourier identity;
- Plancherel;
- any norm identity;
- any zeta-zero sum convergence;
- the Riemann-von Mangoldt explicit formula;
- that the convolution route or branch-integral route is already available in
  Mathlib.

## Planned Proof Routes

The primary route is `convolutionBoxSquare`: represent the triangle spline as a
box convolution and use a future Fourier-convolution theorem.

The fallback route is `piecewiseBranchIntegration`: integrate the affine pieces
on `[-1,0]` and `[0,1]` directly.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS166.TriangleSplineFourierIdentificationReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS166
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
