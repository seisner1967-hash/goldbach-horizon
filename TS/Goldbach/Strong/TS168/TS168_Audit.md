# TS168 Audit - Triangle Spline Branch Integral Route Probe

## Sprint Scope

TS168 records the fallback route selected in TS166: compute the Fourier
integral of the triangle spline by splitting it into the two affine branches
`[-1, 0]` and `[0, 1]`.

The sprint is a probe.  It defines the branch functions, the Mathlib-compatible
forward Fourier kernel, the two directed interval integrals, and the intended
closed-form targets.  It then proves that the branch split, the two branch
evaluations, and the closed-form recombination imply the exact TS166 Fourier
identification statement.

## Main Declarations

- `TS168.Goldbach.BranchIntegralRouteStatus`
- `TS168.Goldbach.leftTriangleSplineBranchAsComplex`
- `TS168.Goldbach.rightTriangleSplineBranchAsComplex`
- `TS168.Goldbach.mathlibForwardFourierKernel`
- `TS168.Goldbach.leftBranchFourierIntegrand`
- `TS168.Goldbach.rightBranchFourierIntegrand`
- `TS168.Goldbach.leftBranchFourierIntegral`
- `TS168.Goldbach.rightBranchFourierIntegral`
- `TS168.Goldbach.branchAngularFrequency`
- `TS168.Goldbach.leftBranchClosedForm`
- `TS168.Goldbach.rightBranchClosedForm`
- `TS168.Goldbach.BranchSplitFourierStatement`
- `TS168.Goldbach.LeftBranchIntegralEvaluationStatement`
- `TS168.Goldbach.RightBranchIntegralEvaluationStatement`
- `TS168.Goldbach.BranchClosedFormRecombinationStatement`
- `TS168.Goldbach.BranchIntegralRouteImpliesTS166Statement`
- `TS168.Goldbach.branchIntegralRoute_implies_ts166`
- `TS168.Goldbach.TriangleSplineBranchIntegralRouteProbeLedger`
- `TS168.Goldbach.triangleSplineBranchIntegralRouteProbeLedger`
- `TS168.Goldbach.TriangleSplineBranchIntegralRouteProbeTarget`
- `TS168.Goldbach.triangleSplineBranchIntegralRouteProbeTarget`

## What Is Proved

TS168 proves the logical wiring of the fallback route:

```lean
BranchSplitFourierStatement ->
  LeftBranchIntegralEvaluationStatement ->
    RightBranchIntegralEvaluationStatement ->
      BranchClosedFormRecombinationStatement ->
        TS166.Goldbach.TriangleSplineFourierIdentificationStatement
```

This theorem is the direct analogue of TS167's convolution-route wiring theorem.

## What Is Only Stated

The following are compiled as real `Prop` statements but not proved:

- the global Fourier integral splits into the left and right branch integrals;
- the left branch interval integral equals its closed form;
- the right branch interval integral equals its closed form;
- the two closed forms recombine into the TS166 squared-sinc candidate.

## Explicit Non-Claims

TS168 does not prove:

- branch splitting of the Fourier integral;
- either branch integral evaluation;
- closed-form recombination;
- the TS166 Fourier identification;
- Plancherel;
- the Riemann-von Mangoldt explicit formula.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS168.TriangleSplineBranchIntegralRouteProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS168
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
