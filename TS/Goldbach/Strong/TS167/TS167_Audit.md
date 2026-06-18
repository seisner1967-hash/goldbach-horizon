# TS167 Audit - Triangle Spline Convolution Route Probe

## Sprint Scope

TS167 probes the primary proof route selected by TS166: represent the triangle
spline as the self-convolution of a centered unit-width box, compute the box
Fourier transform as a non-squared sinc, and use Fourier-convolution exchange
to obtain the TS166 squared-sinc target.

The sprint is still a probe.  It defines the objects and compiles the exact
local statements, but does not prove the analytic convolution or Fourier facts.

## Main Declarations

- `TS167.Goldbach.ConvolutionRouteStatus`
- `TS167.Goldbach.unitBoxFunction`
- `TS167.Goldbach.unitBoxAsComplex`
- `TS167.Goldbach.scaledSinc`
- `TS167.Goldbach.scaledSinc_mul_self_eq_scaledSincSq`
- `TS167.Goldbach.unitBoxSelfConvolution`
- `TS167.Goldbach.BoxConvolutionEqualsTriangleSplineStatement`
- `TS167.Goldbach.BoxFourierEvaluationStatement`
- `TS167.Goldbach.BoxFourierConvolutionExchangeStatement`
- `TS167.Goldbach.ConvolutionRouteImpliesTS166Statement`
- `TS167.Goldbach.convolutionRoute_implies_ts166`
- `TS167.Goldbach.TriangleSplineConvolutionRouteProbeLedger`
- `TS167.Goldbach.triangleSplineConvolutionRouteProbeLedger`
- `TS167.Goldbach.TriangleSplineConvolutionRouteProbeTarget`
- `TS167.Goldbach.triangleSplineConvolutionRouteProbeTarget`

## What Is Proved

TS167 proves the algebraic wiring of the route:

```lean
BoxConvolutionEqualsTriangleSplineStatement ->
  BoxFourierEvaluationStatement ->
    BoxFourierConvolutionExchangeStatement ->
      TS166.Goldbach.TriangleSplineFourierIdentificationStatement
```

It also proves that the square of the non-squared scaled sinc is the TS164
`scaledSincSq` profile at the same scale.

## What Is Only Stated

The following are compiled as real `Prop` statements but not proved:

- the box self-convolution equals the complexified triangle spline;
- Mathlib's Fourier transform of the box equals the non-squared scaled sinc;
- Mathlib's Fourier transform exchanges this self-convolution for pointwise
  multiplication of box transforms.

## Explicit Non-Claims

TS167 does not prove:

- box integrability;
- the spatial convolution identity;
- the box Fourier evaluation;
- the Fourier-convolution exchange theorem;
- the TS166 Fourier identification;
- Plancherel;
- the Riemann-von Mangoldt explicit formula.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS167.TriangleSplineConvolutionRouteProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS167
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
