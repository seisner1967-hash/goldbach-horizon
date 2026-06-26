# TS210 Audit - Box Convolution Triangle Evidence

## Scope

TS210 discharges the first concrete obligation in the TS167 convolution route:
the centered unit-width box convolved with itself is exactly the triangle
spline.

The sprint works with the manual Bochner convolution already defined in TS167:

```lean
integral volume
  (fun y => unitBoxAsComplex y * unitBoxAsComplex (x - y))
```

It evaluates this pointwise by computing the overlap of the two box supports.
For `x < -1` and `1 < x`, the integrand is identically zero.  For
`-1 <= x <= 0`, the overlap is `[-1/2, x + 1/2]` and has length `1 + x`.
For `0 <= x <= 1`, the overlap is `[x - 1/2, 1/2]` and has length `1 - x`.
The branch values are then matched with the TS56 affine branch formulae for
`TS42.MellinJackson.triangleSpline`, after coercion to complex values through
TS166.

## Main Declarations

- `TS210.Goldbach.unitBoxConvolutionIntegrand_eq_zero_of_lt_neg_one`
- `TS210.Goldbach.unitBoxConvolutionIntegrand_eq_zero_of_gt_one`
- `TS210.Goldbach.unitBoxConvolutionIntegrand_left`
- `TS210.Goldbach.unitBoxConvolutionIntegrand_right`
- `TS210.Goldbach.unitBoxSelfConvolution_eq_zero_of_lt_neg_one`
- `TS210.Goldbach.unitBoxSelfConvolution_eq_zero_of_gt_one`
- `TS210.Goldbach.unitBoxSelfConvolution_eq_one_add_of_left`
- `TS210.Goldbach.unitBoxSelfConvolution_eq_one_sub_of_right`
- `TS210.Goldbach.boxConvolutionEqualsTriangleSpline`
- `TS210.Goldbach.BoxConvolutionTriangleEvidenceLedger`
- `TS210.Goldbach.boxConvolutionTriangleEvidenceLedger`
- `TS210.Goldbach.BoxConvolutionTriangleEvidenceTarget`
- `TS210.Goldbach.boxConvolutionTriangleEvidenceTarget`

## What TS210 Proves

TS210 proves the TS167 spatial convolution statement:

```lean
TS167.Goldbach.BoxConvolutionEqualsTriangleSplineStatement
```

Equivalently, for every real `x`, the TS167 manual self-convolution of the
centered unit box equals `TS166.Goldbach.triangleSplineAsComplex x`.

The proof reduces the convolution integral to integrals of constant indicators
over compact intervals and uses `Real.volume_Icc` to compute the interval
lengths exactly.

## Non-Claims

TS210 does not evaluate the Fourier transform of the box.
TS210 does not prove Fourier-convolution exchange.
TS210 does not prove Plancherel.
TS210 does not prove the canonical sinc-fourth integral.
TS210 does not prove the explicit formula.
TS210 does not prove Gallagher or large-sieve bounds.
TS210 does not prove Goldbach.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS210\BoxConvolutionTriangleEvidence.lean
lake build TS.Goldbach.Strong.TS210.BoxConvolutionTriangleEvidence
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS210
git diff --check
git status --short
```
