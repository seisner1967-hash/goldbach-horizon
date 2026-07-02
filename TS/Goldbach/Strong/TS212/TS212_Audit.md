# TS212 Audit - Box Fourier Convolution Exchange

## Scope

TS212 proves the third local obligation in the TS167 convolution route:
the Fourier transform of the centered-box self-convolution is the square of
the Fourier transform of the centered box.

The proof is specialized to the centered unit box.  It does not use or prove a
general Fourier-convolution theorem.  Instead, it compares both sides with
already-proved closed forms:

- TS210 identifies the manual box self-convolution with the triangle spline.
- TS173 evaluates the Fourier transform of the triangle spline as the
  pi-scaled squared-sinc profile.
- TS211 evaluates the Fourier transform of the box as the pi-scaled sinc.
- TS167 proves that the square of the sinc profile is the squared-sinc profile.

This closes the full TS167 convolution route to the TS166 triangle-spline
Fourier identification, while leaving Plancherel and the `sinc^4` integral
open.

## Main Declarations

- `TS212.Goldbach.BoxFourierConvolutionExchangeTarget`
- `TS212.Goldbach.boxFourierConvolutionExchange`
- `TS212.Goldbach.triangleSplineFourierIdentification_via_boxRoute`
- `TS212.Goldbach.BoxFourierConvolutionExchangeLedger`
- `TS212.Goldbach.boxFourierConvolutionExchangeLedger`
- `TS212.Goldbach.BoxFourierConvolutionExchangeLedgerTarget`
- `TS212.Goldbach.boxFourierConvolutionExchangeLedgerTarget`

## What TS212 Proves

TS212 proves:

```lean
TS167.Goldbach.BoxFourierConvolutionExchangeStatement
```

That is, for every real frequency `xi`,

```lean
Real.fourierIntegral TS167.Goldbach.unitBoxSelfConvolution xi =
  Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi *
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi
```

It also proves that the TS167 convolution route now supplies:

```lean
TS166.Goldbach.TriangleSplineFourierIdentificationStatement
```

using TS210, TS211, and the TS212 exchange statement.

## Non-Claims

TS212 does not prove:

- a general Fourier-convolution theorem;
- Plancherel or Parseval;
- the canonical `sinc^4` integral;
- the Riemann-von Mangoldt explicit formula;
- Gallagher or large-sieve comparison;
- Goldbach.

## Verification Commands

```text
lake env lean TS\Goldbach\Strong\TS212\BoxFourierConvolutionExchange.lean
lake build TS.Goldbach.Strong.TS212.BoxFourierConvolutionExchange
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS212
git diff --check
git status --short
```
