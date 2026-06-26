# TS211 Audit - Box Fourier Evaluation

## Scope

TS211 proves the second concrete obligation in the TS167 convolution route:
the Mathlib Fourier transform of the centered unit box is the non-squared
pi-scaled sinc profile.

The proof is direct and local.  It expands `Real.fourierIntegral` using
Mathlib's real Fourier kernel, proves that the box integrand vanishes outside
`[-1/2, 1/2]`, converts the global integral to a directed interval integral,
and evaluates the zero and nonzero frequency cases separately.  The nonzero
case uses Mathlib's `integral_exp_mul_complex` and simplifies the endpoint
exponentials with `Complex.exp_mul_I`.

## Main Declarations

- `TS211.Goldbach.unitBoxFourierIntegrand`
- `TS211.Goldbach.unitBoxPureFourierIntegrand`
- `TS211.Goldbach.unitBoxFourier_eq_globalIntegral`
- `TS211.Goldbach.unitBoxFourier_globalIntegral_eq_intervalIntegral`
- `TS211.Goldbach.unitBoxFourier_eq_intervalIntegral`
- `TS211.Goldbach.unitBoxFourier_zero`
- `TS211.Goldbach.unitBoxPureFourier_intervalIntegral_nonzero`
- `TS211.Goldbach.unitBoxFourier_nonzero`
- `TS211.Goldbach.boxFourierEvaluation`
- `TS211.Goldbach.BoxFourierEvaluationLedger`
- `TS211.Goldbach.boxFourierEvaluationLedger`
- `TS211.Goldbach.BoxFourierEvaluationTarget`
- `TS211.Goldbach.boxFourierEvaluationTarget`

## What TS211 Proves

TS211 proves:

```lean
TS167.Goldbach.BoxFourierEvaluationStatement
```

Equivalently, for every real frequency `xi`,

```lean
Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
  (TS167.Goldbach.scaledSinc
    TS165.Goldbach.mathlibFourierTargetScale xi : Complex)
```

The zero-frequency case gives value `1`; the nonzero case gives
`sin (pi * xi) / (pi * xi)` after the exact finite-interval exponential
integral calculation.

## Non-Claims

TS211 does not prove:

- the Fourier-convolution exchange for the box self-convolution;
- Plancherel or Parseval;
- the canonical `sinc^4` integral;
- the Riemann-von Mangoldt explicit formula;
- Gallagher or large-sieve comparison;
- Goldbach.

## Verification Commands

```text
lake env lean TS\Goldbach\Strong\TS211\BoxFourierEvaluation.lean
lake build TS.Goldbach.Strong.TS211.BoxFourierEvaluation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS211
git diff --check
git status --short
```
