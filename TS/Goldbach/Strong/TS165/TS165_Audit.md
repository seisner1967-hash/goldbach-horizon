# TS165 Audit - Triangle Spline Mathlib Fourier Scale Ledger

## Sprint Scope

TS165 calibrates the TS164 scale-parametrized squared-sinc family against the
current Mathlib Fourier API.

The sprint is deliberately a normalization ledger, not a Fourier-integral
calculation.  It records that Mathlib's real Fourier transform uses the
standard additive character with `2 * pi` in the exponent, and that the forward
real kernel is exposed through the theorem
`Real.fourierIntegral_real_eq_integral_exp_smul` with the negative
`2 * pi * v * w` exponent.

## Main Definitions

- `mathlibFourierTargetScale`
  - Defined as `Real.pi`.
  - This is the scale selected for the TS164 `scaledSincSq` family.

- `triangleSplineMathlibFourierWeight`
  - Defined as `TS164.Goldbach.scaledSincSq mathlibFourierTargetScale`.
  - Represents the future Mathlib-normalized squared-sinc spectral candidate.

- `TriangleSplineMathlibFourierScaleLedger`
  - Packages the TS53 concrete Fourier symbol probe.
  - Packages the TS164 normalization probe.
  - Selects the pi-scale TS164 contract.
  - Records the checked Mathlib `2 * pi` convention.
  - Keeps the triangle-spline Fourier identity, Plancherel, and explicit
    formula out of scope.

## Proved Facts

- `mathlibFourierTargetScale_pos`
  - Proves `0 < mathlibFourierTargetScale`.

- `triangleSplineMathlibFourierWeight_nonneg`
  - Proves pointwise nonnegativity of the selected pi-scale squared-sinc
    candidate.

- `triangleSplineMathlibFourierWeight_zero`
  - Proves zero-frequency normalization:
    `triangleSplineMathlibFourierWeight 0 = 1`.

- `mathlib_fourierChar_twoPi_checked`
  - References `Real.fourierChar_apply`, confirming the Mathlib additive
    character convention.

- `mathlib_forward_fourier_kernel_checked`
  - References `Real.fourierIntegral_real_eq_integral_exp_smul`, confirming
    the forward real Fourier kernel expansion available in Mathlib.

- `mathlibFourierTargetScale_two_mul_eq_derivativeMultiplierCandidate`
  - Connects the selected scale to the TS53 derivative multiplier:
    `2 * mathlibFourierTargetScale =
      TS53.MellinJackson.derivativeMultiplierCandidate`.

- `triangleSplineMathlibFourierScaleTarget`
  - Populates the TS165 target ledger.

## Explicit Non-Claims

TS165 does not prove:

- that the triangle spline Fourier transform equals the selected pi-scale
  squared-sinc weight;
- any Plancherel or L2 isometry theorem;
- any explicit formula or zeta-zero trace statement;
- any convergence theorem for spectral sums.

Those remain future obligations, now with the normalization risk localized to
the TS165 ledger.

## Verification

The sprint was checked with:

```bash
lake build TS.Goldbach.Strong.TS165.TriangleSplineMathlibFourierScaleLedger
rg -n "s[o]rry|a[x]iom|[^\\x00-\\x7F]" TS/Goldbach/Strong/TS165
git diff --check -- README.md TS/Goldbach/Strong/TS165
```

Expected result:

- build succeeds;
- no proof holes;
- no forbidden declaration escapes;
- no non-ASCII characters in TS165 source or audit;
- whitespace check clean.

## Status

`repo_committed`
