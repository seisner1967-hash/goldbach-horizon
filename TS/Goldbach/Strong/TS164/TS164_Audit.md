# TS164 Audit - Triangle Spline Fourier Normalization Probe

## Status

TS164 introduces a scale-parametrized squared-sinc family to prevent the TS163
unit-scale candidate from becoming an accidental Fourier-normalization claim.

Status: `repo_committed`.

## What TS164 Proves

The sprint defines

```lean
scaledSincSq scale xi =
  if scale * xi = 0 then 1
  else (Real.sin (scale * xi) / (scale * xi)) ^ 2
```

and proves:

- `scaledSincSq_nonneg`:
  every scaled candidate is nonnegative;
- `scaledSincSq_zero`:
  every scaled candidate is normalized to `1` at frequency `0`;
- `scaledSincSq_one_eq_triangleSplineFourierWeight`:
  the TS163 candidate is exactly the unit-scale member of the family;
- `scaledTriangleSplineSpectralWeight_nonneg`:
  the complex-parameter lift is nonnegative;
- `scaledTriangleSplineTraceKernelSpectralDataLedger`:
  every scale gives a TS94 trace-kernel ledger;
- `triangleSplineFourierIdentificationContract`:
  every positive scale gives a fail-closed identification contract;
- `triangleSplineFourierNormalizationProbeLedger`:
  the unit-scale TS163 convention is recorded as one option, not as the chosen
  Mathlib normalization.

## What TS164 Does Not Prove

TS164 does not:

- select the correct Fourier normalization constant;
- prove the Mathlib `Real.fourierIntegral` identity;
- prove Plancherel;
- prove decay estimates;
- prove zeta-zero sum convergence;
- instantiate the TS95 explicit-formula ledger.

## Lean Files

- `TriangleSplineFourierNormalizationProbe.lean`

## Key Declarations

```lean
TS164.Goldbach.scaledSincSq
TS164.Goldbach.scaledSincSq_nonneg
TS164.Goldbach.scaledSincSq_zero
TS164.Goldbach.scaledSincSq_one_eq_triangleSplineFourierWeight
TS164.Goldbach.scaledTriangleSplineSpectralWeight
TS164.Goldbach.scaledTriangleSplineTraceKernel
TS164.Goldbach.scaledTriangleSplineTraceKernelSpectralDataLedger
TS164.Goldbach.TriangleSplineFourierIdentificationContract
TS164.Goldbach.triangleSplineFourierIdentificationContract
TS164.Goldbach.TriangleSplineFourierNormalizationProbeLedger
TS164.Goldbach.triangleSplineFourierNormalizationProbeLedger
TS164.Goldbach.TriangleSplineFourierNormalizationProbeTarget
TS164.Goldbach.triangleSplineFourierNormalizationProbeTarget
```

## Verification

```powershell
lake build TS.Goldbach.Strong.TS164.TriangleSplineFourierNormalizationProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS164
git diff --check -- README.md TS\Goldbach\Strong\TS164
```

Expected result: build succeeds; no `s[o]rry`, no `a[x]iom`, no non-ASCII in
TS164; whitespace check is clean.

## Interpretation

TS164 is a normalization firewall.  It preserves the useful positivity and
zero-frequency normalization of TS163, but prevents the unit-scale `sinc^2`
candidate from being silently treated as the true Mathlib Fourier transform of
the triangle spline.
