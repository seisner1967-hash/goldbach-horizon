# TS163 Audit - Triangle Spline Fourier Weight Ledger

## Status

TS163 replaces the TS162 zero spectral-weight placeholder by a natural
nonnegative squared-sinc candidate while keeping the Fourier theorem itself as
an explicit future obligation.

Status: `repo_committed`.

## What TS163 Proves

The sprint defines

```lean
triangleSplineFourierWeight xi =
  if xi = 0 then 1 else (Real.sin xi / xi) ^ 2
```

and proves:

- `triangleSplineFourierWeight_nonneg`:
  the candidate is nonnegative on real frequencies;
- `triangleSplineFourierWeight_zero`:
  the candidate is normalized to `1` at frequency `0`;
- `triangleSplineSpectralWeight_nonneg`:
  the lifted complex-parameter weight is nonnegative;
- `triangleSplineFourierTraceKernel`:
  a TS94 trace kernel using the TS42 triangle spline and the sinc-square
  spectral-weight candidate;
- `triangleSplineFourierTraceKernelSpectralDataLedger`:
  a concrete TS94 kernel-data ledger with a nonzero spectral-weight candidate;
- `triangleSplineFourierWeightLedger`:
  a TS163 ledger recording the remaining Fourier-identification, Plancherel,
  and explicit-formula obligations.

## What TS163 Does Not Prove

TS163 does not prove:

- that the squared-sinc candidate is the actual Mathlib Fourier transform of
  the triangle spline;
- Plancherel;
- decay estimates for the true transform;
- convergence of zeta-zero sums;
- the Riemann-von Mangoldt explicit formula;
- a concrete TS95 explicit-formula ledger.

## Lean Files

- `TriangleSplineFourierWeightLedger.lean`

## Key Declarations

```lean
TS163.Goldbach.triangleSplineFourierWeight
TS163.Goldbach.triangleSplineFourierWeight_nonneg
TS163.Goldbach.triangleSplineFourierWeight_zero
TS163.Goldbach.triangleSplineSpectralWeight
TS163.Goldbach.triangleSplineSpectralWeight_nonneg
TS163.Goldbach.triangleSplineFourierTraceKernel
TS163.Goldbach.triangleSplineFourierTraceKernelSpectralDataLedger
TS163.Goldbach.triangleSplineFourierTraceKernelSpectralDataTarget
TS163.Goldbach.TriangleSplineFourierWeightLedger
TS163.Goldbach.triangleSplineFourierWeightLedger
TS163.Goldbach.TriangleSplineFourierWeightTarget
TS163.Goldbach.triangleSplineFourierWeightTarget
```

## Verification

```powershell
lake build TS.Goldbach.Strong.TS163.TriangleSplineFourierWeightLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS163
git diff --check -- README.md TS\Goldbach\Strong\TS163
```

Expected result: build succeeds; no `s[o]rry`, no `a[x]iom`, no non-ASCII in
TS163; whitespace check is clean.

## Interpretation

TS163 makes the spectral side nontrivial without overclaiming.  TS162 installed
the real trace kernel.  TS163 installs a nonnegative candidate spectral weight.
The next sprint can now probe the actual Mathlib Fourier API and decide which
normalization constants are needed to identify the candidate with the true
Fourier transform of the triangle spline.
