# TS162 Audit - Triangle Spline Trace Kernel Instantiation

## Status

TS162 instantiates the TS94 trace-kernel ledger with the concrete triangle
spline introduced in TS42.

Status: `repo_committed`.

## What TS162 Proves

The sprint proves the elementary real-kernel facts needed to package the
triangle spline as a TS94 kernel:

- `triangleSpline_nonneg`:
  `0 <= TS42.MellinJackson.triangleSpline x` for every real `x`;
- `triangleSpline_zero`:
  `TS42.MellinJackson.triangleSpline 0 = 1`;
- `triangleSpline_eq_zero_of_one_le_abs`:
  the spline vanishes whenever `1 <= |x|`;
- `triangleSplineTraceKernel`:
  the TS94 `TraceKernel` whose real kernel is the triangle spline and whose
  placeholder spectral weight is identically zero;
- `triangleSplineTraceKernelSpectralDataLedger`:
  a concrete TS94 `TraceKernelSpectralDataLedger`;
- `triangleSplineTraceKernelSpectralDataTarget`:
  the corresponding TS94 target;
- `triangleSplineTraceKernelInstantiationLedger`:
  a TS162 ledger keeping the TS161 phi pre-mortem in scope, installing the
  triangle spline kernel, and leaving TS95 as the next analytic front.

## What TS162 Does Not Prove

TS162 does not prove:

- Plancherel;
- a nontrivial Fourier transform for the triangle spline;
- a zeta-zero sum convergence theorem;
- the Riemann-von Mangoldt explicit formula;
- the TS95 concrete explicit-formula ledger.

Those are deliberately left as future analytic obligations.

## Lean Files

- `TriangleSplineTraceKernelInstantiation.lean`

## Key Declarations

```lean
TS162.Goldbach.triangleSpline_nonneg
TS162.Goldbach.triangleSpline_zero
TS162.Goldbach.triangleSpline_eq_zero_of_one_le_abs
TS162.Goldbach.triangleSplineTraceKernel
TS162.Goldbach.triangleSplineTraceKernelSpectralDataLedger
TS162.Goldbach.triangleSplineTraceKernelSpectralDataTarget
TS162.Goldbach.TriangleSplineTraceKernelInstantiationLedger
TS162.Goldbach.triangleSplineTraceKernelInstantiationLedger
TS162.Goldbach.TriangleSplineTraceKernelInstantiationTarget
TS162.Goldbach.triangleSplineTraceKernelInstantiationTarget
```

## Verification

```powershell
lake build TS.Goldbach.Strong.TS162.TriangleSplineTraceKernelInstantiation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS162
git diff --check -- README.md TS\Goldbach\Strong\TS162
```

Expected result: build succeeds; no `s[o]rry`, no `a[x]iom`, no non-ASCII in
TS162; whitespace check is clean.

## Interpretation

TS162 is the first concrete post-TS161 spectral-pivot sprint.  It does not
attempt to solve the explicit-formula side.  It simply turns the dormant
triangle-spline real-analysis work into a concrete TS94 kernel-data object,
ready for a later Fourier/Plancherel reality probe.
