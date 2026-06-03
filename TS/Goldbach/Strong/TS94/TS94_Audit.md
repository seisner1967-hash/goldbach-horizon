# TS94 - Trace Kernel Spectral Data Ledger

## Status

`repo_committed_relative`

TS94 refines the `TraceKernelSpectralData` component introduced in TS92. It
does not choose a concrete trace kernel and does not prove any spectral trace
estimate. Instead, it records the local kernel-side facts that a future
explicit-formula trace proof must provide.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS94/TraceKernelSpectralDataLedger.lean
```

Key declarations:

```lean
TS94.Goldbach.TraceKernel
TS94.Goldbach.TraceKernel.Normalization
TS94.Goldbach.TraceKernel.Decay
TS94.Goldbach.TraceKernel.SpectralSumConvergence
TS94.Goldbach.TraceKernelSpectralDataLedger
TS94.Goldbach.TraceKernelSpectralDataRoadmap
TS94.Goldbach.traceKernelSpectralDataRoadmap
TS94.Goldbach.traceKernelSpectralData_of_ledger
TS94.Goldbach.TraceKernelSpectralDataRoadmapTarget
TS94.Goldbach.TraceKernelSpectralDataLedgerTarget
TS94.Goldbach.TraceKernelSpectralDataTarget
TS94.Goldbach.traceKernelSpectralDataRoadmapTarget
TS94.Goldbach.traceKernelSpectralDataTarget_of_ledgerTarget
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS94.TraceKernelSpectralDataLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS94
rg -n "a[x]iom" TS\Goldbach\Strong\TS94
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS94-K1 | `TraceKernel` | `repo_committed_relative` | real trace kernel plus spectral weight function |
| TS94-K2 | `TraceKernel.Normalization` | `analytic_infrastructure_obligation` | normalization statement expected of the future concrete kernel |
| TS94-K3 | `TraceKernel.Decay` | `analytic_infrastructure_obligation` | decay statement expected of the future concrete kernel |
| TS94-K4 | `TraceKernel.SpectralSumConvergence` | `analytic_infrastructure_obligation` | convergence statement for the zero sum induced by the kernel |
| TS94-C1 | `TraceKernelSpectralDataLedger` | `analytic_infrastructure_obligation` | kernel nonnegativity, spectral-weight nonnegativity, normalization, decay, and convergence |
| TS94-P1 | `traceKernelSpectralDataTarget_of_ledgerTarget` | `repo_committed_relative` | a concrete kernel ledger supplies the TS92 kernel-data marker |

## Summary

TS94 names the kernel-side vocabulary needed by the future `Ct <= 1/2` trace
estimate while keeping the analytic theorem itself external and explicit.
