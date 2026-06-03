# TS92 - Spectral Trace Roadmap

## Status

`repo_committed_relative`

TS92 opens the spectral trace front for `Ct <= 1/2`. It does not prove a
zeta-zero estimate or an explicit-formula trace bound. Instead, it records the
local analytic contract whose future discharge would supply the TS32
`TraceMajorantContract`.

The scale-transfer side is already supplied by TS91 in the current API, so
TS92 proves mechanical bridges from the spectral trace contract plus the TS83
Mellin-tail final contracts to the TS84/TS25 assembly targets.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS92/SpectralTraceRoadmap.lean
```

Key declarations:

```lean
TS92.Goldbach.TraceKernelSpectralData
TS92.Goldbach.ZetaZeroFamily
TS92.Goldbach.ExplicitFormulaTraceBridge
TS92.Goldbach.SpectralTraceRoadmap
TS92.Goldbach.spectralTraceRoadmap
TS92.Goldbach.SpectralTraceMajorantContract
TS92.Goldbach.traceMajorantContract_of_spectralTrace
TS92.Goldbach.SpectralTraceRoadmapTarget
TS92.Goldbach.SpectralTraceMajorantContractTarget
TS92.Goldbach.spectralTraceRoadmapTarget
TS92.Goldbach.traceMajorantContractTarget_of_spectralTraceTarget
TS92.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_spectralTrace_mellin
TS92.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_spectralTrace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS92.SpectralTraceRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS92
rg -n "a[x]iom" TS\Goldbach\Strong\TS92
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS92-R1 | `TraceKernelSpectralData` | `analytic_infrastructure_obligation` | kernel normalization, positivity, and decay data for the trace front |
| TS92-R2 | `ZetaZeroFamily` | `analytic_infrastructure_obligation` | zeta-zero family, multiplicity, and symmetry bookkeeping |
| TS92-R3 | `ExplicitFormulaTraceBridge` | `analytic_infrastructure_obligation` | bridge from explicit formula to the trace sum and residual errors |
| TS92-C1 | `SpectralTraceMajorantContract` | `analytic_infrastructure_obligation` | local spectral contract carrying `Ct_bound <= 1/2` |
| TS92-P1 | `traceMajorantContractTarget_of_spectralTraceTarget` | `repo_committed_relative` | a spectral trace target supplies the TS32 trace target |
| TS92-P2 | `OTSAFinalMajorantAPIContractsTarget_of_spectralTrace_mellin` | `repo_committed_relative` | spectral trace plus Mellin-tail final contracts feed TS84 via TS91 |

## Summary

TS92 does for the `Ct` front what TS83 did for `Cm`: it names the exact final
analytic package needed by the OTSA route, without pretending that the
zeta-zero trace estimate has already been proved.
