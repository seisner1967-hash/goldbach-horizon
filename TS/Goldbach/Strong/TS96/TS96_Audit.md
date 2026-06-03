# TS96 - Spectral Trace Majorant Discharge

## Status

`repo_committed_relative`

TS96 assembles the spectral trace front. It proves that a concrete TS95
`ExplicitFormulaTraceBridgeLedger` supplies the TS92
`SpectralTraceMajorantContract` by using the TS95 rational trace budget as
`Ct_bound`.

TS96 does not prove the Riemann-von Mangoldt explicit formula and does not prove
a zeta-zero trace estimate. The analytic content remains the TS95 ledger.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS96/SpectralTraceMajorantDischarge.lean
```

Key declarations:

```lean
TS96.Goldbach.spectralTraceMajorantContract_of_explicitFormulaLedger
TS96.Goldbach.SpectralTraceMajorantDischargeTarget
TS96.Goldbach.spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
TS96.Goldbach.traceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
TS96.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_explicitFormulaTrace_mellin
TS96.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_explicitFormulaTrace_mellin
TS96.Goldbach.spectralTraceMajorantDischargeTarget_of_explicitFormulaTraceBridgeLedgerTarget
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS96.SpectralTraceMajorantDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS96
rg -n "a[x]iom" TS\Goldbach\Strong\TS96
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS96-A1 | `spectralTraceMajorantContract_of_explicitFormulaLedger` | `repo_committed_relative` | assembles TS93, TS94, and TS95 data into the TS92 spectral trace contract |
| TS96-P1 | `spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget` | `repo_committed_relative` | a TS95 bridge target supplies the TS92 spectral trace target |
| TS96-P2 | `traceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget` | `repo_committed_relative` | the TS95 bridge target supplies the TS32 trace contract target |
| TS96-P3 | `OTSAFinalMajorantAPIContractsTarget_of_explicitFormulaTrace_mellin` | `repo_committed_relative` | TS95 plus TS83 feeds the TS84 final majorant API route |
| TS96-P4 | `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_explicitFormulaTrace_mellin` | `repo_committed_relative` | Brun-Titchmarsh plus TS95 and TS83 feeds TS25 |

## Summary

TS96 freezes the `Ct <= 1/2` front at the architectural level: the remaining
mathematical work is exactly the TS95 explicit-formula ledger.
