# TS90 - Farey Covering Proof

## Status

`repo_committed`

TS90 discharges the TS87 Farey covering target for the current TS87 interface.
That interface is intentionally a marker:

```lean
structure FareyCoveringContract where
  covering_ready : True
```

TS90 therefore proves exactly the contract currently present in the repository.
It does not claim a formal Dirichlet approximation theorem or a concrete
interval-covering lemma.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS90/FareyCoveringProof.lean
```

Key declarations:

```lean
TS90.Goldbach.fareyCoveringContract
TS90.Goldbach.fareyCoveringContractTarget
TS90.Goldbach.FareyCoveringProofTarget
TS90.Goldbach.fareyCoveringProofTarget
TS90.Goldbach.fareySpacingContractTarget
TS90.Goldbach.fareySpacingInfrastructureTarget
TS90.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_paddedDualLargeSieveTarget
TS90.Goldbach.paddedGallagherVarianceTransferContractTarget_of_paddedDualLargeSieveTarget
TS90.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedDualLargeSieveTarget
TS90.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedDualLargeSieve
TS90.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedDualLargeSieve
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS90.FareyCoveringProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS90
rg -n "a[x]iom" TS\Goldbach\Strong\TS90
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS90-P1 | `fareyCoveringContract` | `repo_committed` | fills the current TS87 covering marker |
| TS90-P2 | `fareyCoveringContractTarget` | `repo_committed` | discharges the TS87 covering target |
| TS90-P3 | `fareySpacingContractTarget` | `repo_committed` | combines TS88 separation, TS89 counting, and TS90 covering |
| TS90-P4 | `fareySpacingInfrastructureTarget` | `repo_committed` | discharges the TS86 Farey-spacing infrastructure marker |
| TS90-P5 | `scaleTransferMajorantAPIContractsTarget_of_paddedDualLargeSieveTarget` | `repo_committed_relative` | after the Farey layer, the padded dual large-sieve target feeds TS84 |

## Summary

TS90 closes the current Farey-side geometric package exposed by TS87. The
remaining scale-transfer input is the analytic `DualLargeSieveVarianceBound`
at the TS24 padded scale; stronger future versions may replace the marker
covering field with a concrete Dirichlet/Farey covering statement.
