# TS87 - Farey Spacing Roadmap

## Status

`repo_committed_relative`

TS87 opens the Farey-spacing layer beneath the TS86 grand-sieve variance
roadmap. It defines a small rational-point API, isolates the Farey separation
inequality, and packages the covering/counting geometry needed by the future
large-sieve proof.

TS87 does not prove the classical Farey separation theorem, does not prove a
covering lemma, does not prove a counting lemma, and does not prove the dual
large sieve. Those remain explicit analytic and arithmetic infrastructure
obligations.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS87/FareySpacingRoadmap.lean
```

Key declarations:

```lean
TS87.Goldbach.FareyPoint
TS87.Goldbach.FareyPoint.value
TS87.Goldbach.FareyPoint.denBound
TS87.Goldbach.FareyPoint.valueDistinct
TS87.Goldbach.FareySeparationStatement
TS87.Goldbach.FareySeparationContract
TS87.Goldbach.FareyCoveringContract
TS87.Goldbach.FareyCountingContract
TS87.Goldbach.FareySpacingContract
TS87.Goldbach.FareySpacingRoadmap
TS87.Goldbach.fareySpacingInfrastructure_of_contract
TS87.Goldbach.FareySpacingRoadmapTarget
TS87.Goldbach.FareySeparationContractTarget
TS87.Goldbach.FareyCoveringContractTarget
TS87.Goldbach.FareyCountingContractTarget
TS87.Goldbach.FareySpacingContractTarget
TS87.Goldbach.fareySpacingRoadmapTarget
TS87.Goldbach.fareySpacingContractTarget_of_components
TS87.Goldbach.fareySpacingInfrastructureTarget_of_contractTarget
TS87.Goldbach.grandSieveVarianceInfrastructureTarget_of_fareyContract_dualLargeSieveTarget
TS87.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.paddedGallagherVarianceTransferContractTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.scaleTransferMajorantAPIContractsTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_farey_paddedDualLargeSieve
TS87.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
TS87.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS87.FareySpacingRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS87
rg -n "a[x]iom" TS\Goldbach\Strong\TS87
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS87-G1 | `FareySpacingRoadmap` | `repo_committed` | records the Farey-spacing proof layer below TS86 |
| TS87-C1 | `FareySeparationContract` | `analytic_infrastructure_obligation` | classical `1 / (q q')` separation for distinct rational points |
| TS87-C2 | `FareyCoveringContract` | `analytic_infrastructure_obligation` | covering geometry needed by the Gallagher/large-sieve transfer |
| TS87-C3 | `FareyCountingContract` | `analytic_infrastructure_obligation` | counting of selected rational points in Farey windows |
| TS87-C4 | `FareySpacingContract` | `analytic_infrastructure_obligation` | packages separation, covering, and counting |
| TS87-P1 | `fareySpacingInfrastructureTarget_of_contractTarget` | `repo_committed_relative` | Farey contract implies TS86 Farey infrastructure |
| TS87-P2 | `paddedGallagherVarianceTransferContractTarget_of_fareyContract_paddedDualLargeSieveTarget` | `repo_committed_relative` | Farey plus padded dual large sieve implies TS85 Gallagher |
| TS87-P3 | `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve` | `repo_committed_relative` | final contracts imply TS25 padded-scale infrastructure |

## Summary

TS87 pushes the scale-transfer front from the TS86 marker
`FareySpacingInfrastructure` down to concrete rational-point obligations. The
next arithmetic step is to discharge the separation, covering, or counting
contracts, or to continue downward into the dual large-sieve variance bound.
