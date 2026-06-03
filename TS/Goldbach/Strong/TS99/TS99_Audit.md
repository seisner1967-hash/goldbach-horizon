# TS99 - Selberg Sieve Weight Ledger

## Status

`repo_committed_relative`

TS99 opens the Selberg-weight layer below the TS97 final Brun-Titchmarsh input.
It records the finite weight data and the local Selberg obligations needed to
recover the TS30 Selberg Brun-Titchmarsh infrastructure.

TS99 does not prove Selberg's sieve, Brun-Titchmarsh, Mobius inversion,
quadratic-form diagonalization, or a prime-count estimate.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS99/SelbergSieveWeightLedger.lean
```

Key declarations:

```lean
TS99.Goldbach.SelbergSieveWeightRoadmap
TS99.Goldbach.selbergSieveWeightRoadmap
TS99.Goldbach.SelbergSieveWeightLedger
TS99.Goldbach.SelbergSieveWeightInfrastructure
TS99.Goldbach.SelbergSieveWeightRoadmapTarget
TS99.Goldbach.SelbergSieveWeightLedgerTarget
TS99.Goldbach.SelbergSieveWeightInfrastructureTarget
TS99.Goldbach.selbergSieveWeightRoadmapTarget
TS99.Goldbach.selbergBrunTitchmarshInfrastructure_of_weightInfrastructure
TS99.Goldbach.brunTitchmarshFinalInputLedger_of_weightInfrastructure
TS99.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_weightInfrastructureTarget
TS99.Goldbach.finalHorizonInputsTarget_of_selbergWeight_trace_mellin
TS99.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergWeight_trace_mellin
TS99.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergWeight_trace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS99.SelbergSieveWeightLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS99
rg -n "a[x]iom" TS\Goldbach\Strong\TS99
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS99-R1 | `SelbergSieveWeightRoadmap` | `repo_committed` | records the Selberg-weight layer to be formalized |
| TS99-A1 | `SelbergSieveWeightLedger` | `repo_committed_relative` | records finite Selberg weight data and normalization |
| TS99-A2 | `SelbergSieveWeightInfrastructure` | `repo_committed_relative` | packages weights with the TS30 sieve and budget obligations |
| TS99-P1 | `selbergBrunTitchmarshInfrastructure_of_weightInfrastructure` | `repo_committed_relative` | weights infrastructure supplies TS30 Selberg BT infrastructure |
| TS99-P2 | `brunTitchmarshFinalInputLedgerTarget_of_weightInfrastructureTarget` | `repo_committed_relative` | weights infrastructure supplies the TS97 final BT input target |
| TS99-P3 | `paddedScaleAnalyticInfrastructureTarget_of_selbergWeight_trace_mellin` | `repo_committed_relative` | Selberg weights plus TS95 and TS83 feed TS25 through TS98 |

## Summary

TS99 refines the arithmetic root obligation from TS97 into a Selberg-weight
front. The hard arithmetic content remains explicit in the TS99/TS30 local
contracts.
