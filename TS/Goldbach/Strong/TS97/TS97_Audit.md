# TS97 - Brun-Titchmarsh Final Input Ledger

## Status

`repo_committed_relative`

TS97 isolates the final arithmetic input still needed by the padded-scale
assembly route: a concrete `TS22.Goldbach.BrunTitchmarshNatIntervalBound`.

TS97 does not prove Brun-Titchmarsh, Selberg's sieve, or a prime-count estimate.
It records the exact TS22 object required and proves the mechanical bridges from
that object, plus the TS95 trace ledger and TS83 Mellin-tail contracts, to the
TS84/TS25 final assembly routes.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS97/BrunTitchmarshFinalInputLedger.lean
```

Key declarations:

```lean
TS97.Goldbach.BrunTitchmarshFinalInputRoadmap
TS97.Goldbach.brunTitchmarshFinalInputRoadmap
TS97.Goldbach.BrunTitchmarshFinalInputLedger
TS97.Goldbach.BrunTitchmarshFinalInputRoadmapTarget
TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget
TS97.Goldbach.brunTitchmarshFinalInputRoadmapTarget
TS97.Goldbach.brunTitchmarshNatIntervalBoundTarget_of_finalInputLedgerTarget
TS97.Goldbach.paddedScaleTransferFinalAPIContracts_of_finalInputLedger
TS97.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin
TS97.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS97.BrunTitchmarshFinalInputLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS97
rg -n "a[x]iom" TS\Goldbach\Strong\TS97
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS97-R1 | `BrunTitchmarshFinalInputRoadmap` | `repo_committed` | records that the final arithmetic input is the TS22 natural-interval BT theorem |
| TS97-A1 | `BrunTitchmarshFinalInputLedger` | `repo_committed_relative` | wraps the exact `TS22.Goldbach.BrunTitchmarshNatIntervalBound` still needed |
| TS97-P1 | `brunTitchmarshNatIntervalBoundTarget_of_finalInputLedgerTarget` | `repo_committed_relative` | extracts the raw TS22 BT target from the TS97 ledger |
| TS97-P2 | `paddedScaleTransferFinalAPIContractsTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin` | `repo_committed_relative` | TS97 plus TS95 and TS83 supplies the TS84 padded final API target |
| TS97-P3 | `paddedScaleAnalyticInfrastructureTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin` | `repo_committed_relative` | TS97 plus TS95 and TS83 supplies the TS25 padded-scale infrastructure target |

## Summary

TS97 names the last central arithmetic input for the current global assembly:
the natural-interval Brun-Titchmarsh theorem. The proof of that theorem remains
external to this sprint.
