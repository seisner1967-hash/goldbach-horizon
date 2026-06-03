# TS85 - Scale Transfer Variance Ledger

## Status

TS85 opens the variance-transfer layer beneath the TS84 scale-transfer
majorant roadmap. It introduces a Gallagher-style variance transfer contract
for an explicit TS22 scale, specializes it to the TS24 padded closed-form
scale, and proves that this contract feeds the TS84 and TS25 assembly layers.

Status: `repo_committed_relative`.

TS85 does not prove Gallagher's variance estimate, does not prove a large-sieve
variance theorem, and does not instantiate the trace or Mellin-tail contracts.
It records the exact local contract needed before those analytic inputs can be
combined.

## Lean Files

- `ScaleTransferVarianceLedger.lean`:
  - defines `ScaleTransferVarianceLedger`;
  - defines `scaleTransferVarianceLedger`;
  - defines `GallagherVarianceTransferContract S`;
  - defines `scaleToOTSAControl_of_gallagherVariance`;
  - defines `PaddedGallagherVarianceTransferContract`;
  - defines `scaleTransferMajorantAPIContracts_of_paddedGallagher`;
  - defines `ScaleTransferVarianceLedgerTarget`;
  - defines `GallagherVarianceTransferContractTarget S`;
  - defines `PaddedGallagherVarianceTransferContractTarget`;
  - proves `scaleTransferVarianceLedgerTarget`;
  - proves `scaleToOTSAControlTarget_of_gallagherVarianceTarget`;
  - proves `scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget`;
  - proves `scaleTransferMajorantContractTarget_of_paddedGallagherTarget`;
  - proves `OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher`;
  - proves `PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher`;
  - proves `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS85.ScaleTransferVarianceLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS85
rg -n "a[x]iom" TS\Goldbach\Strong\TS85
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS85-G1 | `ScaleTransferVarianceLedger` | `repo_committed` | records the variance-transfer proof layer |
| TS85-C1 | `GallagherVarianceTransferContract S` | `analytic_infrastructure_obligation` | scale-level Gallagher/variance transfer contract |
| TS85-C2 | `PaddedGallagherVarianceTransferContract` | `analytic_infrastructure_obligation` | Gallagher contract specialized to the TS24 padded scale |
| TS85-P1 | `scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget` | `repo_committed_relative` | padded Gallagher target implies TS84 scale-transfer API target |
| TS85-P2 | `OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher` | `repo_committed_relative` | trace + Mellin + Gallagher contracts imply TS84 final OTSA majorants |
| TS85-P3 | `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher` | `repo_committed_relative` | final contracts imply TS25 padded-scale infrastructure |

## Conclusion

TS85 decomposes the scale-transfer front one layer further. The next analytic
task is now explicit: prove the padded Gallagher variance transfer contract
with rational factor at most `2`.
