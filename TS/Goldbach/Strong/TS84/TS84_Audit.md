# TS84 - Scale Transfer Majorant Roadmap

## Status

TS84 opens the scale-transfer front after the TS83 Mellin-tail ledger. It
records the remaining `Cscale <= 2` work as an explicit local API contract,
then proves that this contract mechanically feeds the existing TS33 and TS25
assembly layers.

Status: `repo_committed_relative`.

TS84 does not prove a Gallagher/large-sieve scale transfer theorem, does not
instantiate a concrete Brun-Titchmarsh theorem, and does not prove the remaining
Mellin-tail or trace API contracts. It shows how those contracts combine once
they are supplied.

## Lean Files

- `ScaleTransferMajorantRoadmap.lean`:
  - defines `ScaleTransferMajorantRoadmap`;
  - defines `scaleTransferMajorantRoadmap`;
  - defines `ScaleTransferMajorantAPIContracts`;
  - defines `scaleTransferMajorantContract_of_apiContracts`;
  - defines `OTSAFinalMajorantAPIContracts`;
  - defines `mellinTailMajorantContract_of_finalAPIContracts`;
  - defines `scaleTransferMajorantContract_of_finalAPIContracts`;
  - defines `OTSACert_candidate_v3_of_finalAPIContracts`;
  - defines `OTSARegister_candidate_v3_of_finalAPIContracts`;
  - defines `OTSAProvenance_candidate_v3_of_finalAPIContracts`;
  - proves `scaledOTSAAdmissible_of_finalAPIContracts`;
  - defines `PaddedScaleTransferFinalAPIContracts`;
  - defines `paddedScaleAnalyticInfrastructure_of_finalAPIContracts`;
  - defines the TS84 roadmap and contract targets;
  - proves `scaleTransferMajorantRoadmapTarget`;
  - proves `scaleTransferMajorantContractTarget_of_apiContractsTarget`;
  - proves `traceMajorantContractTarget_of_finalAPIContractsTarget`;
  - proves `mellinTailFinalAPIContractsTarget_of_finalAPIContractsTarget`;
  - proves `scaleTransferMajorantContractTarget_of_finalAPIContractsTarget`;
  - proves `OTSACert_candidate_v3_target_of_finalAPIContractsTarget`;
  - proves `OTSARegister_candidate_v3_target_of_finalAPIContractsTarget`;
  - proves `OTSAProvenance_candidate_v3_target_of_finalAPIContractsTarget`;
  - proves `scaledOTSAAdmissibleTarget_of_finalAPIContractsTarget`;
  - proves `paddedScaleAnalyticInfrastructureTarget_of_finalAPIContractsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS84.ScaleTransferMajorantRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS84
rg -n "a[x]iom" TS\Goldbach\Strong\TS84
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS84-G1 | `ScaleTransferMajorantRoadmap` | `repo_committed` | records the scale-transfer front after TS83 |
| TS84-C1 | `ScaleTransferMajorantAPIContracts` | `analytic_infrastructure_obligation` | padded scale control plus rational `Cscale <= 2` |
| TS84-C2 | `OTSAFinalMajorantAPIContracts` | `analytic_infrastructure_obligation` | trace, Mellin-tail, and scale-transfer final contracts |
| TS84-C3 | `PaddedScaleTransferFinalAPIContracts` | `analytic_infrastructure_obligation` | adds Brun-Titchmarsh input for TS25 padded infrastructure |
| TS84-P1 | `scaleTransferMajorantContractTarget_of_apiContractsTarget` | `repo_committed_relative` | scale contracts imply the TS33 scale-transfer contract |
| TS84-P2 | `scaledOTSAAdmissible_of_finalAPIContracts` | `repo_committed_relative` | final contracts imply TS23 scaled admissibility |
| TS84-P3 | `paddedScaleAnalyticInfrastructureTarget_of_finalAPIContractsTarget` | `repo_committed_relative` | final padded contracts imply TS25 infrastructure |

## Conclusion

TS84 moves the architecture from the closed Mellin-tail ledger to the
scale-transfer pillar. The remaining `Cscale` work is now named precisely:
provide a padded-scale TS23 transfer control and a compatible rational bound
`Cscale <= 2`.
