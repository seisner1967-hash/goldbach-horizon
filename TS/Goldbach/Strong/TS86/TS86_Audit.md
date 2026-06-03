# TS86 - Grand Sieve Variance Roadmap

## Status

TS86 opens the grand-sieve layer beneath the TS85 Gallagher variance contract.
It separates the expected proof into Farey-spacing geometry, a dual large-sieve
variance bound, and a grand-sieve variance infrastructure package. It then
proves that such a package feeds TS85, TS84, and the TS25 padded-scale assembly.

Status: `repo_committed_relative`.

TS86 does not prove the grand sieve, does not prove Farey-spacing estimates,
and does not instantiate the dual large-sieve variance bound. These remain
explicit analytic infrastructure obligations.

## Lean Files

- `GrandSieveVarianceRoadmap.lean`:
  - defines `GrandSieveVarianceRoadmap`;
  - defines `grandSieveVarianceRoadmap`;
  - defines `FareySpacingInfrastructure`;
  - defines `DualLargeSieveVarianceBound S`;
  - defines `GrandSieveVarianceInfrastructure S`;
  - defines `gallagherVarianceTransferContract_of_grandSieveVariance`;
  - defines `PaddedGrandSieveVarianceInfrastructure`;
  - defines `paddedGallagherVarianceTransferContract_of_grandSieveVariance`;
  - defines the TS86 roadmap and contract targets;
  - proves `grandSieveVarianceRoadmapTarget`;
  - defines `grandSieveVarianceInfrastructure_of_farey_dualLargeSieve`;
  - proves `grandSieveVarianceInfrastructureTarget_of_farey_dualLargeSieveTargets`;
  - proves `gallagherVarianceTransferContractTarget_of_grandSieveVarianceTarget`;
  - proves `paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget`;
  - proves `scaleTransferMajorantAPIContractsTarget_of_paddedGrandSieveTarget`;
  - proves `scaleTransferMajorantContractTarget_of_paddedGrandSieveTarget`;
  - proves `OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGrandSieve`;
  - proves `PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve`;
  - proves `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS86.GrandSieveVarianceRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS86
rg -n "a[x]iom" TS\Goldbach\Strong\TS86
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS86-G1 | `GrandSieveVarianceRoadmap` | `repo_committed` | records the grand-sieve variance proof layer |
| TS86-C1 | `FareySpacingInfrastructure` | `analytic_infrastructure_obligation` | rational-point spacing and covering geometry |
| TS86-C2 | `DualLargeSieveVarianceBound S` | `analytic_infrastructure_obligation` | scale-level dual large-sieve variance estimate |
| TS86-C3 | `GrandSieveVarianceInfrastructure S` | `analytic_infrastructure_obligation` | packages Farey geometry plus dual large-sieve variance |
| TS86-P1 | `gallagherVarianceTransferContractTarget_of_grandSieveVarianceTarget` | `repo_committed_relative` | grand-sieve package implies TS85 Gallagher contract |
| TS86-P2 | `scaleTransferMajorantAPIContractsTarget_of_paddedGrandSieveTarget` | `repo_committed_relative` | padded grand-sieve package implies TS84 scale-transfer API target |
| TS86-P3 | `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve` | `repo_committed_relative` | final contracts imply TS25 padded-scale infrastructure |

## Conclusion

TS86 pushes the scale-transfer front down to the grand-sieve/Farey-spacing
layer. The next analytic task is now precisely named: supply the Farey geometry
and dual large-sieve variance bound that imply the padded Gallagher transfer
contract.
