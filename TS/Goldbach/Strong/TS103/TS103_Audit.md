# TS103 - Mobius Inversion Ledger

## Status

`repo_committed_relative`

TS103 opens the Mobius-inversion layer below the TS101 Selberg
divisor-algebra front. It records the divisor-sum/convolution API, the
Mobius-delta identity package, and the local infrastructure expected to
recover the TS101 divisor-algebra infrastructure.

TS103 does not prove Mobius inversion, divisor-convolution algebra, gcd/lcm
kernel algebra, Selberg's sieve, Brun-Titchmarsh, or a prime-count estimate.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS103/MobiusInversionLedger.lean
```

Key declarations:

```lean
TS103.Goldbach.MobiusInversionRoadmap
TS103.Goldbach.mobiusInversionRoadmap
TS103.Goldbach.DivisorSumConvolution
TS103.Goldbach.MobiusDeltaIdentity
TS103.Goldbach.MobiusInversionLedger
TS103.Goldbach.MobiusInversionInfrastructure
TS103.Goldbach.MobiusInversionRoadmapTarget
TS103.Goldbach.DivisorSumConvolutionTarget
TS103.Goldbach.MobiusDeltaIdentityTarget
TS103.Goldbach.MobiusInversionLedgerTarget
TS103.Goldbach.MobiusInversionInfrastructureTarget
TS103.Goldbach.mobiusInversionRoadmapTarget
TS103.Goldbach.selbergDivisorAlgebraLedger_of_mobiusInversionLedger
TS103.Goldbach.selbergDivisorAlgebraInfrastructure_of_mobiusInversionInfrastructure
TS103.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.selbergQuadraticFormInfrastructureTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.selbergSieveWeightInfrastructureTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.finalHorizonInputsTarget_of_mobius_trace_mellin
TS103.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobius_trace_mellin
TS103.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobius_trace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS103.MobiusInversionLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS103
rg -n "a[x]iom" TS\Goldbach\Strong\TS103
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS103-R1 | `MobiusInversionRoadmap` | `repo_committed` | records the Mobius-inversion layer to be formalized |
| TS103-A1 | `DivisorSumConvolution` | `repo_committed_relative` | records the divisor-sum and Dirichlet-convolution API expected by Selberg |
| TS103-A2 | `MobiusDeltaIdentity` | `repo_committed_relative` | records the Mobius-delta identity and inversion readiness |
| TS103-A3 | `MobiusInversionLedger` | `repo_committed_relative` | packages Mobius data with divisor weights and gcd/lcm kernels |
| TS103-A4 | `MobiusInversionInfrastructure` | `repo_committed_relative` | packages Mobius data with the TS100/TS99/TS30 Selberg obligations |
| TS103-P1 | `selbergDivisorAlgebraInfrastructure_of_mobiusInversionInfrastructure` | `repo_committed_relative` | Mobius infrastructure supplies TS101 divisor-algebra infrastructure |
| TS103-P2 | `brunTitchmarshFinalInputLedgerTarget_of_mobiusInversionInfrastructureTarget` | `repo_committed_relative` | Mobius infrastructure supplies the TS97 final BT input through TS101 |
| TS103-P3 | `paddedScaleAnalyticInfrastructureTarget_of_mobius_trace_mellin` | `repo_committed_relative` | Mobius infrastructure plus TS95 and TS83 feed TS25 through TS101 |

## Summary

TS103 refines the TS101 divisor-algebra front into a Mobius-inversion front.
The hard arithmetic content remains explicit in the TS103/TS101/TS100/TS99/TS30
local contracts.
