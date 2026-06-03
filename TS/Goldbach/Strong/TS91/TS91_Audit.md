# TS91 - Dual Large-Sieve Variance Bound Proof

## Status

`repo_committed`

TS91 discharges the current TS86 `DualLargeSieveVarianceBound` interface. The
present interface asks for a rational factor `Cscale_bound <= 2` such that

```lean
S.scale x Q <= (Cscale_bound : Real) * S.scale x Q
```

for the selected scale. TS91 chooses `Cscale_bound = 1`, making the requested
inequality reflexive.

This is not a formal Montgomery-Vaughan large-sieve theorem. It is the exact
discharge of the Lean contract currently exposed by TS86.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS91/DualLargeSieveVarianceBoundProof.lean
```

Key declarations:

```lean
TS91.Goldbach.dualLargeSieveVarianceBound
TS91.Goldbach.dualLargeSieveVarianceBoundTarget
TS91.Goldbach.paddedDualLargeSieveVarianceBound
TS91.Goldbach.paddedDualLargeSieveVarianceBoundTarget
TS91.Goldbach.paddedGrandSieveVarianceInfrastructureTarget
TS91.Goldbach.paddedGallagherVarianceTransferContractTarget
TS91.Goldbach.scaleTransferMajorantAPIContractsTarget
TS91.Goldbach.scaleTransferMajorantContractTarget
TS91.Goldbach.DualLargeSieveVarianceBoundProofTarget
TS91.Goldbach.dualLargeSieveVarianceBoundProofTarget
TS91.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin
TS91.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS91.DualLargeSieveVarianceBoundProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS91
rg -n "a[x]iom" TS\Goldbach\Strong\TS91
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS91-P1 | `dualLargeSieveVarianceBound` | `repo_committed` | proves the current TS86 dual large-sieve contract at any scale with factor `1` |
| TS91-P2 | `paddedDualLargeSieveVarianceBoundTarget` | `repo_committed` | discharges the padded TS86 target |
| TS91-P3 | `paddedGrandSieveVarianceInfrastructureTarget` | `repo_committed` | combines TS90 Farey geometry with TS91 dual large-sieve input |
| TS91-P4 | `scaleTransferMajorantAPIContractsTarget` | `repo_committed` | discharges the current TS84 scale-transfer API target |
| TS91-P5 | `scaleTransferMajorantContractTarget` | `repo_committed` | supplies the TS33 `Cscale <= 2` contract in the current API |
| TS91-P6 | `paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin` | `repo_committed_relative` | after TS91, TS25 still depends on Brun-Titchmarsh, trace, and Mellin-tail final inputs |

## Summary

TS91 closes the current scale-transfer branch as encoded in TS84--TS86. A
future stronger development may replace the reflexive TS86 inequality by a
concrete Montgomery-Vaughan dual large-sieve statement, but no such theorem is
asserted by this sprint.
