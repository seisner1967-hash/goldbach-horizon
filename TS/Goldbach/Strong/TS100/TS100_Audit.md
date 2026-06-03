# TS100 - Selberg Quadratic Form Ledger

## Status

`repo_committed_relative`

TS100 opens the Selberg quadratic-form layer below the TS99 Selberg-weight
front. It records the quadratic kernel, divisor algebra, Mobius-inversion,
diagonalization, and square-majorant obligations expected before recovering the
TS99 Selberg-weight infrastructure.

TS100 does not prove Selberg's sieve, Brun-Titchmarsh, Mobius inversion,
quadratic-form diagonalization, or a prime-count estimate.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS100/SelbergQuadraticFormLedger.lean
```

Key declarations:

```lean
TS100.Goldbach.SelbergQuadraticFormRoadmap
TS100.Goldbach.selbergQuadraticFormRoadmap
TS100.Goldbach.SelbergQuadraticFormLedger
TS100.Goldbach.SelbergQuadraticFormInfrastructure
TS100.Goldbach.SelbergQuadraticFormRoadmapTarget
TS100.Goldbach.SelbergQuadraticFormLedgerTarget
TS100.Goldbach.SelbergQuadraticFormInfrastructureTarget
TS100.Goldbach.selbergQuadraticFormRoadmapTarget
TS100.Goldbach.selbergSieveWeightInfrastructure_of_quadraticFormInfrastructure
TS100.Goldbach.selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget
TS100.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_quadraticFormInfrastructureTarget
TS100.Goldbach.finalHorizonInputsTarget_of_selbergQuadratic_trace_mellin
TS100.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergQuadratic_trace_mellin
TS100.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergQuadratic_trace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS100.SelbergQuadraticFormLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS100
rg -n "a[x]iom" TS\Goldbach\Strong\TS100
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS100-R1 | `SelbergQuadraticFormRoadmap` | `repo_committed` | records the divisor-algebra and quadratic-form layer to be formalized |
| TS100-A1 | `SelbergQuadraticFormLedger` | `repo_committed_relative` | records finite Selberg weight data plus a quadratic kernel |
| TS100-A2 | `SelbergQuadraticFormInfrastructure` | `repo_committed_relative` | packages the quadratic ledger with the TS30 sieve and budget obligations |
| TS100-P1 | `selbergSieveWeightInfrastructure_of_quadraticFormInfrastructure` | `repo_committed_relative` | quadratic infrastructure supplies TS99 Selberg-weight infrastructure |
| TS100-P2 | `brunTitchmarshFinalInputLedgerTarget_of_quadraticFormInfrastructureTarget` | `repo_committed_relative` | quadratic infrastructure supplies the TS97 final BT input target through TS99 |
| TS100-P3 | `paddedScaleAnalyticInfrastructureTarget_of_selbergQuadratic_trace_mellin` | `repo_committed_relative` | Selberg quadratic infrastructure plus TS95 and TS83 feed TS25 through TS99 |

## Summary

TS100 refines the TS99 Selberg-weight front into a quadratic-form front. The
hard arithmetic content remains explicit in the TS100/TS99/TS30 local
contracts.
