# TS109 Audit - Selberg Quadratic Diagonalization Ledger

## Status

`repo_committed_relative`

TS109 opens the diagonalization layer above the finite Selberg quadratic-form
expansion of TS108. It defines a finite divisor-filtered change of variables,
a diagonal coefficient slot, and the corresponding finite diagonal square sum.

This sprint does not prove the dense-to-diagonal Selberg identity, the
square-sum majorant, Selberg's sieve, Brun-Titchmarsh, the interval majorant,
the budget comparison, or any prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS109/SelbergQuadraticDiagonalizationLedger.lean
```

## Key declarations

```lean
TS109.Goldbach.selbergDiagonalSupport
TS109.Goldbach.selbergDiagonalTransformedWeight
TS109.Goldbach.selbergUnitDiagonalCoefficient
TS109.Goldbach.selbergDiagonalSquareTerm
TS109.Goldbach.selbergDiagonalSquareSum
TS109.Goldbach.selbergDiagonalTransformedWeight_expansion
TS109.Goldbach.selbergDiagonalSquareSum_expansion
TS109.Goldbach.SelbergDiagonalChangeOfVariables
TS109.Goldbach.selbergDiagonalChangeOfVariables
TS109.Goldbach.SelbergQuadraticDiagonalization
TS109.Goldbach.selbergQuadraticDiagonalization
TS109.Goldbach.SelbergQuadraticDiagonalizationTarget
TS109.Goldbach.selbergQuadraticDiagonalizationTarget
TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructure
TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructureTarget
TS109.Goldbach.quadraticFormExpansionInfrastructure_of_diagonalizationInfrastructure
TS109.Goldbach.quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
TS109.Goldbach.selbergKernelExtractionInfrastructureTarget_of_diagonalizationInfrastructureTarget
TS109.Goldbach.mobiusInversionInfrastructureTarget_of_diagonalizationInfrastructureTarget
TS109.Goldbach.finalHorizonInputsTarget_of_diagonalization_trace_mellin
TS109.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_diagonalization_trace_mellin
TS109.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_diagonalization_trace_mellin
```

## Proof summary

The definitions

```lean
TS109.Goldbach.selbergDiagonalTransformedWeight
TS109.Goldbach.selbergDiagonalSquareSum
```

record the finite diagonal side of the Selberg quadratic form over the same
support window used in TS108. The expansion theorems are definitional
equalities.

The full `SelbergQuadraticDiagonalizationInfrastructure` remains relative: it
packages a TS108 expansion infrastructure together with readiness markers for
the dense-to-diagonal identity, square-sum majorant, Selberg sieve, and budget
comparison.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS109.SelbergQuadraticDiagonalizationLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS109
rg -n "a[x]iom" TS\Goldbach\Strong\TS109
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS109
git diff --check -- README.md TS\Goldbach\Strong\TS109\SelbergQuadraticDiagonalizationLedger.lean TS\Goldbach\Strong\TS109\TS109_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS109-D1 | `selbergDiagonalTransformedWeight` | `repo_committed` | defines the finite divisor-filtered transformed weight |
| TS109-D2 | `selbergDiagonalSquareSum` | `repo_committed` | defines the diagonal finite square sum |
| TS109-D3 | `selbergDiagonalSquareSum_expansion` | `repo_committed` | records the definitional finite diagonal expansion |
| TS109-C1 | `SelbergDiagonalChangeOfVariables` | `repo_committed_relative` | packages the future triangular Selberg change of variables |
| TS109-Q1 | `SelbergQuadraticDiagonalization` | `repo_committed_relative` | packages the dense expansion and diagonal square-sum side |
| TS109-I1 | `SelbergQuadraticDiagonalizationInfrastructure` | `repo_committed_relative` | packages diagonalization with the remaining TS30 Selberg obligations |
| TS109-T1 | `quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget` | `repo_committed_relative` | transports diagonalization infrastructure into TS108 |
| TS109-T2 | `paddedScaleAnalyticInfrastructureTarget_of_diagonalization_trace_mellin` | `repo_committed_relative` | transports TS109 plus TS95 and TS83 to TS25 through TS108 |

## Remaining work

TS109 does not close the arithmetic front. The remaining work is to prove the
dense-to-diagonal Selberg identity, the square-sum majorant, interval majorant,
Selberg sieve bound, and Brun-Titchmarsh budget comparison.
