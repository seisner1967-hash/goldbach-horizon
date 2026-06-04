# TS108 Audit - Selberg Quadratic Form Expansion Ledger

## Status

`repo_committed_relative`

TS108 formalizes the finite quadratic-form expansion layer above TS107. It
defines the finite double sum

```text
sum_a sum_b w(a) * w(b) * gcd(a,b) / lcm(a,b)
```

over `Finset.range (level + 1)` and proves the immediate symmetry of the
summand and the index-swapped expansion using TS107's canonical kernel
symmetry.

This sprint does not prove the quadratic-form diagonalization, Selberg's
sieve, Brun-Titchmarsh, the interval majorant, the budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS108/SelbergQuadraticFormExpansionLedger.lean
```

## Key declarations

```lean
TS108.Goldbach.selbergQuadraticFormTerm
TS108.Goldbach.selbergQuadraticFormTerm_symm
TS108.Goldbach.selbergQuadraticSupport
TS108.Goldbach.selbergQuadraticForm
TS108.Goldbach.selbergQuadraticForm_expansion
TS108.Goldbach.selbergQuadraticForm_swap_indices
TS108.Goldbach.SelbergQuadraticFormExpansion
TS108.Goldbach.selbergQuadraticFormExpansion
TS108.Goldbach.SelbergQuadraticFormExpansionTarget
TS108.Goldbach.selbergQuadraticFormExpansionTarget
TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructure
TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructureTarget
TS108.Goldbach.kernelExtractionInfrastructure_of_quadraticFormExpansionInfrastructure
TS108.Goldbach.selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
TS108.Goldbach.divisorKernelAlgebraInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
TS108.Goldbach.mobiusInversionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
TS108.Goldbach.finalHorizonInputsTarget_of_quadraticExpansion_trace_mellin
TS108.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_quadraticExpansion_trace_mellin
TS108.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_quadraticExpansion_trace_mellin
```

## Proof summary

The theorem

```lean
TS108.Goldbach.selbergQuadraticFormTerm_symm
```

uses `TS107.Goldbach.canonicalSelbergQuadraticKernel_symm` and ring
normalization over `Rat` to swap the indices of one quadratic-form term.

The theorem

```lean
TS108.Goldbach.selbergQuadraticForm_swap_indices
```

lifts that termwise symmetry through the finite double sum over
`Finset.range (level + 1)`.

The full `SelbergQuadraticFormExpansionInfrastructure` remains relative: it
still requires the TS30 interval majorant, sieve theorem, and budget comparison.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS108.SelbergQuadraticFormExpansionLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS108
rg -n "a[x]iom" TS\Goldbach\Strong\TS108
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS108
git diff --check -- README.md TS\Goldbach\Strong\TS108\SelbergQuadraticFormExpansionLedger.lean TS\Goldbach\Strong\TS108\TS108_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS108-Q1 | `selbergQuadraticFormTerm` | `repo_committed` | defines one term of the canonical Selberg quadratic form |
| TS108-Q2 | `selbergQuadraticFormTerm_symm` | `repo_committed` | proves termwise symmetry from TS107 kernel symmetry |
| TS108-Q3 | `selbergQuadraticForm` | `repo_committed` | defines the finite double-sum quadratic form |
| TS108-Q4 | `selbergQuadraticForm_swap_indices` | `repo_committed` | proves the index-swapped finite expansion |
| TS108-E1 | `SelbergQuadraticFormExpansion` | `repo_committed_relative` | packages the finite expansion and diagonalization marker |
| TS108-I1 | `SelbergQuadraticFormExpansionInfrastructure` | `repo_committed_relative` | packages the expansion with remaining TS30 Selberg obligations |
| TS108-T1 | `mobiusInversionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget` | `repo_committed_relative` | transports expansion infrastructure into TS103 through TS107 |
| TS108-T2 | `paddedScaleAnalyticInfrastructureTarget_of_quadraticExpansion_trace_mellin` | `repo_committed_relative` | transports TS108 plus TS95 and TS83 to TS25 through TS107 |

## Remaining work

TS108 does not close the arithmetic front. The remaining work is to prove the
quadratic-form diagonalization, interval majorant, Selberg sieve bound, and
Brun-Titchmarsh budget comparison.
