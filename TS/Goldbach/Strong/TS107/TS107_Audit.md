# TS107 Audit - Selberg Quadratic Kernel Extraction Ledger

## Status

`repo_committed_relative`

TS107 extracts the canonical Selberg-style quadratic kernel from the TS106
canonical rational gcd/lcm kernels. It proves the symmetry of the canonical
kernel

```text
gcd(a,b) / lcm(a,b)
```

as a rational-valued kernel and uses that extraction to populate the TS106
`SelbergQuadraticKernelExtractionTarget`.

This sprint does not prove Selberg's sieve, Brun-Titchmarsh, quadratic-form
diagonalization, the interval majorant, the sieve bound, the budget comparison,
or any prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS107/SelbergQuadraticKernelExtractionLedger.lean
```

## Key declarations

```lean
TS107.Goldbach.canonicalSelbergQuadraticKernel
TS107.Goldbach.canonicalSelbergQuadraticKernel_symm
TS107.Goldbach.SelbergQuadraticKernelExtractionProof
TS107.Goldbach.selbergQuadraticKernelExtractionProof
TS107.Goldbach.selbergQuadraticKernelExtraction_of_proof
TS107.Goldbach.SelbergKernelExtractionInfrastructure
TS107.Goldbach.SelbergQuadraticKernelExtractionProofTarget
TS107.Goldbach.SelbergKernelExtractionInfrastructureTarget
TS107.Goldbach.selbergQuadraticKernelExtractionProofTarget
TS107.Goldbach.selbergQuadraticKernelExtractionTarget
TS107.Goldbach.divisorKernelAlgebraInfrastructure_of_kernelExtractionInfrastructure
TS107.Goldbach.divisorKernelAlgebraInfrastructureTarget_of_kernelExtractionInfrastructureTarget
TS107.Goldbach.mobiusInversionInfrastructureTarget_of_kernelExtractionInfrastructureTarget
TS107.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_kernelExtractionInfrastructureTarget
TS107.Goldbach.finalHorizonInputsTarget_of_kernelExtraction_trace_mellin
TS107.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_kernelExtraction_trace_mellin
TS107.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_kernelExtraction_trace_mellin
```

## Proof summary

The theorem

```lean
TS107.Goldbach.canonicalSelbergQuadraticKernel_symm
```

unfolds the canonical rational kernel and rewrites with Mathlib's

```lean
Nat.gcd_comm
Nat.lcm_comm
```

The extraction proof then packages this symmetric gcd/lcm ratio with TS106's
canonical gcd/lcm product identity and supplies the TS106 extraction target.

The full `SelbergKernelExtractionInfrastructure` remains relative: it still
requires the TS30 interval majorant, sieve theorem, and budget comparison.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS107.SelbergQuadraticKernelExtractionLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS107
rg -n "a[x]iom" TS\Goldbach\Strong\TS107
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS107
git diff --check -- README.md TS\Goldbach\Strong\TS107\SelbergQuadraticKernelExtractionLedger.lean TS\Goldbach\Strong\TS107\TS107_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS107-K1 | `canonicalSelbergQuadraticKernel` | `repo_committed` | defines the canonical rational gcd/lcm ratio kernel |
| TS107-K2 | `canonicalSelbergQuadraticKernel_symm` | `repo_committed` | proves symmetry of the canonical kernel |
| TS107-E1 | `SelbergQuadraticKernelExtractionProof` | `repo_committed_relative` | packages the extracted kernel and remaining expansion/diagonalization markers |
| TS107-E2 | `selbergQuadraticKernelExtractionTarget` | `repo_committed` | supplies the TS106 extraction target |
| TS107-I1 | `SelbergKernelExtractionInfrastructure` | `repo_committed_relative` | packages the remaining kernel-to-Selberg route |
| TS107-T1 | `mobiusInversionInfrastructureTarget_of_kernelExtractionInfrastructureTarget` | `repo_committed_relative` | transports kernel extraction infrastructure into TS103 through TS106 |
| TS107-T2 | `paddedScaleAnalyticInfrastructureTarget_of_kernelExtraction_trace_mellin` | `repo_committed_relative` | transports TS107 plus TS95 and TS83 to TS25 through TS106 |

## Remaining work

TS107 does not close the arithmetic front. The remaining work is to prove the
finite quadratic-form expansion, diagonalization, interval majorant, Selberg
sieve bound, and Brun-Titchmarsh budget comparison.
