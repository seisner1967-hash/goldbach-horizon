# TS106 Audit - Divisor Kernel Algebra Ledger

## Status

`repo_committed_relative`

TS106 opens the divisor-kernel algebra layer above the TS105 Mobius-delta
discharge. It proves the canonical rational gcd/lcm product identity and
packages the remaining divisor-kernel infrastructure feeding TS103.

This sprint does not prove Selberg's sieve, Brun-Titchmarsh, quadratic-form
diagonalization, or any prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS106/DivisorKernelAlgebraLedger.lean
```

## Key declarations

```lean
TS106.Goldbach.canonicalGcdKernel
TS106.Goldbach.canonicalLcmKernel
TS106.Goldbach.canonicalGcdKernel_mul_lcmKernel
TS106.Goldbach.DivisorConvolutionBridge
TS106.Goldbach.divisorConvolutionBridge
TS106.Goldbach.GCDLCMKernelAlgebra
TS106.Goldbach.gcdLCMKernelAlgebra
TS106.Goldbach.SelbergQuadraticKernelExtraction
TS106.Goldbach.DivisorKernelAlgebraInfrastructure
TS106.Goldbach.DivisorConvolutionBridgeTarget
TS106.Goldbach.GCDLCMKernelAlgebraTarget
TS106.Goldbach.SelbergQuadraticKernelExtractionTarget
TS106.Goldbach.DivisorKernelAlgebraInfrastructureTarget
TS106.Goldbach.divisorConvolutionBridgeTarget
TS106.Goldbach.gcdLCMKernelAlgebraTarget
TS106.Goldbach.mobiusInversionLedger_of_divisorKernelAlgebraInfrastructure
TS106.Goldbach.mobiusInversionInfrastructure_of_divisorKernelAlgebraInfrastructure
TS106.Goldbach.mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
TS106.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
TS106.Goldbach.finalHorizonInputsTarget_of_divisorKernel_trace_mellin
TS106.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_divisorKernel_trace_mellin
TS106.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_divisorKernel_trace_mellin
```

## Proof summary

The theorem

```lean
TS106.Goldbach.canonicalGcdKernel_mul_lcmKernel
```

uses Mathlib's

```lean
Nat.gcd_mul_lcm
```

and `exact_mod_cast` to transport the natural-number identity to the
rational-valued canonical kernels.

The full `DivisorKernelAlgebraInfrastructure` remains a relative package:
given the remaining Selberg quadratic-kernel, majorant, sieve, and budget
fields, TS106 constructs the TS103 `MobiusInversionInfrastructure`.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS106.DivisorKernelAlgebraLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS106
rg -n "a[x]iom" TS\Goldbach\Strong\TS106
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS106
git diff --check -- README.md TS\Goldbach\Strong\TS106\DivisorKernelAlgebraLedger.lean TS\Goldbach\Strong\TS106\TS106_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS106-G1 | `canonicalGcdKernel_mul_lcmKernel` | `repo_committed` | proves the rational canonical gcd/lcm product identity |
| TS106-C1 | `DivisorConvolutionBridge` | `repo_committed` | packages TS104 concrete binding and TS105 Mobius-delta discharge |
| TS106-K1 | `GCDLCMKernelAlgebra` | `repo_committed` | provides canonical gcd/lcm kernels with the product identity |
| TS106-Q1 | `SelbergQuadraticKernelExtraction` | `repo_committed_relative` | names the remaining extraction of Selberg's quadratic kernel from divisor kernels |
| TS106-I1 | `DivisorKernelAlgebraInfrastructure` | `repo_committed_relative` | packages the remaining divisor-kernel and TS30 Selberg obligations |
| TS106-T1 | `mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget` | `repo_committed_relative` | transports full divisor-kernel infrastructure into TS103 |
| TS106-T2 | `paddedScaleAnalyticInfrastructureTarget_of_divisorKernel_trace_mellin` | `repo_committed_relative` | transports TS106 plus TS95 and TS83 to TS25 through TS103 |

## Remaining work

TS106 does not close the full arithmetic front. The remaining work is to
instantiate the Selberg quadratic-kernel extraction, prove the relevant
quadratic-form diagonalization, build the interval majorant, prove the Selberg
sieve bound, and discharge the Brun-Titchmarsh budget comparison.
