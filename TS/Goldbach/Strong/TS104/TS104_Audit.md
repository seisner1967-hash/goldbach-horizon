# TS104 - Mobius Mathlib API Probe

## Status

`repo_committed_relative`

TS104 probes the current Mathlib Mobius API and records a concrete binding
layer below TS103. It locates `ArithmeticFunction.moebius`,
`ArithmeticFunction.zeta`, divisor finsets, divisor antidiagonal convolution,
and the bundled Mathlib theorem that `moebius` and `zeta` are convolution
inverses.

TS104 does not prove the full TS103 Mobius inversion infrastructure, gcd/lcm
kernel algebra, Selberg's sieve, Brun-Titchmarsh, or a prime-count estimate.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS104/MobiusMathlibAPIProbe.lean
```

Key declarations:

```lean
TS104.Goldbach.MobiusSymbolStatus
TS104.Goldbach.MobiusMathlibAPIProbe
TS104.Goldbach.mathlibMoebiusFun
TS104.Goldbach.mathlibDivisorSum
TS104.Goldbach.mathlibDirichletConvolution
TS104.Goldbach.mathlibArithmeticDelta
TS104.Goldbach.mathlibArithmeticDelta_one
TS104.Goldbach.mathlibArithmeticDelta_ne_one_zero
TS104.Goldbach.mobiusMathlibAPIProbe
TS104.Goldbach.MobiusConcreteBinding
TS104.Goldbach.mobiusConcreteBinding
TS104.Goldbach.divisorSumConvolution_of_concreteBinding
TS104.Goldbach.mobiusDeltaIdentity_of_concreteBinding
TS104.Goldbach.MobiusConcreteBindingInfrastructure
TS104.Goldbach.MobiusMathlibAPIProbeTarget
TS104.Goldbach.MobiusConcreteBindingTarget
TS104.Goldbach.MobiusConcreteBindingInfrastructureTarget
TS104.Goldbach.mobiusMathlibAPIProbeTarget
TS104.Goldbach.mobiusConcreteBindingTarget
TS104.Goldbach.divisorSumConvolutionTarget_of_concreteBindingTarget
TS104.Goldbach.mobiusDeltaIdentityTarget_of_concreteBindingTarget
TS104.Goldbach.mobiusInversionLedger_of_concreteBindingInfrastructure
TS104.Goldbach.mobiusInversionInfrastructure_of_concreteBindingInfrastructure
TS104.Goldbach.mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget
TS104.Goldbach.finalHorizonInputsTarget_of_mobiusConcrete_trace_mellin
TS104.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobiusConcrete_trace_mellin
TS104.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobiusConcrete_trace_mellin
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS104.MobiusMathlibAPIProbe

rg -n "s[o]rry" TS\Goldbach\Strong\TS104
rg -n "a[x]iom" TS\Goldbach\Strong\TS104
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS104-P1 | `MobiusMathlibAPIProbe` | `repo_committed` | records the located Mathlib Mobius, zeta, divisor, convolution, and inverse-theorem symbols |
| TS104-B1 | `MobiusConcreteBinding` | `repo_committed_relative` | binds TS103's unbundled Mobius/divisor API to concrete Mathlib symbols |
| TS104-B2 | `MobiusConcreteBindingInfrastructure` | `repo_committed_relative` | packages the concrete binding with the remaining TS103/TS30 Selberg obligations |
| TS104-T1 | `divisorSumConvolutionTarget_of_concreteBindingTarget` | `repo_committed_relative` | concrete binding supplies the TS103 divisor-sum/convolution target |
| TS104-T2 | `mobiusDeltaIdentityTarget_of_concreteBindingTarget` | `repo_committed_relative` | concrete binding supplies the TS103 Mobius-delta target |
| TS104-T3 | `mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget` | `repo_committed_relative` | concrete binding infrastructure supplies the full TS103 infrastructure target |
| TS104-T4 | `paddedScaleAnalyticInfrastructureTarget_of_mobiusConcrete_trace_mellin` | `repo_committed_relative` | concrete binding infrastructure plus TS95 and TS83 feed TS25 through TS103 |

## Summary

TS104 confirms that Mathlib already exposes the central Mobius arithmetic
function and its bundled convolution inverse theorem with zeta. The remaining
work is to turn that API into the full TS103 divisor-kernel and Selberg
infrastructure.
