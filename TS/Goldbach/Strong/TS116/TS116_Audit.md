# TS116 Audit - Selberg GCD Coefficient Kernel Match Ledger

## Status

`repo_committed_relative`

TS116 opens the local kernel-match layer below the TS115 Mobius-coefficient
ledger. It exposes the diagonal coefficient slot used in the TS115 filtered
coefficient sum, rewrites the gcd coefficient through that explicit formula,
and proves that the resulting compatibility obligation supplies the TS115
coefficient-kernel match.

The current TS109 diagonal coefficient is still the unit placeholder. TS116
therefore does not prove the Mobius coefficient calculation or claim that the
current coefficient normalization already matches the dense `gcd/lcm` kernel.
It records the exact compatibility obligation needed before the
dense-to-diagonal Selberg identity can be closed.

This sprint does not prove the Mobius coefficient calculation, the dense
kernel match, the dense-to-diagonal identity, square-sum majorant, Selberg's
sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS116/SelbergGcdCoefficientKernelMatchLedger.lean
```

## Key declarations

```lean
TS116.Goldbach.selbergDiagonalCoefficientFormula
TS116.Goldbach.selbergDiagonalCoefficientFormula_eq_unit
TS116.Goldbach.selbergGcdCoefficient_eq_formula_filter_sum
TS116.Goldbach.selbergCanonicalKernelFromGcd
TS116.Goldbach.SelbergGcdCoefficientKernelCompatibility
TS116.Goldbach.gcdCoefficientKernelCompatibility_iff_ts115_match
TS116.Goldbach.gcdCoefficientKernelMatchObligation_of_compatibility
TS116.Goldbach.innerGcdKernelMatchObligation_of_compatibility
TS116.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_compatibility
TS116.Goldbach.SelbergGcdCoefficientKernelMatch
TS116.Goldbach.selbergGcdCoefficientKernelMatch
TS116.Goldbach.SelbergGcdCoefficientKernelMatchTarget
TS116.Goldbach.selbergGcdCoefficientKernelMatchTarget
TS116.Goldbach.SelbergGcdCoefficientKernelMatchInfrastructure
TS116.Goldbach.SelbergGcdCoefficientKernelMatchInfrastructureTarget
TS116.Goldbach.coefficientInfrastructure_of_kernelMatchInfrastructure
TS116.Goldbach.coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.innerCollapseInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.fubiniInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.mobiusCollapseInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.mobiusInversionInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.finalHorizonInputsTarget_of_kernelMatch_trace_mellin
TS116.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_kernelMatch_trace_mellin
TS116.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_kernelMatch_trace_mellin
```

## Proof summary

The theorem

```lean
TS116.Goldbach.selbergDiagonalCoefficientFormula_eq_unit
```

records that the current TS109 diagonal coefficient slot is the unit
placeholder.

The theorem

```lean
TS116.Goldbach.selbergGcdCoefficient_eq_formula_filter_sum
```

rewrites the TS115 gcd coefficient as a filtered finite sum of the explicit
diagonal coefficient formula.

The theorem

```lean
TS116.Goldbach.gcdCoefficientKernelCompatibility_iff_ts115_match
```

identifies the TS116 local compatibility obligation with the TS115
coefficient-kernel match.

The theorem

```lean
TS116.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_compatibility
```

propagates the local compatibility through TS115 and TS114 to the conditional
TS112 gcd-filtered dense-side equality.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS116.SelbergGcdCoefficientKernelMatchLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS116
rg -n "a[x]iom" TS\Goldbach\Strong\TS116
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS116
git diff --check -- README.md TS\Goldbach\Strong\TS116\SelbergGcdCoefficientKernelMatchLedger.lean TS\Goldbach\Strong\TS116\TS116_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS116-R1 | `selbergDiagonalCoefficientFormula_eq_unit` | `repo_committed` | exposes the current TS109 diagonal coefficient as the unit placeholder |
| TS116-R2 | `selbergGcdCoefficient_eq_formula_filter_sum` | `repo_committed` | rewrites the TS115 gcd coefficient through the explicit diagonal coefficient formula |
| TS116-R3 | `gcdCoefficientKernelCompatibility_iff_ts115_match` | `repo_committed_relative` | identifies the TS116 compatibility with the TS115 match obligation |
| TS116-R4 | `selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_compatibility` | `repo_committed_relative` | transports the compatibility through TS115/TS114 to the TS112 dense-side equality |
| TS116-I1 | `SelbergGcdCoefficientKernelCompatibility` | `repo_committed_relative` | names the remaining local coefficient-to-`gcd/lcm` kernel compatibility |
| TS116-I2 | `SelbergGcdCoefficientKernelMatch` | `repo_committed_relative` | packages the coefficient formula plus the remaining compatibility obligation |
| TS116-T1 | `coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget` | `repo_committed_relative` | transports TS116 infrastructure into TS115 |
| TS116-T2 | `paddedScaleAnalyticInfrastructureTarget_of_kernelMatch_trace_mellin` | `repo_committed_relative` | transports TS116 plus TS95 and TS83 to TS25 through TS115 |

## Remaining work

TS116 does not close the arithmetic front. The next local task is to replace
the unit placeholder diagonal coefficient with the real Selberg/Mobius
coefficient data or prove an equivalent coefficient compatibility theorem.
After that, the remaining arithmetic work is the dense-to-diagonal Selberg
identity, the diagonal square-sum majorant, Selberg's sieve bound, and
Brun-Titchmarsh budget comparison.
