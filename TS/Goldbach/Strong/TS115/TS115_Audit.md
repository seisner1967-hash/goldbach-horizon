# TS115 Audit - Selberg Mobius Coefficient Ledger

## Status

`repo_committed_relative`

TS115 opens the one-variable coefficient layer below the TS114 inner
gcd-divisor collapse ledger. It proves that the TS114 local coefficient for a
pair `(m,n)` depends on that pair only through `Nat.gcd m n`, rewrites this
coefficient as a filtered finite sum over the diagonal support, and records the
remaining coefficient-to-kernel match as the exact local arithmetic
obligation.

This sprint does not prove the Mobius coefficient calculation, the dense
kernel match, the dense-to-diagonal identity, square-sum majorant, Selberg's
sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS115/SelbergMobiusCoefficientLedger.lean
```

## Key declarations

```lean
TS115.Goldbach.selbergGcdCoefficientSupport
TS115.Goldbach.selbergGcdCoefficient
TS115.Goldbach.selbergInnerGcdKernelCoefficient_eq_gcdCoefficient
TS115.Goldbach.selbergGcdCoefficient_eq_filter_sum
TS115.Goldbach.SelbergGcdCoefficientKernelMatchObligation
TS115.Goldbach.innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
TS115.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_gcdCoefficientKernelMatch
TS115.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch
TS115.Goldbach.SelbergMobiusCoefficient
TS115.Goldbach.selbergMobiusCoefficient
TS115.Goldbach.SelbergMobiusCoefficientTarget
TS115.Goldbach.selbergMobiusCoefficientTarget
TS115.Goldbach.SelbergMobiusCoefficientInfrastructure
TS115.Goldbach.SelbergMobiusCoefficientInfrastructureTarget
TS115.Goldbach.innerCollapseInfrastructure_of_coefficientInfrastructure
TS115.Goldbach.innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.fubiniInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.mobiusCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.mobiusInversionInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.finalHorizonInputsTarget_of_coefficient_trace_mellin
TS115.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_coefficient_trace_mellin
TS115.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_coefficient_trace_mellin
```

## Proof summary

The theorem

```lean
TS115.Goldbach.selbergInnerGcdKernelCoefficient_eq_gcdCoefficient
```

identifies the TS114 local coefficient with a one-variable coefficient
evaluated at `Nat.gcd m n`.

The theorem

```lean
TS115.Goldbach.selbergGcdCoefficient_eq_filter_sum
```

rewrites the one-variable coefficient as a finite sum over
`selbergGcdCoefficientSupport level g`, using `Finset.sum_filter`.

The theorem

```lean
TS115.Goldbach.innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
```

proves that the TS115 coefficient-kernel obligation supplies the TS114 local
kernel-match obligation.

The theorems

```lean
TS115.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_gcdCoefficientKernelMatch
TS115.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch
```

propagate that coefficient match through TS114 to the pair-first and
gcd-filtered dense-side equalities.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS115.SelbergMobiusCoefficientLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS115
rg -n "a[x]iom" TS\Goldbach\Strong\TS115
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS115
git diff --check -- README.md TS\Goldbach\Strong\TS115\SelbergMobiusCoefficientLedger.lean TS\Goldbach\Strong\TS115\TS115_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS115-R1 | `selbergInnerGcdKernelCoefficient_eq_gcdCoefficient` | `repo_committed` | reduces the TS114 local coefficient to a one-variable gcd coefficient |
| TS115-R2 | `selbergGcdCoefficient_eq_filter_sum` | `repo_committed` | rewrites the coefficient as a filtered finite divisor sum |
| TS115-R3 | `innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch` | `repo_committed_relative` | transports the coefficient match into the TS114 local kernel match |
| TS115-R4 | `selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch` | `repo_committed_relative` | proves the TS112 gcd-filtered side equals dense under the coefficient-match obligation |
| TS115-I1 | `SelbergGcdCoefficientKernelMatchObligation` | `repo_committed_relative` | names the remaining local coefficient identity against the canonical `gcd/lcm` kernel |
| TS115-I2 | `SelbergMobiusCoefficient` | `repo_committed_relative` | packages one-variable coefficient reduction plus the remaining coefficient-collapse obligation |
| TS115-T1 | `innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget` | `repo_committed_relative` | transports TS115 infrastructure into TS114 |
| TS115-T2 | `paddedScaleAnalyticInfrastructureTarget_of_coefficient_trace_mellin` | `repo_committed_relative` | transports TS115 plus TS95 and TS83 to TS25 through TS114 |

## Remaining work

TS115 does not close the arithmetic front. The next local task is to prove the
coefficient-kernel identity recorded by
`SelbergGcdCoefficientKernelMatchObligation`. After that, the remaining
arithmetic work is the dense-to-diagonal Selberg identity, the diagonal
square-sum majorant, Selberg's sieve bound, and Brun-Titchmarsh budget
comparison.
