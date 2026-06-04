# TS114 Audit - Selberg Inner GCD Divisor Collapse Ledger

## Status

`repo_committed_relative`

TS114 opens the local inner-collapse layer below the TS113 finite-Fubini
reindexing ledger. It proves that, for each fixed pair `(m,n)`, the TS113
inner gcd-divisor sum factors as

```text
weight m * weight n * localCoefficient(m,n)
```

where `localCoefficient(m,n)` is the remaining finite divisor coefficient over
the gcd filter. It also proves that if this local coefficient is identified
with the canonical dense Selberg kernel `gcd(m,n)/lcm(m,n)`, then the TS113
pair-first side and the full TS112 gcd-filtered side equal the TS110 dense
side.

This sprint does not prove the Mobius coefficient calculation, the dense
kernel match, the dense-to-diagonal identity, square-sum majorant, Selberg's
sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS114/SelbergInnerGcdDivisorCollapseLedger.lean
```

## Key declarations

```lean
TS114.Goldbach.selbergInnerGcdKernelCoefficient
TS114.Goldbach.selbergGcdCollapseTerm_factor
TS114.Goldbach.selbergInnerGcdDivisorSum_factor
TS114.Goldbach.SelbergInnerGcdKernelMatchObligation
TS114.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
TS114.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch
TS114.Goldbach.SelbergInnerGcdDivisorCollapse
TS114.Goldbach.selbergInnerGcdDivisorCollapse
TS114.Goldbach.SelbergInnerGcdDivisorCollapseTarget
TS114.Goldbach.selbergInnerGcdDivisorCollapseTarget
TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructure
TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructureTarget
TS114.Goldbach.fubiniInfrastructure_of_innerCollapseInfrastructure
TS114.Goldbach.fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.mobiusCollapseInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.reindexingInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.mobiusInversionInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.finalHorizonInputsTarget_of_innerCollapse_trace_mellin
TS114.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_innerCollapse_trace_mellin
TS114.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_innerCollapse_trace_mellin
```

## Proof summary

The theorem

```lean
TS114.Goldbach.selbergGcdCollapseTerm_factor
```

splits a single TS113 gcd-collapse term into the external pair weight
`weight m * weight n` and a local divisor coefficient.

The theorem

```lean
TS114.Goldbach.selbergInnerGcdDivisorSum_factor
```

lifts this factorization through the finite inner sum over `d` using
`Finset.mul_sum`.

The theorem

```lean
TS114.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
```

proves that the pair-first TS113 side equals the TS110 dense side whenever the
local coefficient matches the canonical TS107 `gcd/lcm` kernel.

The theorem

```lean
TS114.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch
```

combines the TS113 finite-Fubini equality with that local kernel-match theorem
to close the TS112 gcd-filtered side conditionally.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS114.SelbergInnerGcdDivisorCollapseLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS114
rg -n "a[x]iom" TS\Goldbach\Strong\TS114
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS114
git diff --check -- README.md TS\Goldbach\Strong\TS114\SelbergInnerGcdDivisorCollapseLedger.lean TS\Goldbach\Strong\TS114\TS114_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS114-R1 | `selbergGcdCollapseTerm_factor` | `repo_committed` | factors one gcd-collapse term into pair weight and local coefficient |
| TS114-R2 | `selbergInnerGcdDivisorSum_factor` | `repo_committed` | factors the inner divisor sum using finite distributivity |
| TS114-R3 | `selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch` | `repo_committed_relative` | proves pair-first equals dense under the local kernel-match obligation |
| TS114-R4 | `selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch` | `repo_committed_relative` | proves the TS112 gcd-filtered side equals dense under the local kernel-match obligation |
| TS114-I1 | `SelbergInnerGcdKernelMatchObligation` | `repo_committed_relative` | names the remaining Mobius coefficient match to the canonical `gcd/lcm` kernel |
| TS114-I2 | `SelbergInnerGcdDivisorCollapse` | `repo_committed_relative` | packages local factorization plus the remaining coefficient-collapse obligation |
| TS114-T1 | `fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget` | `repo_committed_relative` | transports TS114 infrastructure into TS113 |
| TS114-T2 | `paddedScaleAnalyticInfrastructureTarget_of_innerCollapse_trace_mellin` | `repo_committed_relative` | transports TS114 plus TS95 and TS83 to TS25 through TS113 |

## Remaining work

TS114 does not close the arithmetic front. The next local task is to prove the
Mobius coefficient calculation identifying `selbergInnerGcdKernelCoefficient`
with the canonical dense `gcd/lcm` kernel. After that, the remaining
arithmetic work is the dense-to-diagonal Selberg identity, the diagonal
square-sum majorant, Selberg's sieve bound, and Brun-Titchmarsh budget
comparison.
