# TS113 Audit - Selberg Finite Fubini Reindexing Ledger

## Status

`repo_committed_relative`

TS113 opens the finite-Fubini layer below the TS112 Mobius-collapse ledger. It
proves that the TS112 gcd-filtered triple sum can be reordered from
diagonal-first order

```text
sum d, sum m, sum n, term d m n
```

to pair-first order

```text
sum m, sum n, sum d, term d m n
```

using finite `Finset.sum_comm`. It also isolates the inner gcd-divisor sum for
each pair `(m,n)`.

This sprint does not prove the Mobius-delta collapse of the inner sum, the
dense-kernel match, the dense-to-diagonal identity, square-sum majorant,
Selberg's sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS113/SelbergFiniteFubiniReindexingLedger.lean
```

## Key declarations

```lean
TS113.Goldbach.selbergGcdCollapseTerm
TS113.Goldbach.selbergGcdCollapseTripleSum
TS113.Goldbach.selbergInnerGcdDivisorSum
TS113.Goldbach.selbergPairFirstGcdCollapseSum
TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_tripleSum
TS113.Goldbach.selbergGcdCollapseTripleSum_reordered
TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_pairFirst
TS113.Goldbach.InnerGcdDivisorCollapseReady
TS113.Goldbach.innerGcdDivisorCollapseReady
TS113.Goldbach.SelbergFiniteFubiniReindexing
TS113.Goldbach.selbergFiniteFubiniReindexing
TS113.Goldbach.SelbergFiniteFubiniReindexingTarget
TS113.Goldbach.selbergFiniteFubiniReindexingTarget
TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructure
TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructureTarget
TS113.Goldbach.mobiusCollapseInfrastructure_of_fubiniInfrastructure
TS113.Goldbach.mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
TS113.Goldbach.reindexingInfrastructureTarget_of_fubiniInfrastructureTarget
TS113.Goldbach.mobiusInversionInfrastructureTarget_of_fubiniInfrastructureTarget
TS113.Goldbach.finalHorizonInputsTarget_of_fubini_trace_mellin
TS113.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_fubini_trace_mellin
TS113.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_fubini_trace_mellin
```

## Proof summary

The theorem

```lean
TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_tripleSum
```

identifies the TS112 gcd-filtered expansion with the TS113 diagonal-first
triple sum.

The theorem

```lean
TS113.Goldbach.selbergGcdCollapseTripleSum_reordered
```

uses `Finset.sum_comm` twice to reorder

```text
sum d, sum m, sum n
```

into

```text
sum m, sum n, sum d
```

over the same finite support.

The theorem

```lean
TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_pairFirst
```

combines those facts and exposes the inner divisor sum ready for the future
Mobius-delta collapse.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS113.SelbergFiniteFubiniReindexingLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS113
rg -n "a[x]iom" TS\Goldbach\Strong\TS113
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS113
git diff --check -- README.md TS\Goldbach\Strong\TS113\SelbergFiniteFubiniReindexingLedger.lean TS\Goldbach\Strong\TS113\TS113_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS113-R1 | `selbergCanonicalGcdCollapseExpansion_eq_tripleSum` | `repo_committed` | identifies the TS112 gcd expansion with the TS113 triple sum |
| TS113-R2 | `selbergGcdCollapseTripleSum_reordered` | `repo_committed` | proves finite Fubini from diagonal-first to pair-first order |
| TS113-R3 | `selbergCanonicalGcdCollapseExpansion_eq_pairFirst` | `repo_committed` | exposes the pair-first inner gcd-divisor sum |
| TS113-I1 | `InnerGcdDivisorCollapseReady` | `repo_committed_relative` | packages the local inner-sum Mobius collapse obligation for one pair |
| TS113-I2 | `SelbergFiniteFubiniReindexing` | `repo_committed_relative` | packages finite Fubini plus remaining inner collapse obligations |
| TS113-T1 | `mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget` | `repo_committed_relative` | transports finite-Fubini infrastructure into TS112 |
| TS113-T2 | `paddedScaleAnalyticInfrastructureTarget_of_fubini_trace_mellin` | `repo_committed_relative` | transports TS113 plus TS95 and TS83 to TS25 through TS112 |

## Remaining work

TS113 does not close the arithmetic front. The remaining work is to prove the
Mobius-delta collapse of the inner gcd-divisor sums, match the resulting factor
with the dense `gcd/lcm` kernel, prove the dense-to-diagonal Selberg identity,
then prove the diagonal square-sum majorant, Selberg sieve bound, and
Brun-Titchmarsh budget comparison.
