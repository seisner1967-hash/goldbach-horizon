# TS111 Audit - Selberg Dense-To-Diagonal Reindexing Ledger

## Status

`repo_committed_relative`

TS111 opens the finite reindexing layer below the TS110 dense-to-diagonal
identity. It proves a concrete finite expansion of the TS109 diagonal square
side into a triple sum.

This sprint does not prove the Mobius reindexing collapse, divisor-filter
rewrite, gcd/lcm kernel match, dense-to-diagonal identity, square-sum majorant,
Selberg's sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS111/SelbergDenseToDiagonalReindexingLedger.lean
```

## Key declarations

```lean
TS111.Goldbach.selbergDiagonalFilterTerm
TS111.Goldbach.selbergDiagonalTripleTerm
TS111.Goldbach.selbergCanonicalDiagonalTripleExpansion
TS111.Goldbach.selbergDiagonalSquareTerm_triple_expansion
TS111.Goldbach.selbergDiagonalSide_triple_expansion
TS111.Goldbach.SelbergDenseToDiagonalReindexing
TS111.Goldbach.selbergDenseToDiagonalReindexing
TS111.Goldbach.SelbergDenseToDiagonalReindexingTarget
TS111.Goldbach.selbergDenseToDiagonalReindexingTarget
TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructure
TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructureTarget
TS111.Goldbach.denseToDiagonalInfrastructure_of_reindexingInfrastructure
TS111.Goldbach.denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
TS111.Goldbach.diagonalizationInfrastructureTarget_of_reindexingInfrastructureTarget
TS111.Goldbach.mobiusInversionInfrastructureTarget_of_reindexingInfrastructureTarget
TS111.Goldbach.finalHorizonInputsTarget_of_reindexing_trace_mellin
TS111.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_reindexing_trace_mellin
TS111.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_reindexing_trace_mellin
```

## Proof summary

The theorem

```lean
TS111.Goldbach.selbergDiagonalSquareTerm_triple_expansion
```

expands one diagonal square term into a finite double sum using
`Finset.sum_mul_sum`, `Finset.mul_sum`, and ring normalization over `Rat`.

The theorem

```lean
TS111.Goldbach.selbergDiagonalSide_triple_expansion
```

lifts this expansion through the outer finite sum and identifies the canonical
TS109 diagonal side with a triple sum over the same finite support window.

The remaining reindexing and arithmetic-collapse steps are still local
obligations in `SelbergDenseToDiagonalReindexing`.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS111.SelbergDenseToDiagonalReindexingLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS111
rg -n "a[x]iom" TS\Goldbach\Strong\TS111
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS111
git diff --check -- README.md TS\Goldbach\Strong\TS111\SelbergDenseToDiagonalReindexingLedger.lean TS\Goldbach\Strong\TS111\TS111_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS111-R1 | `selbergDiagonalFilterTerm` | `repo_committed` | defines one divisor-filtered diagonal summand |
| TS111-R2 | `selbergCanonicalDiagonalTripleExpansion` | `repo_committed` | defines the expanded triple-sum diagonal side |
| TS111-R3 | `selbergDiagonalSquareTerm_triple_expansion` | `repo_committed` | proves one square term expands to a finite double sum |
| TS111-R4 | `selbergDiagonalSide_triple_expansion` | `repo_committed` | proves the canonical diagonal side expands to the finite triple sum |
| TS111-I1 | `SelbergDenseToDiagonalReindexing` | `repo_committed_relative` | packages the remaining finite reindexing and Mobius-collapse obligations |
| TS111-T1 | `denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget` | `repo_committed_relative` | transports reindexing infrastructure into TS110 |
| TS111-T2 | `paddedScaleAnalyticInfrastructureTarget_of_reindexing_trace_mellin` | `repo_committed_relative` | transports TS111 plus TS95 and TS83 to TS25 through TS110 |

## Remaining work

TS111 does not close the arithmetic front. The remaining work is to prove the
finite sum interchange, divisor-filter rewrite, Mobius-delta collapse, gcd/lcm
kernel match, dense-to-diagonal Selberg identity, diagonal square-sum majorant,
Selberg sieve bound, and Brun-Titchmarsh budget comparison.
