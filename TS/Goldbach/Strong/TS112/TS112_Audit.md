# TS112 Audit - Selberg Mobius Collapse Ledger

## Status

`repo_committed_relative`

TS112 opens the Mobius-collapse layer below the TS111 reindexing ledger. It
proves concrete divisor-filter rewrites needed before the dense-to-diagonal
Selberg identity:

- the product of two TS111 divisor filters is a pair-divisibility filter;
- the pair-divisibility filter is a single filter on `Nat.gcd`;
- the TS111 diagonal triple expansion rewrites to a gcd-filtered triple sum.

This sprint does not prove the full finite-sum interchange, Mobius-delta
collapse, dense-kernel match, dense-to-diagonal identity, square-sum majorant,
Selberg's sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS112/SelbergMobiusCollapseLedger.lean
```

## Key declarations

```lean
TS112.Goldbach.selbergDivisorPairFilter
TS112.Goldbach.selbergGcdFilterTerm
TS112.Goldbach.selbergDiagonalFilterTerm_mul_eq_pairFilter
TS112.Goldbach.selbergDivisorPairFilter_eq_gcdFilter
TS112.Goldbach.selbergDiagonalTripleTerm_eq_gcdFilter
TS112.Goldbach.selbergCanonicalGcdCollapseExpansion
TS112.Goldbach.selbergCanonicalDiagonalTripleExpansion_eq_gcdCollapseExpansion
TS112.Goldbach.SelbergMobiusCollapse
TS112.Goldbach.selbergMobiusCollapse
TS112.Goldbach.selbergMobiusCollapse_obligation_eq
TS112.Goldbach.SelbergMobiusCollapseTarget
TS112.Goldbach.selbergMobiusCollapseTarget
TS112.Goldbach.SelbergMobiusCollapseInfrastructure
TS112.Goldbach.SelbergMobiusCollapseInfrastructureTarget
TS112.Goldbach.reindexingInfrastructure_of_mobiusCollapseInfrastructure
TS112.Goldbach.reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
TS112.Goldbach.denseToDiagonalInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
TS112.Goldbach.mobiusInversionInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
TS112.Goldbach.finalHorizonInputsTarget_of_mobiusCollapse_trace_mellin
TS112.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobiusCollapse_trace_mellin
TS112.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobiusCollapse_trace_mellin
```

## Proof summary

The theorem

```lean
TS112.Goldbach.selbergDiagonalFilterTerm_mul_eq_pairFilter
```

proves the product of two divisor-filtered TS111 terms is exactly an
`if`-encoded pair-divisibility filter.

The theorem

```lean
TS112.Goldbach.selbergDivisorPairFilter_eq_gcdFilter
```

uses `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, and `Nat.dvd_gcd` to rewrite that
pair filter as a single divisibility filter on `Nat.gcd`.

The theorem

```lean
TS112.Goldbach.selbergCanonicalDiagonalTripleExpansion_eq_gcdCollapseExpansion
```

lifts the gcd-filter rewrite through the finite TS111 triple sum.

The remaining Mobius collapse and dense-kernel matching steps are still local
obligations in `SelbergMobiusCollapse`.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS112.SelbergMobiusCollapseLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS112
rg -n "a[x]iom" TS\Goldbach\Strong\TS112
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS112
git diff --check -- README.md TS\Goldbach\Strong\TS112\SelbergMobiusCollapseLedger.lean TS\Goldbach\Strong\TS112\TS112_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS112-R1 | `selbergDiagonalFilterTerm_mul_eq_pairFilter` | `repo_committed` | proves product of two divisor filters is a pair filter |
| TS112-R2 | `selbergDivisorPairFilter_eq_gcdFilter` | `repo_committed` | proves the pair filter equals the gcd filter |
| TS112-R3 | `selbergDiagonalTripleTerm_eq_gcdFilter` | `repo_committed` | rewrites one TS111 triple term through the gcd filter |
| TS112-R4 | `selbergCanonicalDiagonalTripleExpansion_eq_gcdCollapseExpansion` | `repo_committed` | lifts the gcd-filter rewrite through the finite triple sum |
| TS112-I1 | `SelbergMobiusCollapse` | `repo_committed_relative` | packages the remaining Mobius collapse and dense-kernel match obligations |
| TS112-T1 | `reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget` | `repo_committed_relative` | transports collapse infrastructure into TS111 |
| TS112-T2 | `paddedScaleAnalyticInfrastructureTarget_of_mobiusCollapse_trace_mellin` | `repo_committed_relative` | transports TS112 plus TS95 and TS83 to TS25 through TS111 |

## Remaining work

TS112 does not close the arithmetic front. The remaining work is to prove the
finite sum interchange, Mobius-delta collapse, dense-kernel match,
dense-to-diagonal Selberg identity, diagonal square-sum majorant, Selberg
sieve bound, and Brun-Titchmarsh budget comparison.
