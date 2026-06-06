# TS141 Audit - Concrete Selberg Square Majorant Expansion

## Scope

TS141 adds:

```text
TS/Goldbach/Strong/TS141/ConcreteSelbergSquareMajorantExpansion.lean
```

It expands the concrete TS138 Selberg square majorant from interval-first form
to pair-first lcm form.

## Concrete declarations

TS141 defines:

```lean
TS141.Goldbach.selbergConcreteDivisorTerm
TS141.Goldbach.selbergConcretePairTerm
TS141.Goldbach.selbergConcreteLcmMultiplicity
TS141.Goldbach.selbergConcreteLcmExpandedMajorantRat
TS141.Goldbach.ConcreteSelbergSquareMajorantExpansionLedger
TS141.Goldbach.ConcreteSelbergSquareMajorantExpansionBridgeTarget
```

TS141 proves:

```lean
TS141.Goldbach.selbergConcreteDivisorWeight_eq_sum_divisorTerm
TS141.Goldbach.selbergConcreteDivisorWeight_sq_expand_double
TS141.Goldbach.selbergConcreteSquareMajorantRat_expand_pairFirst
TS141.Goldbach.divisorPair_filter_eq_lcm_filter
TS141.Goldbach.selbergConcretePairTerm_eq_lcmIndicator
TS141.Goldbach.selbergConcretePairSum_eq_lcmMultiplicity
TS141.Goldbach.selbergConcreteSquareMajorantRat_expand_lcm
TS141.Goldbach.concreteSelbergSquareMajorantExpansionLedger
TS141.Goldbach.concreteSelbergSquareMajorantExpansionBridgeTarget
TS141.Goldbach.largePrimeAdmissibilityBridgeTarget
```

## Meaning

TS138 defines:

```text
sum_{k in interval} (sum_{d in support, d | k} lambda_d)^2
```

TS141 proves the exact finite expansion:

```text
sum_{d1 in support} sum_{d2 in support}
  lambda_d1 * lambda_d2 *
    #{k in interval | lcm(d1,d2) | k}
```

The proof is purely finite:

```text
(sum_d a_d)^2 = sum_d1 sum_d2 a_d1 * a_d2
sum_k sum_d1 sum_d2 = sum_d1 sum_d2 sum_k
d1 | k and d2 | k <-> lcm(d1,d2) | k
```

## Remaining analytic obligations

TS141 does not estimate the lcm multiplicity count:

```text
#{k in [n,n+h] | lcm(d1,d2) | k}
```

The next analytic-arithmetic step is to compare this count with an interval
main term and a remainder term, then use that comparison for the
Brun-Titchmarsh budget bound.

## What TS141 does not prove

TS141 does not prove:

- an upper bound for the lcm multiple count in the interval;
- the main-term plus remainder decomposition;
- the Brun-Titchmarsh budget comparison;
- denominator asymptotics;
- Brun-Titchmarsh itself;
- the spectral trace package;
- the Mellin-tail package.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS141/ConcreteSelbergSquareMajorantExpansion.lean
lake build TS.Goldbach.Strong.TS141.ConcreteSelbergSquareMajorantExpansion
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS141
git diff --check -- TS\Goldbach\Strong\TS141 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS141.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the lcm multiple-count estimate and the
Brun-Titchmarsh budget comparison remain separate analytic inputs.
