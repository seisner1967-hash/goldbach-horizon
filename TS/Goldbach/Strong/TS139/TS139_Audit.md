# TS139 Audit - Concrete Selberg Interval Sieve Theorem Ledger

## Scope

TS139 adds:

```text
TS/Goldbach/Strong/TS139/ConcreteSelbergIntervalSieveTheoremLedger.lean
```

It proves the finite counting bridge for the concrete TS138 square majorant:
if every prime in the TS22 interval contributes at least `1` to the Selberg
square bracket, then the TS138 ceiling majorant bounds the interval prime
count.

## Concrete declarations

TS139 defines:

```lean
TS139.Goldbach.SelbergConcretePrimePointwiseMajorant
TS139.Goldbach.ConcreteSelbergIntervalSieveTheorem
TS139.Goldbach.ConcreteSelbergSquareBudgetComparison
TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremLedger
TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremBridgeTarget
```

TS139 proves:

```lean
TS139.Goldbach.finset_card_filter_cast_le_sum_of_pointwise
TS139.Goldbach.primeIntervalCard_cast_le_squareMajorantRat_of_pointwise
TS139.Goldbach.primeIntervalCard_le_concreteMajorantValue_of_pointwise
TS139.Goldbach.selbergConcretePrimePointwiseMajorant_of_weight_eq_one
TS139.Goldbach.concreteSelbergSieveIntervalBound
TS139.Goldbach.concreteSelbergSquareMajorantProofs
TS139.Goldbach.concreteSelbergIntervalSieveTheoremLedger
TS139.Goldbach.concreteSelbergIntervalSieveTheoremBridgeTarget
TS139.Goldbach.selbergSieveWeightInfrastructure_of_intervalSieveTheorem
TS139.Goldbach.brunTitchmarshFinalInputLedger_of_intervalSieveTheorem
TS139.Goldbach.selbergSieveWeightInfrastructureTarget_of_intervalSieveTheoremTarget
TS139.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_intervalSieveTheoremTarget
TS139.Goldbach.concreteSelbergSquareMajorantBridgeTarget
```

## Meaning

TS138 defines the concrete square majorant:

```text
sum_{k in [n,n+h]} (sum_{d in support, d | k} lambda_d)^2
```

TS139 proves that the TS22 prime count is bounded by the ceiling of this square
sum if the following pointwise prime input is available:

```text
for every prime k in [n,n+h],
  1 <= (sum_{d in support, d | k} lambda_d)^2
```

The proof is purely finite:

```text
card {k in interval | prime k}
<= sum_{k in interval} (square bracket at k)
<= ceiling of the rational square sum
```

The first inequality uses a generic finite counting lemma
`finset_card_filter_cast_le_sum_of_pointwise`.  The second uses `Nat.le_ceil`.

## Remaining analytic obligations

TS139 deliberately does not assert that the pointwise prime lower-bound is
automatic for every TS22 prime.  In the usual Selberg sieve, this requires an
admissibility relation between the support level and the primes being counted
or a separate treatment of small primes.

The remaining local inputs are:

```text
pointwise_prime_square_lower_bound
selbergConcreteMajorantValue <= brunTitchmarshCeilBudget
```

When both are supplied, TS139 builds the TS138 square-majorant proof package,
then feeds TS99 and TS97.

## What TS139 does not prove

TS139 does not yet prove:

- the pointwise prime admissibility condition for the optimal weights;
- the Brun-Titchmarsh budget comparison;
- denominator asymptotics;
- Brun-Titchmarsh itself;
- the spectral trace package;
- the Mellin-tail package.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS139/ConcreteSelbergIntervalSieveTheoremLedger.lean
lake build TS.Goldbach.Strong.TS139.ConcreteSelbergIntervalSieveTheoremLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS139
git diff --check -- TS\Goldbach\Strong\TS139 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS139.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because pointwise prime admissibility and the
Brun-Titchmarsh budget comparison remain analytic obligations.
