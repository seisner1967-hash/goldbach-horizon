# TS140 Audit - Large Prime Admissibility

## Scope

TS140 adds:

```text
TS/Goldbach/Strong/TS140/LargePrimeAdmissibility.lean
```

It proves the large-prime admissibility input for the concrete TS139 interval
sieve theorem.  If every prime in the TS22 interval is strictly larger than the
Selberg support level, then the TS138 divisor bracket is exactly `lambda_1`,
and TS136 has already proved `lambda_1 = 1`.

## Concrete declarations

TS140 defines:

```lean
TS140.Goldbach.LargePrimeSupportAdmissibility
TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem
TS140.Goldbach.LargePrimeAdmissibilityLedger
TS140.Goldbach.LargePrimeAdmissibilityBridgeTarget
```

TS140 proves:

```lean
TS140.Goldbach.selbergOptimizationSupport_mem_le_level
TS140.Goldbach.selbergOptimizationSupport_mem_pos
TS140.Goldbach.support_divisor_eq_one_of_prime_gt_level
TS140.Goldbach.selbergConcreteDivisorWeight_eq_one_of_prime_gt_level
TS140.Goldbach.selbergConcretePrimePointwiseMajorant_of_largePrimeSupport
TS140.Goldbach.largePrimeSupportAdmissibility_of_level_lt_leftEndpoint
TS140.Goldbach.selbergConcretePrimePointwiseMajorant_of_level_lt_leftEndpoint
TS140.Goldbach.primeIntervalCard_le_concreteMajorantValue_of_level_lt_leftEndpoint
TS140.Goldbach.concreteSelbergIntervalSieveTheorem
TS140.Goldbach.largePrimeAdmissibilityLedger
TS140.Goldbach.largePrimeAdmissibilityBridgeTarget
TS140.Goldbach.concreteSelbergIntervalSieveTheoremBridgeTarget
```

## Meaning

TS139 left the pointwise prime input:

```text
for every prime k in the interval,
  1 <= (sum_{d in support, d | k} lambda_d)^2
```

TS140 proves that this input follows from the large-prime support condition:

```text
for every prime k in the interval,
  level < k
```

The proof is finite and arithmetical:

```text
d in support -> d <= level
level < k -> d < k
k prime and d | k -> d = 1 or d = k
d < k excludes d = k
therefore the only support divisor is d = 1
```

Since TS136 proves the optimal reconstructed weight at `1` is `1`, the TS138
divisor bracket is `1`, and its square is also `1`.

TS140 also provides a convenient sufficient condition:

```text
level < n
```

because every `k` in the interval `[n, n + h]` satisfies `n <= k`.

## Remaining analytic obligations

TS140 closes the pointwise prime admissibility route under the large-prime
interval condition.  It does not prove that the chosen global interval
parameters always satisfy `level < n`; this is recorded as
`left_endpoint_large_obligation`.

The Brun-Titchmarsh budget comparison remains separate:

```text
selbergConcreteMajorantValue <= brunTitchmarshCeilBudget
```

## What TS140 does not prove

TS140 does not prove:

- the Brun-Titchmarsh budget comparison;
- denominator asymptotics;
- Brun-Titchmarsh itself;
- treatment of small primes `k <= level`;
- the spectral trace package;
- the Mellin-tail package.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS140/LargePrimeAdmissibility.lean
lake build TS.Goldbach.Strong.TS140.LargePrimeAdmissibility
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS140
git diff --check -- TS\Goldbach\Strong\TS140 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS140.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because `level < n` for the intended interval family
and the Brun-Titchmarsh budget comparison remain separate analytic inputs.
