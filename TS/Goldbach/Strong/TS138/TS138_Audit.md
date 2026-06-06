# TS138 Audit - Concrete Selberg Interval Majorant Formulation

## Scope

TS138 adds:

```text
TS/Goldbach/Strong/TS138/ConcreteSelbergIntervalMajorantFormulation.lean
```

It instantiates the data side of the TS137 interval-majorant interface with a
concrete finite Selberg square majorant built from the TS136 optimal
reconstructed weights.

## Concrete declarations

TS138 defines:

```lean
TS138.Goldbach.selbergConcreteInterval
TS138.Goldbach.selbergConcreteDivisorWeight
TS138.Goldbach.selbergConcreteSquareMajorantRat
TS138.Goldbach.selbergConcreteMajorantValue
TS138.Goldbach.selbergConcreteMainTerm
TS138.Goldbach.selbergConcreteErrorTerm
TS138.Goldbach.selbergConcreteMajorantRat
TS138.Goldbach.concreteSelbergIntervalMajorantData
TS138.Goldbach.ConcreteSelbergSquareMajorantProofs
TS138.Goldbach.concreteSelbergIntervalMajorantProofs
TS138.Goldbach.ConcreteSelbergSquareMajorantLedger
TS138.Goldbach.concreteSelbergSquareMajorantLedger
TS138.Goldbach.ConcreteSelbergSquareMajorantBridgeTarget
```

TS138 proves:

```lean
TS138.Goldbach.selbergConcreteMajorantRat_formula
TS138.Goldbach.selbergConcreteErrorTerm_nonnegative
TS138.Goldbach.concreteSelbergSquareMajorantBridgeTarget
TS138.Goldbach.selbergSieveWeightInfrastructure_of_squareMajorant
TS138.Goldbach.brunTitchmarshFinalInputLedger_of_squareMajorant
TS138.Goldbach.selbergSieveWeightInfrastructureTarget_of_squareMajorantTarget
TS138.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_squareMajorantTarget
TS138.Goldbach.primeIntervalCard_le_concreteInterval_card
TS138.Goldbach.concreteSelbergIntervalMajorantBridgeTarget
```

## Meaning

TS137 names the abstract concrete interval-majorant data:

```text
majorantValue : Nat -> Nat -> Nat -> Nat
mainTerm      : Nat -> Nat -> Nat -> Rat
errorTerm     : Nat -> Nat -> Nat -> Rat
majorantRat   : Nat -> Nat -> Nat -> Rat
```

TS138 supplies a specific finite Selberg square formula:

```text
sum_{n <= k <= n + h}
  (sum_{d in support, d | k} lambda_d)^2
```

where `lambda_d` is the optimal reconstructed Selberg weight from TS136.
The natural TS30 majorant is the ceiling of this rational square sum.

The rational decomposition recorded in TS137 is deliberately minimal:

```text
mainTerm    = square sum
errorTerm   = 0
majorantRat = square sum
```

This proves the data-side formula and nonnegative error term without importing
any new analytic estimate.

## Remaining analytic obligations

For this explicit square majorant, TS138 leaves exactly the two TS137 proof
fields:

```text
primeIntervalCard <= selbergConcreteMajorantValue
selbergConcreteMajorantValue <= brunTitchmarshCeilBudget
```

These are bundled in `ConcreteSelbergSquareMajorantProofs`.  Once supplied,
TS138 constructs the TS137 ledger and therefore feeds the TS99 Selberg weight
infrastructure and the TS97 final Brun-Titchmarsh input ledger.

TS138 also proves a sanity lemma:

```text
primeIntervalCard <= cardinality of the ambient interval
```

This confirms that the TS22 prime-counting window is the same finite interval
used by the concrete square-majorant formula.  It is not the Selberg sieve
theorem.

## What TS138 does not prove

TS138 does not yet prove:

- the Selberg interval sieve theorem for the square majorant;
- the comparison with the TS22 Brun-Titchmarsh ceiling;
- denominator asymptotics;
- Brun-Titchmarsh itself;
- the spectral trace package;
- the Mellin-tail package;
- any final prime-counting theorem.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS138/ConcreteSelbergIntervalMajorantFormulation.lean
lake build TS.Goldbach.Strong.TS138.ConcreteSelbergIntervalMajorantFormulation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS138
git diff --check -- TS\Goldbach\Strong\TS138 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS138.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the interval sieve estimate and the
Brun-Titchmarsh budget comparison remain the analytic TS30 obligations.
