# TS137 Audit - Concrete Selberg Interval Majorant Interface

## Scope

TS137 adds:

```text
TS/Goldbach/Strong/TS137/ConcreteSelbergIntervalMajorantInterface.lean
```

It defines a concrete analytic interface for the interval majorant inputs
required by TS30/TS136.

## Concrete declarations

TS137 defines:

```lean
TS137.Goldbach.ConcreteSelbergIntervalMajorantData
TS137.Goldbach.concreteSelbergIntervalMajorant
TS137.Goldbach.ConcreteSelbergIntervalMajorantProofs
TS137.Goldbach.concreteSelbergSieveIntervalBound
TS137.Goldbach.concreteSelbergMajorantBudgetComparison
TS137.Goldbach.ConcreteSelbergIntervalMajorantLedger
TS137.Goldbach.concreteSelbergIntervalMajorantLedger
TS137.Goldbach.ConcreteSelbergIntervalMajorantBridgeTarget
TS137.Goldbach.ConcreteSelbergIntervalMajorantLedgerTarget
```

TS137 proves:

```lean
TS137.Goldbach.selbergSieveWeightInfrastructure_of_concreteIntervalMajorant
TS137.Goldbach.brunTitchmarshFinalInputLedger_of_concreteIntervalMajorant
TS137.Goldbach.concreteSelbergIntervalMajorantBridgeTarget
TS137.Goldbach.selbergSieveWeightInfrastructureTarget_of_concreteIntervalMajorantTarget
TS137.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_concreteIntervalMajorantTarget
TS137.Goldbach.selbergIntervalMajorantFromOptimalBudgetBridgeTarget
```

## Meaning

TS136 says that the finite optimal Selberg weights feed TS99/TS97 once the
TS30 interval objects are supplied. TS137 names the concrete data and proof
obligations for those objects.

The concrete data contain:

```text
level
majorantValue : Nat -> Nat -> Nat -> Nat
mainTerm      : Nat -> Nat -> Nat -> Rat
errorTerm     : Nat -> Nat -> Nat -> Rat
majorantRat   : Nat -> Nat -> Nat -> Rat
majorantRat = mainTerm + errorTerm
0 <= errorTerm
```

The proof package contains exactly the two interval facts required by TS30:

```text
primeIntervalCard <= majorantValue
majorantValue <= brunTitchmarshCeilBudget
```

From these fields, TS137 constructs:

```text
TS30.SelbergIntervalMajorant
TS30.SelbergSieveIntervalBound
TS30.SelbergMajorantBudgetComparison
TS136.SelbergIntervalMajorantFromOptimalBudget
TS99.SelbergSieveWeightInfrastructure
TS97.BrunTitchmarshFinalInputLedger
```

Thus the next analytic target is fully named: prove the concrete interval
sieve bound and the budget comparison for a chosen `majorantValue`.

## What TS137 does not prove

TS137 does not yet prove:

- the concrete interval sieve estimate;
- the comparison with the TS22 Brun-Titchmarsh ceiling;
- denominator asymptotics;
- Brun-Titchmarsh itself;
- the spectral trace package;
- the Mellin-tail package;
- any prime-counting estimate.

These remain explicit fields in `ConcreteSelbergIntervalMajorantProofs`.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS137/ConcreteSelbergIntervalMajorantInterface.lean
lake build TS.Goldbach.Strong.TS137.ConcreteSelbergIntervalMajorantInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS137
git diff --check -- TS\Goldbach\Strong\TS137 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS137.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the interval sieve estimate and budget
comparison remain the analytic TS30 obligations.
