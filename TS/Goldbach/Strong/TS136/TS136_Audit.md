# TS136 Audit - Selberg Interval Majorant Ledger

## Scope

TS136 adds:

```text
TS/Goldbach/Strong/TS136/SelbergIntervalMajorantLedger.lean
```

It connects the finite optimal Selberg weights from TS135 to the existing
interval-majorant interfaces from TS30/TS99.

## Concrete declarations

TS136 proves:

```lean
TS136.Goldbach.selbergOptimalIntervalWeight_support_bound
TS136.Goldbach.selbergOptimalIntervalWeight_one
TS136.Goldbach.selbergOptimalIntervalWeight_dense_budget_exact
TS136.Goldbach.selbergSieveWeightInfrastructure_of_intervalMajorant
TS136.Goldbach.brunTitchmarshFinalInputLedger_of_intervalMajorant
TS136.Goldbach.selbergIntervalMajorantFromOptimalBudgetBridgeTarget
TS136.Goldbach.selbergSieveWeightInfrastructureTarget_of_intervalMajorantTarget
TS136.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_intervalMajorantTarget
TS136.Goldbach.selbergFiniteMobiusReconstructionExpansionDischargeTarget
```

TS136 defines:

```lean
TS136.Goldbach.selbergOptimalIntervalWeight
TS136.Goldbach.selbergOptimalSieveWeightLedger
TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudget
TS136.Goldbach.selbergIntervalMajorantFromOptimalBudget
TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudgetBridgeTarget
TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudgetTarget
```

## Meaning

TS135 proves that the reconstructed optimal weights attain the exact dense-side
budget:

```text
TS110 dense side = 1 / TS122 optimization denominator.
```

TS136 packages those reconstructed weights as the raw Selberg weight ledger
expected by TS99. It proves:

```text
support(weight) <= level
weight(1) = 1
```

for positive `level`. The second identity follows by evaluating the Mobius
reconstruction formula at `m = 1`, where it becomes exactly the TS128 Mobius
linear constraint.

Once a concrete TS30 interval majorant, sieve bound, and budget comparison are
provided, TS136 builds:

```text
TS129.SelbergSieveMajorantFromDiagonalBudget
TS99.SelbergSieveWeightInfrastructure
TS97.BrunTitchmarshFinalInputLedger
```

Thus the finite Selberg algebra is now wired to the high-level interval
Selberg/Brun-Titchmarsh interfaces.

## What TS136 does not prove

TS136 does not yet prove:

- a concrete interval majorant;
- the Selberg sieve interval theorem;
- the comparison of that majorant with the TS22 Brun-Titchmarsh ceiling;
- Brun-Titchmarsh itself;
- the spectral trace package;
- the Mellin-tail package;
- any prime-counting estimate.

These remain explicit fields in the TS30/TS99 interface.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS136/SelbergIntervalMajorantLedger.lean
lake build TS.Goldbach.Strong.TS136.SelbergIntervalMajorantLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS136
git diff --check -- TS\Goldbach\Strong\TS136 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS136.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the concrete interval majorant, interval sieve
theorem, and majorant-budget comparison remain external TS30 obligations.
