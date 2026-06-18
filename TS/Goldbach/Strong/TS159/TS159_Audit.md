# TS159 Audit - Selberg Denominator Refactor Interface

## Status

`repo_committed`

TS159 opens the post-obstruction refactor interface after TS158.  It does not
alter the current Selberg/Brun-Titchmarsh route; instead it defines the data
that any replacement denominator must provide and proves that the legacy
TS122 Jordan-two denominator cannot satisfy a growth interface requiring a
positive-level lower bound at least `2`.

## New interface

TS159 introduces:

```lean
TS159.Goldbach.SelbergDenominatorGrowthRegime
TS159.Goldbach.SelbergGrowingDenominatorData
TS159.Goldbach.RefactoredSelbergBTComparisonRoute
TS159.Goldbach.SelbergGrowingDenominatorDataSatisfiedBy
```

The `SelbergGrowingDenominatorData` structure separates:

```text
denominator : Nat -> Rat
requiredGrowth : Nat -> Rat
positivity on positive levels
lower_bound on the selected growth regime
```

The refactored route asks a future denominator to make the refined Selberg
budget fit under the TS22 `brunTitchmarshCeilBudget`.

## Legacy diagnostic

The central theorem is:

```lean
TS159.Goldbach.current_jordanTwo_denominator_not_growing
```

It states that if a required-growth curve satisfies

```text
2 <= requiredGrowth(level)
```

for every positive level, then the current TS122 denominator cannot realize
that growth interface.

The proof instantiates the interface at `level = 1`.  The interface would
force:

```text
2 <= TS122.selbergOptimizationDenominator 1
```

whereas TS154 proves:

```text
TS122.selbergOptimizationDenominator 1 < 2
```

This closes the diagnostic without any new analytic estimate.

## Refactor ledger

TS159 packages the result in:

```lean
TS159.Goldbach.SelbergDenominatorRefactorInterfaceLedger
TS159.Goldbach.selbergDenominatorRefactorInterfaceLedger
TS159.Goldbach.SelbergDenominatorRefactorInterfaceTarget
TS159.Goldbach.selbergDenominatorRefactorInterfaceTarget
```

The package carries:

```text
the TS158 obstruction closure,
the replacement-interface status,
the eventual no-comparison theorem for the legacy route,
the diagnostic excluding TS122/J2 from any growth interface reaching 2,
and an explicit scope note that no claim is made about all Selberg sieves.
```

## Scope

TS159 is an interface sprint.  It does not propose or prove a new denominator,
does not refactor TS122, and does not reopen the TS150 route.  It makes the
next requirement precise: any repaired route must supply a denominator that
escapes the TS154 cap.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS159.SelbergDenominatorRefactorInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS159
git diff --check -- README.md TS\Goldbach\Strong\TS159
```

Expected result: build succeeds, no audit matches, and no whitespace errors.
