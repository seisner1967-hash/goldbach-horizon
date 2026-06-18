# TS158 Audit - Selberg/Brun-Titchmarsh Obstruction Closure Ledger

## Status

`repo_committed`

TS158 packages the obstruction proved across TS153--TS157 into one terminal
ledger for the current Selberg/Brun-Titchmarsh route.

## Affected route

The affected route is named by:

```lean
TS158.Goldbach.SelbergBTObstructionRoute.refinedSelbergBudgetToTS22
```

It refers specifically to the TS150 refined Selberg budget comparison against
the TS22 `brunTitchmarshCeilBudget`.

## Named causes

TS158 records the three formal causes:

```lean
TS158.Goldbach.SelbergBTObstructionCause.jordanTwoDenominatorBoundedByTwo
TS158.Goldbach.SelbergBTObstructionCause.thresholdGeometryForcesOppositeInequality
TS158.Goldbach.SelbergBTObstructionCause.goldbachScaleEventuallyTriggersThreshold
```

These correspond to:

```text
TS154: D(level) < 2 for positive levels.
TS155: successful comparison forces intervalScale+1 < 2*BTceil.
TS157: for x >= 2^3000 at Goldbach scale, the opposite obstruction holds.
```

## Terminal theorem

TS158 exposes a single theorem:

```lean
TS158.Goldbach.no_TS150_dependent_BT_comparison_eventually
```

It states that for every dependent Selberg level selection and every
`x >= TS157.Goldbach.goldbachObstructionThreshold`, the TS150 dependent
budget comparison is impossible.

## Closure package

The closure package is:

```lean
TS158.Goldbach.SelbergBTObstructionClosure
TS158.Goldbach.selbergBTObstructionClosure
TS158.Goldbach.selbergBTObstructionClosureTarget
```

It records:

```text
threshold = TS157.goldbachObstructionThreshold = 2^3000,
the affected route,
the named causes,
the denominator cap D <= 2,
the eventual Goldbach obstruction regime,
the eventual geometric obstruction,
the terminal no-comparison theorem.
```

## Scope

TS158 does not refactor the denominator, change the TS22 budget, or claim that
every possible Selberg sieve formulation fails. It only closes the current
TS150 route using the current TS122 Jordan-two denominator.

The cumulative finite-head prime-count obligation from TS152 remains separate.
The next architectural task is to choose whether to refactor the denominator or
budget interface, or pivot to another analytic front.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS158.SelbergBTObstructionClosureLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS158
git diff --check -- README.md TS\Goldbach\Strong\TS158
```

Expected result: build succeeds and both audit commands report no issue.
