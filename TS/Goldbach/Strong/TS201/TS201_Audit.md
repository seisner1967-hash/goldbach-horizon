# TS201 Audit - Strategic Decision Ledger

## Scope

TS201 records the strategic decision after TS200.  The project now has a
non-circular final consumption interface, but none of the OTSA input contracts
has been proved.  TS201 lists the open fronts and fixes the next target as Wall
0 measure transport.

This is a governance sprint.  It does not prove a new analytic theorem.

## Main declarations

- `TS201.Goldbach.OpenFront`
- `TS201.Goldbach.openFronts`
- `TS201.Goldbach.recommendedPriority`
- `TS201.Goldbach.selectedNextFront`
- `TS201.Goldbach.recommendedPriority_head`
- `TS201.Goldbach.StrategicDecisionLedger`
- `TS201.Goldbach.strategicDecisionLedger`
- `TS201.Goldbach.StrategicDecisionTarget`
- `TS201.Goldbach.strategicDecisionTarget`

## What is recorded

TS201 records these open fronts:

- Wall 0 measure transport;
- Wall 1 Plancherel;
- Wall 2 explicit formula;
- Wall 3 zero summability;
- Wall 4 circle/Gallagher correlation;
- sieve replacement;
- documentation bundle.

The recommended priority begins with `OpenFront.wall0MeasureTransport`.  The
ledger also records that all walls, sieve replacement, and bundle generation
remain unproved or undone.

## Non-claims

TS201 does not prove:

- Wall 0 measure transport;
- Wall 1 Plancherel;
- Wall 2 explicit formula;
- Wall 3 zero summability;
- Wall 4 correlation;
- a replacement sieve budget;
- a documentation bundle;
- any OTSA input contract;
- Goldbach.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS201.StrategicDecisionLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS201
git diff --check
git status --short
```
