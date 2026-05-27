# TS30 - Brun-Titchmarsh Selberg Roadmap

## Status

TS30 decomposes the remaining `BrunTitchmarshNatIntervalBound` obligation into
two local Selberg-facing obligations:

1. a sieve interval bound producing an explicit integer majorant;
2. an arithmetic comparison between that majorant and the TS22 ceiling budget.

Status: `repo_committed_relative`.

TS30 does not prove the Selberg sieve, Brun-Titchmarsh, or Goldbach. It records
the exact Lean interface that a future Selberg/Brun-Titchmarsh formalization
can instantiate.

## Lean Files

- `BrunTitchmarshSelbergRoadmap.lean`:
  - defines `SelbergIntervalMajorant`;
  - defines `SelbergSieveIntervalBound`;
  - defines `SelbergMajorantBudgetComparison`;
  - defines `SelbergBrunTitchmarshInfrastructure`;
  - proves `brunTitchmarshNatIntervalBound_from_selberg`;
  - proves `Problem_E1Scale_from_selberg_roadmap`;
  - proves `natIntervalBound_from_selberg_roadmap`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS30.BrunTitchmarshSelbergRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS30
rg -n "a[x]iom" TS\Goldbach\Strong\TS30
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS30-S1 | `SelbergIntervalMajorant` | `analytic_infrastructure_obligation` | explicit integer majorant for local prime counts |
| TS30-S2 | `SelbergSieveIntervalBound` | `analytic_infrastructure_obligation` | Selberg sieve proves `primeIntervalCard <= majorant` |
| TS30-S3 | `SelbergMajorantBudgetComparison` | `arithmetic_obligation` | compares the majorant with the TS22 BT ceiling budget |
| TS30-S4 | `SelbergBrunTitchmarshInfrastructure` | `analytic_infrastructure_obligation` | package sufficient for BT |
| TS30-S5 | `brunTitchmarshNatIntervalBound_from_selberg` | `repo_committed_relative` | Selberg infrastructure implies TS22 BT input |
| TS30-S6 | `Problem_E1Scale_from_selberg_roadmap` | `repo_committed_relative` | Selberg infrastructure feeds scaled E1 |

## Conclusion

The absence of a Brun-Titchmarsh proof is now localized one level deeper:

```text
SelbergSieveIntervalBound
+ SelbergMajorantBudgetComparison
=> BrunTitchmarshNatIntervalBound
=> Problem_E1Scale
```

This is the intended target for a future Mathlib Selberg-sieve contribution.
