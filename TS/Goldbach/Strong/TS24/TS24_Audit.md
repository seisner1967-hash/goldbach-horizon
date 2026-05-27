# TS24 - Closed Form Scale Bridge

## Status

TS24 proves a closed-form domination bridge for the exact integer
Brun-Titchmarsh ceiling-budget scale.

Status: `repo_committed`.

It does not prove Brun-Titchmarsh itself. The interval-count theorem remains
the local obligation `BrunTitchmarshNatIntervalBound`. TS24 only discharges the
rounding and scale-domination step after that interval theorem is supplied.

## Lean Files

- `ClosedFormScaleBridge.lean`:
  - defines the real kernel underlying `brunTitchmarshCeilBudget`;
  - proves `brunTitchmarshCeilBudget <= kernel + 1`;
  - defines `brunTitchmarshPaddedClosedFormScale`;
  - proves `localWindowBudgetScale_le_paddedClosedFormScale`;
  - proves `Problem_E1Scale_from_natIntervalBound_paddedClosedForm`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS24.ClosedFormScaleBridge

rg -n "s[o]rry" TS\Goldbach\Strong\TS24
rg -n "a[x]iom" TS\Goldbach\Strong\TS24
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS24-C1 | `brunTitchmarshCeilKernel` | `repo_committed` | real kernel behind the integer ceiling budget |
| TS24-C2 | `brunTitchmarshCeilBudget_le_kernel_add_one` | `repo_committed` | ceiling arithmetic |
| TS24-C3 | `brunTitchmarshPaddedClosedFormScale` | `repo_committed` | closed form with the required ceiling cushion |
| TS24-C4 | `localWindowBudgetScale_le_paddedClosedFormScale` | `repo_committed` | exact scale dominated by padded closed form |
| TS24-C5 | `Problem_E1Scale_from_natIntervalBound_paddedClosedForm` | `repo_committed_relative` | interval BT implies scaled E1 at padded closed-form scale |

## Conclusion

TS24 closes the arithmetic scale-domination layer without touching the sieve
theorem. The resulting path is:

```text
BrunTitchmarshNatIntervalBound
  => localWindowBudgetScale
  <= brunTitchmarshPaddedClosedFormScale
  => Problem_E1Scale brunTitchmarshPaddedClosedFormScale 1
```
