# TS79 - Triangle Spline Distributional Derivative Discharge

## Status

TS79 lifts the concrete TS63 weak-derivative contract discharged in TS78 to the
abstract TS61 distributional derivative target.

Status: `repo_committed`.

TS79 proves the abstract distributional derivative identity is available for
the TS61 test-function API instantiated by TS62. It does not yet prove the TS49
Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineDistributionalDerivativeDischarge.lean`:
  - defines `triangleSplineDistributionalDerivativeContract`;
  - proves `triangleSplineDistributionalDerivativeTarget`;
  - defines `TriangleSplineDistributionalDerivativeDischargeTarget`;
  - proves `triangleSplineDistributionalDerivativeDischargeTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS79.TriangleSplineDistributionalDerivativeDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS79
rg -n "a[x]iom" TS\Goldbach\Strong\TS79
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS79-P1 | `triangleSplineDistributionalDerivativeContract` | `repo_committed` | abstract TS61 contract from TS63 and TS78 |
| TS79-P2 | `triangleSplineDistributionalDerivativeTarget` | `repo_committed` | discharges the TS61 target |
| TS79-P3 | `TriangleSplineDistributionalDerivativeDischargeTarget` | `repo_committed` | local TS79 target |
| TS79-P4 | `triangleSplineDistributionalDerivativeDischargeTarget` | `repo_committed` | local target proof |

## Conclusion

TS79 closes the abstract distributional derivative step. The next natural
sprint is the Sobolev-slot agreement assembly using the a.e. derivative bridge
and the distributional derivative target.
