# TS78 - Triangle Spline Concrete Distributional Discharge

## Status

TS78 discharges the concrete TS63 weak-derivative contract by combining the
TS77 affine branch integration-by-parts proof with the TS74 recombination
theorem.

Status: `repo_committed`.

TS78 proves the concrete distributional identity for the triangle spline
against the TS62 concrete test-function API. It does not yet lift the result to
the abstract TS61 distributional contract, does not prove TS49 Sobolev-slot
agreement, and does not prove Plancherel or Fourier-tail estimates.

## Lean Files

- `TriangleSplineConcreteDistributionalDischarge.lean`:
  - defines `triangleSplineConcreteDistributionalContract`;
  - proves `triangleSplineConcreteDistributionalContractTarget`;
  - defines `TriangleSplineConcreteDistributionalDischargeTarget`;
  - proves `triangleSplineConcreteDistributionalDischargeTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS78.TriangleSplineConcreteDistributionalDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS78
rg -n "a[x]iom" TS\Goldbach\Strong\TS78
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS78-P1 | `triangleSplineConcreteDistributionalContract` | `repo_committed` | concrete TS63 contract from TS74 and TS77 |
| TS78-P2 | `triangleSplineConcreteDistributionalContractTarget` | `repo_committed` | discharges the TS63 target |
| TS78-P3 | `TriangleSplineConcreteDistributionalDischargeTarget` | `repo_committed` | local TS78 target |
| TS78-P4 | `triangleSplineConcreteDistributionalDischargeTarget` | `repo_committed` | local target proof |

## Conclusion

TS78 closes the concrete distributional derivative step. The next natural
sprint is the lift from the concrete TS63 target to the abstract TS61
distributional target, followed by the Sobolev-slot agreement route.
