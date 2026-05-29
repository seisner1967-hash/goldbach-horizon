# TS61 - Triangle Spline Distributional Derivative Ledger

## Status

TS61 records the distributional derivative identity needed after the TS60
almost-everywhere classical derivative bridge.

Status: `repo_committed_relative`.

TS61 does not prove the distributional derivative identity, does not choose a
concrete Mathlib test-function API, and does not prove Sobolev-slot agreement,
Plancherel, or Fourier-tail estimates. It exposes the weak-derivative identity
as an explicit local analytic infrastructure obligation.

## Lean Files

- `TriangleSplineDistributionalDerivativeLedger.lean`:
  - defines `TriangleSplineTestFunctionAPI`;
  - defines `TriangleSplineDistributionalDerivativeContract`;
  - defines `TriangleSplineDistributionalDerivativeTarget`;
  - records the TS60 a.e. classical derivative bridge in
    `TriangleSplineDistributionalDerivativeInputs`;
  - proves `triangleSplineDistributionalDerivativeInputsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS61.TriangleSplineDistributionalDerivativeLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS61
rg -n "a[x]iom" TS\Goldbach\Strong\TS61
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS61-D1 | `TriangleSplineTestFunctionAPI` | `analytic_infrastructure_obligation` | abstract test-function interface |
| TS61-D2 | `TriangleSplineDistributionalDerivativeContract` | `analytic_infrastructure_obligation` | weak derivative identity contract |
| TS61-D3 | `TriangleSplineDistributionalDerivativeTarget` | `repo_committed_relative` | target proposition for the distributional proof |
| TS61-D4 | `TriangleSplineDistributionalDerivativeInputs` | `repo_committed` | records the TS60 a.e. derivative bridge as input |
| TS61-D5 | `triangleSplineDistributionalDerivativeInputsTarget` | `repo_committed` | TS60 input package is available |

## Conclusion

TS61 fixes the exact weak-derivative contract while preserving the fail-closed
discipline. The next Sobolev-side sprint can either select a concrete Mathlib
test-function API or decompose the integration-by-parts proof into smaller
lemmas.
