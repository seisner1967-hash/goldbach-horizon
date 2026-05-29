# TS62 - Triangle Spline Test Function API Probe

## Status

TS62 selects a concrete, lightweight candidate API for the test functions used
in the TS61 distributional derivative ledger.

Status: `repo_committed_relative`.

TS62 does not prove the distributional derivative identity, does not prove
integration by parts, and does not prove Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates. It binds the abstract TS61 test-function interface to a
plain `Real -> Complex` package with explicit regularity, compact-support, and
derivative-agreement fields.

## Lean Files

- `TriangleSplineTestFunctionAPIProbe.lean`:
  - defines `TriangleSplineConcreteTestFunction`;
  - defines `triangleSplineConcreteTestFunctionAPI`;
  - defines `TriangleSplineConcreteTestFunctionAPITarget`;
  - proves `triangleSplineConcreteTestFunctionAPITarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS62.TriangleSplineTestFunctionAPIProbe

rg -n "s[o]rry" TS\Goldbach\Strong\TS62
rg -n "a[x]iom" TS\Goldbach\Strong\TS62
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS62-T1 | `TriangleSplineConcreteTestFunction` | `repo_committed_relative` | concrete candidate test-function package |
| TS62-T2 | `triangleSplineConcreteTestFunctionAPI` | `repo_committed_relative` | concrete binding to TS61 test-function API |
| TS62-T3 | `TriangleSplineConcreteTestFunctionAPITarget` | `repo_committed_relative` | target proposition |
| TS62-T4 | `triangleSplineConcreteTestFunctionAPITarget` | `repo_committed_relative` | target proposition discharged |

## Conclusion

TS62 chooses a concrete test-function shape without committing to a heavier
Mathlib distribution or smooth compact support API. Future sprints can either
strengthen this package or prove the branchwise integration-by-parts identity
against it.
