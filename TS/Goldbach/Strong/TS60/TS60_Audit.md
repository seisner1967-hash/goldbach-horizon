# TS60 - Triangle Spline A.E. Classical Derivative

## Status

TS60 lifts the TS59 off-corner pointwise derivative theorem to an
almost-everywhere derivative statement using the nullity of the corner set
proved in TS58.

Status: `repo_committed`.

TS60 does not prove the distributional derivative identity, Sobolev-slot
agreement, Plancherel, or Fourier-tail estimates. It proves the measure-theory
bridge needed before those later Sobolev-side steps.

## Lean Files

- `TriangleSplineAEClassicalDerivative.lean`:
  - proves `ae_not_mem_triangleSplineCornerSet`;
  - proves `triangleSpline_hasDerivAt_triangleSplineDeriv_ae`;
  - proves `deriv_triangleSpline_eq_triangleSplineDeriv_ae`;
  - packages the facts in `TriangleSplineAEClassicalDerivative`;
  - proves `triangleSplineAEClassicalDerivativeTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS60.TriangleSplineAEClassicalDerivative

rg -n "s[o]rry" TS\Goldbach\Strong\TS60
rg -n "a[x]iom" TS\Goldbach\Strong\TS60
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS60-A1 | `ae_not_mem_triangleSplineCornerSet` | `repo_committed` | null corner set gives a.e. off-corner membership |
| TS60-A2 | `triangleSpline_hasDerivAt_triangleSplineDeriv_ae` | `repo_committed` | a.e. existence of the classical derivative with explicit representative |
| TS60-A3 | `deriv_triangleSpline_eq_triangleSplineDeriv_ae` | `repo_committed` | global `deriv` agrees a.e. with `triangleSplineDeriv` |
| TS60-A4 | `TriangleSplineAEClassicalDerivative` | `repo_committed` | a.e. derivative package |
| TS60-A5 | `triangleSplineAEClassicalDerivativeTarget` | `repo_committed` | target proposition discharged |

## Conclusion

TS60 completes the measure-theoretic lift from pointwise off-corner derivative
control to a.e. classical derivative agreement. The next Sobolev-side sprint can
use this as the Lebesgue bridge before the distributional derivative identity.
