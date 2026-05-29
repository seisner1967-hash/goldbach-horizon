# TS59 - Triangle Spline Off-Corner Classical Derivative

## Status

TS59 proves that away from the corner set `{ -1, 0, 1 }`, the classical
derivative of the triangle spline exists and agrees with `triangleSplineDeriv`.

Status: `repo_committed`.

TS59 does not prove the almost-everywhere derivative statement, the
distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates. It prepares the future a.e. bridge by proving the
pointwise off-corner derivative statement.

## Lean Files

- `TriangleSplineOffCornerClassicalDerivative.lean`:
  - proves `ne_neg_one_of_not_corner`;
  - proves `ne_zero_of_not_corner`;
  - proves `ne_one_of_not_corner`;
  - proves `triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner`;
  - packages the fact in `TriangleSplineOffCornerClassicalDerivative`;
  - proves `triangleSplineOffCornerClassicalDerivativeTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS59.TriangleSplineOffCornerClassicalDerivative

rg -n "s[o]rry" TS\Goldbach\Strong\TS59
rg -n "a[x]iom" TS\Goldbach\Strong\TS59
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS59-O1 | `ne_neg_one_of_not_corner` | `repo_committed` | off-corner excludes `-1` |
| TS59-O2 | `ne_zero_of_not_corner` | `repo_committed` | off-corner excludes `0` |
| TS59-O3 | `ne_one_of_not_corner` | `repo_committed` | off-corner excludes `1` |
| TS59-O4 | `triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner` | `repo_committed` | off-corner derivative agrees with the explicit representative |
| TS59-O5 | `TriangleSplineOffCornerClassicalDerivative` | `repo_committed` | off-corner derivative package |
| TS59-O6 | `triangleSplineOffCornerClassicalDerivativeTarget` | `repo_committed` | target proposition discharged |

## Conclusion

TS59 turns the branch and exterior derivative facts from TS57/TS58 into a
single pointwise off-corner derivative theorem. The next Sobolev-side sprint can
combine this with `volume_triangleSplineCornerSet` to prove the a.e. classical
derivative bridge.
