# TS58 - Triangle Spline Boundary and Exterior Control

## Status

TS58 proves the exterior derivative facts for the triangle spline and records
that the three corner points are Lebesgue-null.

Status: `repo_committed`.

TS58 does not prove global a.e. differentiability, the distributional
derivative identity, Sobolev-slot agreement, Plancherel, or Fourier-tail
estimates. It prepares the future a.e. classical derivative bridge by covering
the two exterior open regions and isolating the exceptional set.

## Lean Files

- `TriangleSplineBoundaryExteriorControl.lean`:
  - proves `triangleSpline_hasDerivAt_left_exterior`;
  - proves `triangleSpline_hasDerivAt_right_exterior`;
  - proves `triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior`;
  - proves `triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior`;
  - defines `triangleSplineCornerSet`;
  - proves `volume_triangleSplineCornerSet`;
  - packages the facts in `TriangleSplineBoundaryExteriorControl`;
  - proves `triangleSplineBoundaryExteriorControlTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS58.TriangleSplineBoundaryExteriorControl

rg -n "s[o]rry" TS\Goldbach\Strong\TS58
rg -n "a[x]iom" TS\Goldbach\Strong\TS58
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS58-B1 | `triangleSpline_hasDerivAt_left_exterior` | `repo_committed` | derivative `0` on `(-infty, -1)` |
| TS58-B2 | `triangleSpline_hasDerivAt_right_exterior` | `repo_committed` | derivative `0` on `(1, infty)` |
| TS58-B3 | `triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior` | `repo_committed` | exterior derivative agrees with the explicit representative on the left |
| TS58-B4 | `triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior` | `repo_committed` | exterior derivative agrees with the explicit representative on the right |
| TS58-B5 | `triangleSplineCornerSet` | `repo_committed` | exceptional corner set `{ -1, 0, 1 }` |
| TS58-B6 | `volume_triangleSplineCornerSet` | `repo_committed` | corner set is Lebesgue-null |
| TS58-B7 | `TriangleSplineBoundaryExteriorControl` | `repo_committed` | boundary/exterior control package |
| TS58-B8 | `triangleSplineBoundaryExteriorControlTarget` | `repo_committed` | target proposition discharged |

## Conclusion

TS58 discharges the exterior and corner-null parts of the TS55 Sobolev ledger.
The next Sobolev-side sprint can combine TS57 and TS58 into an a.e. classical
derivative statement away from the corner set.
