# TS57 - Triangle Spline Classical Branch Derivatives

## Status

TS57 proves the classical derivative facts for the triangle spline on its two
open affine branches.

Status: `repo_committed`.

TS57 does not prove global a.e. differentiability, boundary/raccord control,
the distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates. It is the next concrete Sobolev-side refinement after
TS56.

## Lean Files

- `TriangleSplineClassicalBranchDerivatives.lean`:
  - proves `triangleSpline_hasDerivAt_left`;
  - proves `triangleSpline_hasDerivAt_right`;
  - proves `triangleSpline_hasDerivAt_triangleSplineDeriv_left`;
  - proves `triangleSpline_hasDerivAt_triangleSplineDeriv_right`;
  - packages the facts in `TriangleSplineClassicalBranchDerivatives`;
  - proves `triangleSplineClassicalBranchDerivativesTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS57.TriangleSplineClassicalBranchDerivatives

rg -n "s[o]rry" TS\Goldbach\Strong\TS57
rg -n "a[x]iom" TS\Goldbach\Strong\TS57
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS57-D1 | `triangleSpline_hasDerivAt_left` | `repo_committed` | derivative `1` on `(-1, 0)` |
| TS57-D2 | `triangleSpline_hasDerivAt_right` | `repo_committed` | derivative `-1` on `(0, 1)` |
| TS57-D3 | `triangleSpline_hasDerivAt_triangleSplineDeriv_left` | `repo_committed` | derivative agrees with the explicit representative on the left branch |
| TS57-D4 | `triangleSpline_hasDerivAt_triangleSplineDeriv_right` | `repo_committed` | derivative agrees with the explicit representative on the right branch |
| TS57-D5 | `TriangleSplineClassicalBranchDerivatives` | `repo_committed` | branch-derivative package |
| TS57-D6 | `triangleSplineClassicalBranchDerivativesTarget` | `repo_committed` | target proposition discharged |

## Conclusion

TS57 discharges the classical open-branch derivative part of the TS55 Sobolev
ledger. The next Sobolev-side sprint can isolate the exceptional boundary
points `-1`, `0`, and `1`, or bridge these open-branch facts to an a.e.
classical derivative statement.
