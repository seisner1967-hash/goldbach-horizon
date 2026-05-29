# TS56 - Triangle Spline Branch Formulae

## Status

TS56 proves the elementary affine branch formulae for the triangle spline.

Status: `repo_committed`.

TS56 does not prove classical derivative statements, boundary/raccord control,
the distributional derivative identity, Plancherel, or Fourier-tail estimates.
It prepares the next Sobolev-side sprints by recording the formulae:

- on `[-1, 0]`, `triangleSpline x = 1 + x`;
- on `[0, 1]`, `triangleSpline x = 1 - x`;
- outside `[-1, 1]`, `triangleSpline x = 0`.

## Lean Files

- `TriangleSplineBranchFormulae.lean`:
  - proves `triangleSpline_eq_one_add_of_left`;
  - proves `triangleSpline_eq_one_sub_of_right`;
  - proves `triangleSpline_eq_zero_outside_Icc`;
  - packages the formulae in `TriangleSplineBranchFormulae`;
  - proves `triangleSplineBranchFormulaeTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae

rg -n "s[o]rry" TS\Goldbach\Strong\TS56
rg -n "a[x]iom" TS\Goldbach\Strong\TS56
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS56-B1 | `triangleSpline_eq_one_add_of_left` | `repo_committed` | affine formula on the left branch |
| TS56-B2 | `triangleSpline_eq_one_sub_of_right` | `repo_committed` | affine formula on the right branch |
| TS56-B3 | `triangleSpline_eq_zero_outside_Icc` | `repo_committed` | vanishing outside the support |
| TS56-B4 | `TriangleSplineBranchFormulae` | `repo_committed` | branch-formula package |
| TS56-B5 | `triangleSplineBranchFormulaeTarget` | `repo_committed` | target proposition discharged |

## Conclusion

TS56 strengthens the Sobolev route without choosing a derivative or
distributional API. The next natural sprint can prove classical derivative
facts on the open branches using these affine formulae.
