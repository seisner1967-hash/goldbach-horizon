# TS43 - Triangle Spline Pointwise Facts

## Status

TS43 proves pointwise algebraic/order facts about the triangle-spline weak
derivative representative.

Status: `repo_committed`.

TS43 does not prove the Lebesgue integral, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.

## Lean Files

- `TriangleSplinePointwise.lean`:
  - proves `triangleSplineDeriv_eq_one_of_left`;
  - proves `triangleSplineDeriv_eq_neg_one_of_right`;
  - proves `triangleSplineDeriv_eq_zero_of_not_left_not_right`;
  - proves `abs_triangleSplineDeriv_le_one`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS43.TriangleSplinePointwise

rg -n "s[o]rry" TS\Goldbach\Strong\TS43
rg -n "a[x]iom" TS\Goldbach\Strong\TS43
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS43-P1 | `triangleSplineDeriv_eq_one_of_left` | `repo_committed` | left branch |
| TS43-P2 | `triangleSplineDeriv_eq_neg_one_of_right` | `repo_committed` | right branch |
| TS43-P3 | `triangleSplineDeriv_eq_zero_of_not_left_not_right` | `repo_committed` | outside the two open branches |
| TS43-P4 | `abs_triangleSplineDeriv_le_one` | `repo_committed` | pointwise bound |
