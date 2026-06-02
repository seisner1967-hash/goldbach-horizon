# TS69 - Triangle Spline IPP Branch Split

## Status

TS69 records the branch-splitting contract for the two restricted
triangle-spline integration-by-parts products.

Status: `repo_committed_relative`.

TS69 names the disjoint branch sets `Icc (-1 : Real) 0` and `Ioc (0 : Real) 1`
and the corresponding restricted measures. It then records the exact theorem
shape saying that each TS68-restricted integral over `[-1, 1]` should split as
the sum of the left-branch and right-branch integrals.

TS69 does not prove the branch split, does not convert the right branch to a
closed interval, does not prove affine integration by parts, and does not prove
the TS63 concrete distributional contract, Sobolev-slot agreement,
Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPBranchSplit.lean`:
  - defines `leftBranchSet`;
  - defines `rightBranchSet`;
  - defines `leftBranchMeasure`;
  - defines `rightBranchMeasure`;
  - defines `TriangleSplineIPPBranchSplit`;
  - defines `TriangleSplineIPPBranchSplitInputs`;
  - defines `triangleSplineIPPBranchSplitInputs`;
  - defines `TriangleSplineIPPBranchSplitTarget`;
  - proves `triangleSplineIPPBranchSplitInputsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS69.TriangleSplineIPPBranchSplit

rg -n "s[o]rry" TS\Goldbach\Strong\TS69
rg -n "a[x]iom" TS\Goldbach\Strong\TS69
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS69-B1 | `leftBranchSet` | `repo_committed_relative` | branch set `[-1, 0]` |
| TS69-B2 | `rightBranchSet` | `repo_committed_relative` | branch set `(0, 1]` |
| TS69-B3 | `leftBranchMeasure` | `repo_committed_relative` | volume restricted to the left branch |
| TS69-B4 | `rightBranchMeasure` | `repo_committed_relative` | volume restricted to the right branch |
| TS69-B5 | `TriangleSplineIPPBranchSplit` | `analytic_infrastructure_obligation` | branchwise splitting contract |
| TS69-B6 | `TriangleSplineIPPBranchSplitInputs` | `repo_committed` | TS68 restriction input package |

## Conclusion

TS69 fixes the branchwise split theorem shape without proving it. The next
sprint can attempt to discharge this contract using additivity of restricted
measures over the disjoint decomposition `[-1, 1] = [-1, 0] union (0, 1]`.
