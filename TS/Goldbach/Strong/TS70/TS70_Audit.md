# TS70 - Triangle Spline IPP Branch Split Proof

## Status

TS70 discharges the branch-splitting contract introduced in TS69.

Status: `repo_committed`.

TS70 proves that the TS69 branch sets cover `[-1, 1]`, are disjoint, and that
the restricted measure on `[-1, 1]` splits as the sum of the restricted
measures on `[-1, 0]` and `(0, 1]`. Using TS65 integrability, it then proves
the two branch-splitting equalities for the concrete IPP integrands.

TS70 does not convert `(0, 1]` to `[0, 1]`, does not prove affine integration
by parts, does not prove the TS63 concrete distributional contract, and does
not prove Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPBranchSplitProof.lean`:
  - proves `branch_union_eq_Icc`;
  - proves `disjoint_left_right_branch`;
  - proves `restrict_Icc_eq_left_add_right`;
  - proves `integral_branch_split`;
  - proves `left_integral_split`;
  - proves `right_integral_split`;
  - defines `triangleSplineIPPBranchSplit`;
  - defines `TriangleSplineIPPBranchSplitProofTarget`;
  - proves `triangleSplineIPPBranchSplitTarget`;
  - proves `triangleSplineIPPBranchSplitProofTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS70.TriangleSplineIPPBranchSplitProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS70
rg -n "a[x]iom" TS\Goldbach\Strong\TS70
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS70-B1 | `branch_union_eq_Icc` | `repo_committed` | branch sets cover `[-1, 1]` |
| TS70-B2 | `disjoint_left_right_branch` | `repo_committed` | branch sets are disjoint |
| TS70-B3 | `restrict_Icc_eq_left_add_right` | `repo_committed` | restricted measure split |
| TS70-B4 | `integral_branch_split` | `repo_committed` | generic integrable-function branch split |
| TS70-B5 | `left_integral_split` | `repo_committed` | left IPP integrand split |
| TS70-B6 | `right_integral_split` | `repo_committed` | right IPP integrand split |
| TS70-B7 | `triangleSplineIPPBranchSplit` | `repo_committed` | concrete discharge of TS69 |

## Conclusion

TS70 turns the TS69 branch-splitting contract into a concrete Lean proof using
the disjoint decomposition `[-1, 1] = [-1, 0] union (0, 1]`, Mathlib's
`Measure.restrict_union`, and `integral_add_measure`. The next sprint can
address the bridge from the half-open right branch `(0, 1]` to a closed
interval suitable for the affine integration-by-parts proof.
