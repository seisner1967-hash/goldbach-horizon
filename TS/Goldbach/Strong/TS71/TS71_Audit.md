# TS71 - Triangle Spline IPP Right Branch Closed Bridge

## Status

TS71 records the closed-right-branch bridge contract needed after the TS70
branch split.

Status: `repo_committed_relative`.

TS71 names the closed right branch `Icc (0 : Real) 1` and its restricted
measure. It then records the exact theorem shape saying that the right-branch
integrals over `Ioc (0 : Real) 1` can be replaced by integrals over
`Icc (0 : Real) 1` for both concrete IPP integrands.

TS71 does not prove the closed-branch bridge, does not prove affine integration
by parts, and does not prove the TS63 concrete distributional contract,
Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPRightBranchClosedBridge.lean`:
  - defines `rightClosedBranchSet`;
  - defines `rightClosedBranchMeasure`;
  - defines `TriangleSplineIPPRightBranchClosedBridge`;
  - defines `TriangleSplineIPPRightBranchClosedBridgeInputs`;
  - defines `triangleSplineIPPRightBranchClosedBridgeInputs`;
  - defines `TriangleSplineIPPRightBranchClosedBridgeTarget`;
  - proves `triangleSplineIPPRightBranchClosedBridgeInputsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS71.TriangleSplineIPPRightBranchClosedBridge

rg -n "s[o]rry" TS\Goldbach\Strong\TS71
rg -n "a[x]iom" TS\Goldbach\Strong\TS71
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS71-C1 | `rightClosedBranchSet` | `repo_committed_relative` | closed branch `[0, 1]` |
| TS71-C2 | `rightClosedBranchMeasure` | `repo_committed_relative` | volume restricted to `[0, 1]` |
| TS71-C3 | `TriangleSplineIPPRightBranchClosedBridge` | `analytic_infrastructure_obligation` | bridge from `(0, 1]` to `[0, 1]` |
| TS71-C4 | `TriangleSplineIPPRightBranchClosedBridgeInputs` | `repo_committed` | TS70 branch-split input package |

## Conclusion

TS71 fixes the theorem shape needed before affine integration by parts on the
right branch. The next sprint can attempt to prove that the two right-branch
integrals are unchanged by adding the singleton `{0}`, using its Lebesgue-null
measure.
