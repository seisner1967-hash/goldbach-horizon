# TS72 - Triangle Spline IPP Right Branch Closed Bridge Proof

## Status

TS72 discharges the closed-right-branch bridge contract isolated in TS71.

Status: `repo_committed`.

TS72 proves that the restricted measure on the half-open branch `(0, 1]`
coincides with the restricted measure on the closed branch `[0, 1]`. It then
uses this measure equality to prove the two concrete right-branch bridge
equalities required by TS71.

TS72 does not prove affine integration by parts, the concrete TS63
distributional contract, Sobolev-slot agreement, Plancherel, or Fourier-tail
estimates.

## Lean Files

- `TriangleSplineIPPRightBranchClosedBridgeProof.lean`:
  - proves `rightBranchMeasure_eq_rightClosedBranchMeasure`;
  - proves `integral_rightBranch_eq_rightClosedBranch`;
  - proves `left_rightBranch_eq_closed`;
  - proves `right_rightBranch_eq_closed`;
  - defines `triangleSplineIPPRightBranchClosedBridge`;
  - proves `triangleSplineIPPRightBranchClosedBridgeTarget`;
  - proves `triangleSplineIPPRightBranchClosedBridgeProofTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS72.TriangleSplineIPPRightBranchClosedBridgeProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS72
rg -n "a[x]iom" TS\Goldbach\Strong\TS72
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS72-C1 | `rightBranchMeasure_eq_rightClosedBranchMeasure` | `repo_committed` | restricted-measure bridge `(0, 1]` to `[0, 1]` |
| TS72-C2 | `integral_rightBranch_eq_rightClosedBranch` | `repo_committed` | generic Bochner integral bridge |
| TS72-C3 | `left_rightBranch_eq_closed` | `repo_committed` | bridge for the left IPP integrand |
| TS72-C4 | `right_rightBranch_eq_closed` | `repo_committed` | bridge for the right IPP integrand |
| TS72-C5 | `triangleSplineIPPRightBranchClosedBridge` | `repo_committed` | concrete TS71 contract discharge |

## Conclusion

TS72 removes the topological half-open/right-closed mismatch from the IPP
route. The right branch can now be treated on the closed interval `[0, 1]`,
which is the natural domain for the future affine integration-by-parts proof.
