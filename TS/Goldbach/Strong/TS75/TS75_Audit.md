# TS75 - Triangle Spline IPP Interval-Integral Bridge

## Status

TS75 records the bridge contract between the closed-branch restricted-measure
integrals used in TS73 and the directed interval integrals expected by
Mathlib's finite-interval integration-by-parts API.

Status: `repo_committed_relative`.

TS75 does not prove the restricted-measure to interval-integral conversion. It
does not prove affine integration by parts, the concrete TS63 distributional
contract, Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPIntervalIntegralBridge.lean`:
  - defines `leftBranchIntervalIntegral`;
  - defines `rightClosedBranchIntervalIntegral`;
  - defines `TriangleSplineIPPIntervalIntegralBridge`;
  - defines `TriangleSplineIPPIntervalIntegralBridgeInputs`;
  - defines `triangleSplineIPPIntervalIntegralBridgeInputs`;
  - defines `TriangleSplineIPPIntervalIntegralBridgeTarget`;
  - defines `TriangleSplineIPPIntervalIntegralBridgeInputsTarget`;
  - proves `triangleSplineIPPIntervalIntegralBridgeInputsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS75.TriangleSplineIPPIntervalIntegralBridge

rg -n "s[o]rry" TS\Goldbach\Strong\TS75
rg -n "a[x]iom" TS\Goldbach\Strong\TS75
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS75-B1 | `leftBranchIntervalIntegral` | `repo_committed_relative` | directed interval-integral shape for the left branch |
| TS75-B2 | `rightClosedBranchIntervalIntegral` | `repo_committed_relative` | directed interval-integral shape for the right branch |
| TS75-B3 | `TriangleSplineIPPIntervalIntegralBridge` | `analytic_infrastructure_obligation` | bridge from restricted branch measures to interval-integral API |
| TS75-B4 | `TriangleSplineIPPIntervalIntegralBridgeInputs` | `repo_committed_relative` | records TS73/TS74 inputs before proving the bridge |
| TS75-B5 | `triangleSplineIPPIntervalIntegralBridgeInputsTarget` | `repo_committed_relative` | concrete availability of the TS75 inputs |

## Conclusion

TS75 isolates the remaining API-alignment step before the affine branch IPP
calculation. The local work is now split into converting the closed-branch
restricted integrals to interval-integral form, then applying the affine
one-dimensional integration-by-parts lemmas.
