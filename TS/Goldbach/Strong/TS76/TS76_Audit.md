# TS76 - Triangle Spline IPP Interval-Integral Bridge Proof

## Status

TS76 discharges the interval-integral bridge contract isolated in TS75.

Status: `repo_committed`.

The proof uses `restrict_Ioc_eq_restrict_Icc` to replace the closed branch
restricted measures by the `Ioc` restricted measures used in interval
integrals, then uses `intervalIntegral.integral_of_le` on the oriented
intervals `[-1, 0]` and `[0, 1]`.

TS76 does not prove affine integration by parts, the concrete TS63
distributional contract, Sobolev-slot agreement, Plancherel, or Fourier-tail
estimates.

## Lean Files

- `TriangleSplineIPPIntervalIntegralBridgeProof.lean`:
  - proves `leftBranchMeasure_eq_leftIocMeasure`;
  - proves `integral_leftBranchMeasure_eq_interval`;
  - proves `integral_rightClosedBranchMeasure_eq_interval`;
  - proves the four concrete TS75 IPP-integrand bridge fields;
  - defines `triangleSplineIPPIntervalIntegralBridge`;
  - defines `TriangleSplineIPPIntervalIntegralBridgeProofTarget`;
  - proves `triangleSplineIPPIntervalIntegralBridgeTarget`;
  - proves `triangleSplineIPPIntervalIntegralBridgeProofTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS76.TriangleSplineIPPIntervalIntegralBridgeProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS76
rg -n "a[x]iom" TS\Goldbach\Strong\TS76
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS76-B1 | `leftBranchMeasure_eq_leftIocMeasure` | `repo_committed` | null-left-endpoint restricted-measure bridge |
| TS76-B2 | `integral_leftBranchMeasure_eq_interval` | `repo_committed` | generic left branch restricted-measure to interval-integral bridge |
| TS76-B3 | `integral_rightClosedBranchMeasure_eq_interval` | `repo_committed` | generic right branch restricted-measure to interval-integral bridge |
| TS76-B4 | `triangleSplineIPPIntervalIntegralBridge` | `repo_committed` | concrete discharge of the TS75 bridge contract |
| TS76-B5 | `triangleSplineIPPIntervalIntegralBridgeTarget` | `repo_committed` | discharges the TS75 target |

## Conclusion

TS76 removes the API-alignment burden between branch restricted integrals and
Mathlib interval integrals. The remaining local work is now the affine
integration-by-parts calculation on the two closed branches.
