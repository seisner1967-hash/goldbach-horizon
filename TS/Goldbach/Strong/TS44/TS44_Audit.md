# TS44 - Triangle Spline Measurability and Support

## Status

TS44 proves the support and measurability inputs for the triangle-spline weak
derivative representative.

Status: `repo_committed`.

TS44 does not prove the Lebesgue integral, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.

## Lean Files

- `TriangleSplineMeasurabilitySupport.lean`:
  - proves `triangleSplineDeriv_eq_zero_of_le_neg_one`;
  - proves `triangleSplineDeriv_eq_zero_of_one_le`;
  - proves `triangleSplineDeriv_zero_outside_Icc`;
  - proves `triangleSplineDeriv_measurable`;
  - defines `TriangleSplineDerivativeSupportInputs`;
  - defines `triangleSplineDerivativeSupportInputs`;
  - defines and discharges `TriangleSplineDerivativeSupportTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS44.TriangleSplineMeasurabilitySupport

rg -n "s[o]rry" TS\Goldbach\Strong\TS44
rg -n "a[x]iom" TS\Goldbach\Strong\TS44
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS44-S1 | `triangleSplineDeriv_eq_zero_of_le_neg_one` | `repo_committed` | left exterior vanishing |
| TS44-S2 | `triangleSplineDeriv_eq_zero_of_one_le` | `repo_committed` | right exterior vanishing |
| TS44-S3 | `triangleSplineDeriv_zero_outside_Icc` | `repo_committed` | support containment in `[-1, 1]` |
| TS44-S4 | `triangleSplineDeriv_measurable` | `repo_committed` | measurability of the derivative representative |
| TS44-S5 | `TriangleSplineDerivativeSupportInputs` | `repo_committed` | support/measurability package |
| TS44-S6 | `TriangleSplineDerivativeSupportTarget` | `repo_committed` | discharged support target |
