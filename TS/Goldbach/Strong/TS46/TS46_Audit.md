# TS46 - Triangle Spline Support Measure

## Status

TS46 proves the elementary Lebesgue-measure input for the support interval of
the triangle-spline weak-derivative representative.

Status: `repo_committed`.

TS46 proves that `volume (Icc (-1 : Real) 1) = ENNReal.ofReal 2`, and hence
the support-measure bound needed by the future `snorm` estimate.

TS46 does not prove the `snorm` estimate, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.

## Lean Files

- `TriangleSplineSupportMeasure.lean`:
  - proves `triangleSpline_support_volume_eq_two`;
  - proves `triangleSpline_support_volume_le_two`;
  - defines `TriangleSplineSupportMeasureInputs`;
  - defines `triangleSplineSupportMeasureInputs`;
  - defines and discharges `TriangleSplineSupportMeasureTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS46.TriangleSplineSupportMeasure

rg -n "s[o]rry" TS\Goldbach\Strong\TS46
rg -n "a[x]iom" TS\Goldbach\Strong\TS46
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS46-M1 | `triangleSpline_support_volume_eq_two` | `repo_committed` | exact Lebesgue measure of `[-1, 1]` |
| TS46-M2 | `triangleSpline_support_volume_le_two` | `repo_committed` | support-measure upper bound |
| TS46-M3 | `TriangleSplineSupportMeasureInputs` | `repo_committed` | support-measure package |
| TS46-M4 | `triangleSplineSupportMeasureInputs` | `repo_committed` | concrete support-measure input |
| TS46-M5 | `TriangleSplineSupportMeasureTarget` | `repo_committed` | discharged support-measure target |
