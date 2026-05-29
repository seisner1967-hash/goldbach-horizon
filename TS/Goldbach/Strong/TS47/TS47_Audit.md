# TS47 - Triangle Spline Snorm Discharge Bridge

## Status

TS47 reduces the triangle-spline derivative `snorm <= 2` estimate to a generic
bounded-support `snorm` lemma.

Status: `repo_committed_relative`.

TS47 does not prove the generic `snorm` lemma, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate. It connects the already proved TS43,
TS44, and TS46 facts to the TS45 snorm infrastructure.

## Lean Files

- `TriangleSplineSnormDischarge.lean`:
  - defines `BoundedSupportSnormLemma`;
  - proves `triangleSplineDeriv_complex_measurable`;
  - proves `triangleSplineDeriv_complex_norm_le_one`;
  - defines `triangleSplineDerivativeSnormInfrastructure`;
  - proves `triangleSplineDerivativeSnormTarget_of_boundedSupportLemma`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS47.TriangleSplineSnormDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS47
rg -n "a[x]iom" TS\Goldbach\Strong\TS47
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS47-N1 | `BoundedSupportSnormLemma` | `analytic_infrastructure_obligation` | generic bounded-support L2 estimate |
| TS47-N2 | `triangleSplineDeriv_complex_measurable` | `repo_committed` | complexified derivative measurability |
| TS47-N3 | `triangleSplineDeriv_complex_norm_le_one` | `repo_committed` | complexified pointwise norm bound |
| TS47-N4 | `triangleSplineDerivativeSnormInfrastructure` | `repo_committed_relative` | applies generic lemma to triangle spline |
| TS47-N5 | `triangleSplineDerivativeSnormTarget_of_boundedSupportLemma` | `repo_committed_relative` | discharges TS45 target conditionally |
