# TS45 - Triangle Spline Derivative Snorm Roadmap

## Status

TS45 isolates the `L2`/`snorm` estimate needed for the triangle-spline weak
derivative representative.

Status: `repo_committed_relative`.

TS45 does not prove the Lebesgue integral, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate. It packages the already-proved
TS43/TS44 elementary inputs and records the remaining `snorm <= 2` estimate as
a local infrastructure obligation.

## Lean Files

- `TriangleSplineDerivativeSnorm.lean`:
  - defines `TriangleSplineDerivativeSnormInputs`;
  - defines `triangleSplineDerivativeSnormInputs`;
  - defines `TriangleSplineDerivativeSnormInfrastructure`;
  - proves `deriv_snorm_bound_of_infrastructure`;
  - defines and discharges `TriangleSplineDerivativeSnormInputsTarget`;
  - defines `TriangleSplineDerivativeSnormTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS45.TriangleSplineDerivativeSnorm

rg -n "s[o]rry" TS\Goldbach\Strong\TS45
rg -n "a[x]iom" TS\Goldbach\Strong\TS45
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS45-N1 | `TriangleSplineDerivativeSnormInputs` | `repo_committed` | packages TS43 pointwise bound and TS44 support/measurability |
| TS45-N2 | `triangleSplineDerivativeSnormInputs` | `repo_committed` | concrete elementary inputs |
| TS45-N3 | `TriangleSplineDerivativeSnormInfrastructure` | `analytic_infrastructure_obligation` | local `snorm <= 2` obligation |
| TS45-N4 | `deriv_snorm_bound_of_infrastructure` | `repo_committed_relative` | exposes the infrastructure bound |
| TS45-N5 | `TriangleSplineDerivativeSnormInputsTarget` | `repo_committed` | elementary input target |
| TS45-N6 | `TriangleSplineDerivativeSnormTarget` | `repo_committed_relative` | target proposition for the snorm estimate |
