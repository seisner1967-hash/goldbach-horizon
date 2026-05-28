# TS42 - Mellin Tail Spline Roadmap

## Status

TS42 records the triangle-spline route toward the Mellin-tail majorant contract
`Cm <= 1`.

Status: `repo_committed_relative`.

TS42 does not prove the Lebesgue integral of the derivative, the Sobolev
derivative identity, Plancherel, or the Fourier-tail estimate. It exposes these
facts as local analytic infrastructure obligations.

## Lean Files

- `MellinTailSplineRoadmap.lean`:
  - defines `triangleSpline`;
  - defines `triangleSplineDeriv`;
  - defines `TriangleSplineTailInfrastructure`;
  - defines `mellinTailContract_from_triangleSpline`;
  - defines `TriangleSplineTailTarget`;
  - proves `mellinTailContract_target_of_triangleSplineTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS42.MellinTailSplineRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS42
rg -n "a[x]iom" TS\Goldbach\Strong\TS42
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS42-S1 | `triangleSpline` | `repo_committed_relative` | triangle smoothing profile |
| TS42-S2 | `triangleSplineDeriv` | `repo_committed_relative` | piecewise weak-derivative representative |
| TS42-S3 | `TriangleSplineTailInfrastructure` | `analytic_infrastructure_obligation` | derivative norm + Sobolev agreement + tail route |
| TS42-S4 | `mellinTailContract_from_triangleSpline` | `repo_committed_relative` | local infrastructure gives `Cm <= 1` contract |
| TS42-S5 | `TriangleSplineTailTarget` | `repo_committed_relative` | target proposition for the spline route |
| TS42-S6 | `mellinTailContract_target_of_triangleSplineTarget` | `repo_committed_relative` | target supplies a TS33 Mellin-tail contract |
