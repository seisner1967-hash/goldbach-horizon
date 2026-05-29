# TS50 - Triangle Spline Tail Assembly

## Status

TS50 assembles the triangle-spline route toward the Mellin-tail majorant.

Status: `repo_committed_relative`.

TS50 uses the concrete TS48 `snorm` discharge and the TS49 Sobolev-agreement
infrastructure, while leaving the final Fourier-tail comparison as an explicit
local input. It does not prove Sobolev agreement, Plancherel, or Fourier-tail
decay.

## Lean Files

- `TriangleSplineTailAssembly.lean`:
  - defines `TriangleSplineTailAssemblyInputs`;
  - proves `triangleSplineDeriv_snorm_bound`;
  - defines `triangleSplineTailInfrastructure_from_inputs`;
  - defines `TriangleSplineTailAssemblyTarget`;
  - proves `triangleSplineTailTarget_of_assembly`;
  - defines `mellinTailContract_from_triangleSplineAssembly`;
  - proves `mellinTailContractTarget_of_assemblyTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS50.TriangleSplineTailAssembly

rg -n "s[o]rry" TS\Goldbach\Strong\TS50
rg -n "a[x]iom" TS\Goldbach\Strong\TS50
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS50-A1 | `TriangleSplineTailAssemblyInputs` | `analytic_infrastructure_obligation` | Sobolev agreement plus final tail comparison input |
| TS50-A2 | `triangleSplineDeriv_snorm_bound` | `repo_committed` | extracts the concrete TS48 derivative `snorm <= 2` bound |
| TS50-A3 | `triangleSplineTailInfrastructure_from_inputs` | `repo_committed_relative` | assembles the TS42 infrastructure conditionally |
| TS50-A4 | `TriangleSplineTailAssemblyTarget` | `repo_committed_relative` | target proposition for the assembly inputs |
| TS50-A5 | `triangleSplineTailTarget_of_assembly` | `repo_committed_relative` | assembly inputs imply the TS42 spline target |
| TS50-A6 | `mellinTailContract_from_triangleSplineAssembly` | `repo_committed_relative` | assembly input yields the TS33 Mellin-tail contract |
| TS50-A7 | `mellinTailContractTarget_of_assemblyTarget` | `repo_committed_relative` | assembly target gives a Mellin-tail contract target |

## Conclusion

TS50 verifies the logical wiring from the concrete TS48 norm estimate and the
TS49 Sobolev-agreement interface into the TS42 triangle-spline tail package.
The route to `Cm <= 1` is connected, but remains conditional on Sobolev
agreement and the Fourier-tail comparison.
