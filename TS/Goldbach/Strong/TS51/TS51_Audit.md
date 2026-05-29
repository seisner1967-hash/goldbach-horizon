# TS51 - Triangle Spline Fourier Tail Comparison

## Status

TS51 isolates the final Fourier-tail comparison input needed by the
triangle-spline route.

Status: `repo_committed_relative`.

TS51 does not prove Plancherel, the Fourier derivative rule, Sobolev agreement,
or the concrete high-frequency tail estimate. It records the exact comparison
package that will later feed TS50 and therefore the TS42 triangle-spline route.

## Lean Files

- `TriangleSplineFourierTailComparison.lean`:
  - defines `triangleSplineComplex`;
  - defines `triangleSplineFourierTail`;
  - defines `TriangleSplineFourierTailComparisonInputs`;
  - defines `TriangleSplineFourierTailComparisonTarget`;
  - proves `triangleSpline_tail_snorm_le_one`;
  - defines `triangleSplineTailAssemblyInputs_from_fourierTailComparison`;
  - proves `triangleSplineTailAssemblyTarget_of_fourierTailComparisonTarget`;
  - proves `triangleSplineTailTarget_of_fourierTailComparisonTarget`;
  - proves `mellinTailContractTarget_of_fourierTailComparisonTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS51.TriangleSplineFourierTailComparison

rg -n "s[o]rry" TS\Goldbach\Strong\TS51
rg -n "a[x]iom" TS\Goldbach\Strong\TS51
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS51-F1 | `triangleSplineComplex` | `repo_committed_relative` | complex-valued triangle spline representative |
| TS51-F2 | `triangleSplineFourierTail` | `repo_committed_relative` | high-frequency tail representative |
| TS51-F3 | `TriangleSplineFourierTailComparisonInputs` | `analytic_infrastructure_obligation` | TS40/TS49-compatible tail comparison package |
| TS51-F4 | `TriangleSplineFourierTailComparisonTarget` | `repo_committed_relative` | target proposition for the comparison package |
| TS51-F5 | `triangleSpline_tail_snorm_le_one` | `repo_committed_relative` | extracts the explicit tail estimate from the package |
| TS51-F6 | `triangleSplineTailAssemblyInputs_from_fourierTailComparison` | `repo_committed_relative` | comparison package supplies TS50 assembly inputs |
| TS51-F7 | `mellinTailContractTarget_of_fourierTailComparisonTarget` | `repo_committed_relative` | comparison target gives a TS33 Mellin-tail contract target |

## Conclusion

TS51 replaces the informal TS50 tail marker with a precise Fourier-tail
comparison package. The route to `Cm <= 1` is now connected to an explicit
high-frequency `snorm <= 1` estimate, but remains conditional until the
Fourier-tail comparison is proved with concrete Mathlib Fourier normalization.
