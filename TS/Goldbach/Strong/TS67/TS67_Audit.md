# TS67 - Triangle Spline IPP Integral Restriction

## Status

TS67 records the integral-level restriction contract for the two concrete
triangle-spline integration-by-parts products.

Status: `repo_committed_relative`.

TS67 does not prove the restriction of global Bochner integrals to `[-1, 1]`,
does not split `[-1, 1]` into branches, and does not prove the
integration-by-parts identity. It fixes the exact theorem shape that will
turn TS65 integrability plus TS66 pointwise support restriction into
integral-level restriction.

## Lean Files

- `TriangleSplineIPPIntegralRestriction.lean`:
  - defines `leftIPPIntegrand`;
  - defines `rightIPPIntegrand`;
  - defines `TriangleSplineIPPIntegralRestrictionInputs`;
  - defines `triangleSplineIPPIntegralRestrictionInputs`;
  - defines `TriangleSplineIPPIntegralRestriction`;
  - defines `TriangleSplineIPPIntegralRestrictionTarget`;
  - proves `triangleSplineIPPIntegralRestrictionInputsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS67.TriangleSplineIPPIntegralRestriction

rg -n "s[o]rry" TS\Goldbach\Strong\TS67
rg -n "a[x]iom" TS\Goldbach\Strong\TS67
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS67-R1 | `leftIPPIntegrand` | `repo_committed_relative` | named left IPP product |
| TS67-R2 | `rightIPPIntegrand` | `repo_committed_relative` | named right IPP product |
| TS67-R3 | `TriangleSplineIPPIntegralRestrictionInputs` | `repo_committed` | TS65 integrability plus TS66 support inputs |
| TS67-R4 | `TriangleSplineIPPIntegralRestriction` | `analytic_infrastructure_obligation` | integral restriction to `[-1, 1]` |
| TS67-R5 | `TriangleSplineIPPIntegralRestrictionTarget` | `repo_committed_relative` | target proposition |

## Conclusion

TS67 fixes the integral-restriction theorem shape without proving it. The next
sprint can attempt to prove the two equality fields using TS65 integrability,
TS66 support restriction, and the available Mathlib API for restricted
measures or indicators.
