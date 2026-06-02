# TS65 - Triangle Spline IPP Integrability Discharge

## Status

TS65 proves the two Bochner-integrability inputs isolated in TS64 for the
concrete TS62 test-function API.

Status: `repo_committed`.

TS65 does not prove the integration-by-parts identity, does not prove the
distributional derivative identity, and does not prove Sobolev-slot agreement,
Plancherel, or Fourier-tail estimates. It only discharges the integrability
side needed before future branchwise IPP splitting.

## Lean Files

- `TriangleSplineIPPIntegrabilityDischarge.lean`:
  - proves measurability and boundedness of the complex-valued triangle spline;
  - proves integrability of concrete TS62 test functions and their derivative
    representatives;
  - proves the two product integrability facts from TS64;
  - defines `triangleSplineIPPIntegrabilityInputs`;
  - proves `triangleSplineIPPIntegrabilityTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS65.TriangleSplineIPPIntegrabilityDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS65
rg -n "a[x]iom" TS\Goldbach\Strong\TS65
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS65-I1 | `triangleSpline_complex_measurable` | `repo_committed` | measurable complex-valued triangle spline |
| TS65-I2 | `triangleSpline_complex_norm_le_two` | `repo_committed` | pointwise bound used by `Integrable.bdd_mul` |
| TS65-I3 | `testFunction_integrable` | `repo_committed` | compact-support integrability for TS62 test functions |
| TS65-I4 | `testFunction_deriv_integrable` | `repo_committed` | compact-support integrability for `derivFun` |
| TS65-I5 | `triangleSpline_mul_testFunctionDeriv_integrable` | `repo_committed` | left IPP product integrability |
| TS65-I6 | `triangleSplineDeriv_mul_testFunction_integrable` | `repo_committed` | right IPP product integrability |
| TS65-I7 | `triangleSplineIPPIntegrabilityInputs` | `repo_committed` | concrete TS64 input package |

## Conclusion

TS65 closes the TS64 integrability layer. The next IPP-side sprint can focus on
branchwise restriction/splitting and affine integration by parts, without
carrying the two global product-integrability obligations.
