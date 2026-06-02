# TS64 - Triangle Spline IPP Integrability Inputs

## Status

TS64 records the Bochner-integrability inputs needed before proving the
concrete TS63 integration-by-parts identity.

Status: `repo_committed_relative`.

TS64 does not prove the integration-by-parts identity, does not prove the
distributional derivative identity, and does not prove Sobolev-slot agreement,
Plancherel, or Fourier-tail estimates. It isolates the two product
integrability facts needed before future branchwise integral splitting.

## Lean Files

- `TriangleSplineIPPIntegrabilityInputs.lean`:
  - defines `TriangleSplineIPPIntegrabilityInputs`;
  - defines `TriangleSplineIPPIntegrabilityTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS64.TriangleSplineIPPIntegrabilityInputs

rg -n "s[o]rry" TS\Goldbach\Strong\TS64
rg -n "a[x]iom" TS\Goldbach\Strong\TS64
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS64-I1 | `TriangleSplineIPPIntegrabilityInputs` | `analytic_infrastructure_obligation` | integrability of the two IPP products |
| TS64-I2 | `TriangleSplineIPPIntegrabilityTarget` | `repo_committed_relative` | target proposition |

## Conclusion

TS64 keeps the IPP route fail-closed: the concrete TS63 weak-derivative
identity will be attacked only after the two Bochner-integrability inputs are
available.
