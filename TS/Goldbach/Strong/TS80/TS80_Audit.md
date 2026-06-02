# TS80 - Triangle Spline Sobolev Slot Assembly

## Status

TS80 packages the proved TS60 a.e. classical derivative input and the proved
TS79 abstract distributional derivative input. It isolates the remaining exact
TS41 Sobolev-slot agreement and proves that this single slot agreement is
sufficient to discharge the TS55 ledger target and the TS49 Sobolev-agreement
target.

Status: `repo_committed_relative`.

TS80 does not fabricate a concrete Fourier/Sobolev API instance. It keeps the
remaining `api.sobolevDerivative` agreement as an explicit local obligation.
It does not prove Plancherel or Fourier-tail estimates.

## Lean Files

- `TriangleSplineSobolevSlotAssembly.lean`:
  - defines `TriangleSplineSobolevSlotAssemblyInputs`;
  - defines `triangleSplineSobolevSlotAssemblyInputs`;
  - defines `TriangleSplineSobolevSlotAssembly`;
  - defines `triangleSplineSobolevAgreementLedger`;
  - defines `triangleSplineSobolevAgreementInfrastructure`;
  - defines `TriangleSplineSobolevSlotAssemblyTarget`;
  - defines `TriangleSplineSobolevSlotAssemblyInputsTarget`;
  - proves `triangleSplineSobolevSlotAssemblyInputsTarget`;
  - proves `triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget`;
  - proves `triangleSplineSobolevAgreementTarget_of_slotAssemblyTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS80.TriangleSplineSobolevSlotAssembly

rg -n "s[o]rry" TS\Goldbach\Strong\TS80
rg -n "a[x]iom" TS\Goldbach\Strong\TS80
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS80-I1 | `TriangleSplineSobolevSlotAssemblyInputs` | `repo_committed` | packages TS60 and TS79 |
| TS80-I2 | `triangleSplineSobolevSlotAssemblyInputsTarget` | `repo_committed` | proved input target |
| TS80-C1 | `TriangleSplineSobolevSlotAssembly` | `analytic_infrastructure_obligation` | exact TS41 Sobolev-slot agreement |
| TS80-P1 | `triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget` | `repo_committed_relative` | TS80 target implies TS55 target |
| TS80-P2 | `triangleSplineSobolevAgreementTarget_of_slotAssemblyTarget` | `repo_committed_relative` | TS80 target implies TS49 target |

## Conclusion

TS80 makes the remaining Sobolev gap precise: after TS60 and TS79, the only
local Sobolev-side obligation is the agreement of the chosen TS41
`sobolevDerivative` slot with `triangleSplineDeriv`.
