# TS82 - Triangle Spline Sobolev API Reality Probe

## Status

TS82 records the current Sobolev/weak-derivative API state after TS81. A local
probe found Sobolev-inequality material in Mathlib, but no ready-made
weak-derivative/Sobolev representative API matching the TS41
`sobolevDerivative` slot.

Status: `repo_committed_relative`.

TS82 does not choose a concrete Fourier/Sobolev API, does not prove
weak-derivative uniqueness, and does not prove Plancherel or Fourier-tail
estimates. It defines the exact recognition contract that a future concrete
API proof must provide.

## Lean Files

- `TriangleSplineSobolevAPIRealityProbe.lean`:
  - defines `SobolevAPIProbeStatus`;
  - defines `TriangleSplineSobolevAPIRealityProbe`;
  - defines `triangleSplineSobolevAPIRealityProbe`;
  - defines `SobolevSlotRecognitionContract`;
  - defines `apiBinding_of_sobolevSlotRecognitionContract`;
  - defines `TriangleSplineSobolevAPIRealityProbeTarget`;
  - defines `SobolevSlotRecognitionContractTarget`;
  - proves `triangleSplineSobolevAPIRealityProbeTarget`;
  - proves `apiBindingTarget_of_recognitionContractTarget`;
  - proves `sobolevSlotAssemblyTarget_of_recognitionContractTarget`;
  - proves `sobolevAgreementLedgerTarget_of_recognitionContractTarget`;
  - proves `sobolevAgreementTarget_of_recognitionContractTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS82.TriangleSplineSobolevAPIRealityProbe

rg -n "s[o]rry" TS\Goldbach\Strong\TS82
rg -n "a[x]iom" TS\Goldbach\Strong\TS82
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS82-P0 | `TriangleSplineSobolevAPIRealityProbe` | `repo_committed` | records current Mathlib API state |
| TS82-C1 | `SobolevSlotRecognitionContract` | `analytic_infrastructure_obligation` | exact TS41 Sobolev-slot recognition contract |
| TS82-P1 | `apiBindingTarget_of_recognitionContractTarget` | `repo_committed_relative` | recognition contract implies TS81 target |
| TS82-P2 | `sobolevSlotAssemblyTarget_of_recognitionContractTarget` | `repo_committed_relative` | recognition contract implies TS80 target |
| TS82-P3 | `sobolevAgreementLedgerTarget_of_recognitionContractTarget` | `repo_committed_relative` | recognition contract implies TS55 target |
| TS82-P4 | `sobolevAgreementTarget_of_recognitionContractTarget` | `repo_committed_relative` | recognition contract implies TS49 target |

## Conclusion

TS82 keeps the Sobolev API boundary fail-closed. The remaining local obligation
is now the `SobolevSlotRecognitionContract`: a future concrete TS41 ledger must
prove that its `sobolevDerivative` slot recognizes `triangleSplineDeriv` as the
TS79 weak derivative of `triangleSpline`, almost everywhere.
