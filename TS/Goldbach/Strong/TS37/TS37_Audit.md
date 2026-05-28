# TS37 - Mellin-Fourier Lp Norm Inputs

## Status

TS37 isolates the norm side of the future Mellin-Fourier `L²` isometry.

Status: `repo_committed_relative`.

TS37 does not prove quotient linearity, construct a `LinearIsometryEquiv`, or
touch Fourier-tail/Plancherel infrastructure. It records the exact `Memℒp` and
`snorm` preservation facts that should be proved before the final `Lp` layer is
assembled.

## Lean Files

- `MellinFourierLpNormInputs.lean`:
  - defines `MellinFourierLpNormInputs`;
  - records `Memℒp` preservation for `TsigmaFun`;
  - records `Memℒp` preservation for `TsigmaInvFun`;
  - records `snorm` preservation for `TsigmaFun`;
  - records `snorm` preservation for `TsigmaInvFun`;
  - defines `normInputsOfRoadmap`;
  - defines `MellinFourierLpNormInputsTarget`;
  - proves `normInputsTarget_of_roadmap`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS37.MellinFourierLpNormInputs

rg -n "s[o]rry" TS\Goldbach\Strong\TS37
rg -n "a[x]iom" TS\Goldbach\Strong\TS37
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS37-N1 | `MellinFourierLpNormInputs` | `analytic_infrastructure_obligation` | norm-side `Lp` inputs for the Mellin-Fourier bridge |
| TS37-N2 | `normInputsOfRoadmap` | `repo_committed_relative` | extracts the norm projection of the TS36 roadmap |
| TS37-N3 | `MellinFourierLpNormInputsTarget` | `repo_committed_relative` | names the standalone norm-input target |
| TS37-N4 | `normInputsTarget_of_roadmap` | `repo_committed_relative` | full TS36 roadmap implies the TS37 norm target |

