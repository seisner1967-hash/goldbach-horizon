# TS38 - Mellin-Fourier Lp Linearity Inputs

## Status

TS38 isolates the almost-everywhere linearity side of the future
Mellin-Fourier `L²` isometry.

Status: `repo_committed_relative`.

TS38 does not prove pointwise linearity, construct a `LinearIsometryEquiv`, or
touch Fourier-tail/Plancherel infrastructure. It records the a.e. additivity
and scalar-compatibility inputs needed for the future `Lp`-level
Mellin-Fourier isometry.

## Lean Files

- `MellinFourierLpLinearityInputs.lean`:
  - defines `MellinFourierLpLinearityInputs`;
  - records a.e. additivity for `TsigmaFun`;
  - records a.e. scalar compatibility for `TsigmaFun`;
  - records a.e. additivity for `TsigmaInvFun`;
  - records a.e. scalar compatibility for `TsigmaInvFun`;
  - defines `lpInfrastructureOfNormAndLinearity`;
  - defines `linearityInputsOfRoadmap`;
  - defines `MellinFourierLpLinearityInputsTarget`;
  - proves `linearityTarget_of_roadmap`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS38.MellinFourierLpLinearityInputs

rg -n "s[o]rry" TS\Goldbach\Strong\TS38
rg -n "a[x]iom" TS\Goldbach\Strong\TS38
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS38-L1 | `MellinFourierLpLinearityInputs` | `analytic_infrastructure_obligation` | a.e. additivity and scalar compatibility inputs |
| TS38-L2 | `lpInfrastructureOfNormAndLinearity` | `repo_committed_relative` | combines TS37 norm inputs with TS38 linearity inputs |
| TS38-L3 | `linearityInputsOfRoadmap` | `repo_committed_relative` | extracts the linearity projection of TS36 |
| TS38-L4 | `MellinFourierLpLinearityInputsTarget` | `repo_committed_relative` | names the standalone linearity target |
| TS38-L5 | `linearityTarget_of_roadmap` | `repo_committed_relative` | full TS36 roadmap implies the TS38 linearity target |

