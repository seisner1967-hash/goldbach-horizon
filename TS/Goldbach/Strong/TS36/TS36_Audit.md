# TS36 - Mellin-Fourier L2 Isometry Roadmap

## Status

TS36 packages the remaining `Lp`-level inputs needed to construct the concrete
Mellin-Fourier `L²` isometry.

Status: `repo_committed_relative`.

TS36 does not construct the final `LinearIsometryEquiv`. It records the exact
local infrastructure required after TS35: preservation of `Memℒp`, equality of
`snorm`, and a.e. linearity for the representative operators.

## Lean Files

- `MellinFourierLpIsometryRoadmap.lean`:
  - defines `MellinFourierLpIsometryInfrastructure`;
  - records `Memℒp` preservation for `TsigmaFun` and `TsigmaInvFun`;
  - records `snorm` preservation for both directions;
  - records a.e. additivity and scalar compatibility for both directions;
  - defines `MellinFourierLpIsometryRoadmap`;
  - defines the final fixed-`sigma` target proposition
    `MellinFourierLpIsometryTarget`;
  - exposes the TS35 quotient package via `ae_transport_of_roadmap`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS36.MellinFourierLpIsometryRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS36
rg -n "a[x]iom" TS\Goldbach\Strong\TS36
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS36-L1 | `MellinFourierLpIsometryInfrastructure` | `analytic_infrastructure_obligation` | `Memℒp`, `snorm`, and linearity inputs for `Lp` |
| TS36-L2 | `MellinFourierLpIsometryRoadmap` | `repo_committed_relative` | packages TS35 transport plus `Lp` infrastructure |
| TS36-L3 | `MellinFourierLpIsometryTarget` | `repo_committed_relative` | names the final fixed-`sigma` `LinearIsometryEquiv` target |
| TS36-L4 | `ae_transport_of_roadmap` | `repo_committed_relative` | exposes the TS35 quotient transport layer |

