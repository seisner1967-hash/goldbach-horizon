# TS35 - Mellin-Fourier AEEqFun Transport

## Status

TS35 crosses the almost-everywhere quotient layer for the Mellin-Fourier
representative operators.

Status: `repo_committed_relative`.

TS35 does not prove the `Lp` isometry, Plancherel, or any Fourier-tail bound.
It combines the TS34 measure transport package with a local strong
measurability contract, then feeds those facts into the already compiled TS17
`AEEqFun` quotient construction.

## Lean Files

- `MellinFourierAEEqTransport.lean`:
  - defines `MellinFourierMeasurabilityTransport`;
  - defines `MellinFourierAEEqTransport`;
  - converts the TS35 package to the TS17 fixed-`sigma` transport package via
    `toTS17AEEqTransport`;
  - re-exports `TsigmaAEEqFun` and `TsigmaInvAEEqFun`;
  - proves `TsigmaInvAEEqFun_left` and `TsigmaInvAEEqFun_right`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS35.MellinFourierAEEqTransport

rg -n "s[o]rry" TS\Goldbach\Strong\TS35
rg -n "a[x]iom" TS\Goldbach\Strong\TS35
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS35-M1 | `MellinFourierMeasurabilityTransport` | `analytic_infrastructure_obligation` | strong measurability for `TsigmaFun` and `TsigmaInvFun` |
| TS35-A1 | `MellinFourierAEEqTransport` | `repo_committed_relative` | packages TS34 measure transport plus measurability |
| TS35-A2 | `toTS17AEEqTransport` | `repo_committed_relative` | feeds TS34 congruence into the TS17 quotient API |
| TS35-A3 | `TsigmaAEEqFun` / `TsigmaInvAEEqFun` | `repo_committed_relative` | descended operators on `AEEqFun` |
| TS35-A4 | `TsigmaInvAEEqFun_left` / `TsigmaInvAEEqFun_right` | `repo_committed_relative` | inverse laws on `AEEqFun` |

