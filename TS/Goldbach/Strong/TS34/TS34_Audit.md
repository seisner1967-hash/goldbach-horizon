# TS34 - Mellin-Fourier Measure Transport

## Status

TS34 isolates the measure-transport obligations needed for a future concrete
Mellin/Fourier `L²` isometry.

Status: `repo_committed_relative`.

TS34 does not prove the logarithmic change-of-variable theorem, Plancherel, or
the `Lp`-level isometry. It records the exact almost-everywhere transport facts
needed before constructing the quotient-level Mellin/Fourier bridge.

## Lean Files

- `MellinFourierMeasureTransport.lean`:
  - defines `MellinFourierMeasureTransport`;
  - packages weighted-measure to restricted-Lebesgue transport;
  - packages restricted-Lebesgue to weighted-measure transport;
  - packages pullback by `Real.exp`;
  - packages pullback by `Real.log`;
  - proves `tsigmaFun_congr_of_measureTransport`;
  - proves `tsigmaInvFun_congr_of_measureTransport`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS34.MellinFourierMeasureTransport

rg -n "s[o]rry" TS\Goldbach\Strong\TS34
rg -n "a[x]iom" TS\Goldbach\Strong\TS34
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS34-M1 | `ae_volume_Ioi_of_ae_muWeighted` | `measure_infrastructure_obligation` | weighted Mellin measure to restricted Lebesgue |
| TS34-M2 | `ae_muWeighted_of_ae_volume_Ioi` | `measure_infrastructure_obligation` | restricted Lebesgue to weighted Mellin measure |
| TS34-M3 | `ae_volume_comp_exp_of_ae_volume_Ioi` | `measure_infrastructure_obligation` | pullback by exponential |
| TS34-M4 | `ae_volume_Ioi_comp_log_of_ae_volume` | `measure_infrastructure_obligation` | pullback by logarithm |
| TS34-M5 | `MellinFourierMeasureTransport` | `repo_committed_relative` | package for the four transport facts |
| TS34-C1 | `tsigmaFun_congr_of_measureTransport` | `repo_committed_relative` | transport implies `TsigmaFun` a.e. congruence |
| TS34-C2 | `tsigmaInvFun_congr_of_measureTransport` | `repo_committed_relative` | transport implies `TsigmaInvFun` a.e. congruence |

## Conclusion

TS34 separates the measure-theoretic part of the TS17 front from the future
`Lp` quotient construction:

```text
measure transport
=> Tsigma/TsigmaInv a.e. congruence
=> future AEEqFun/Lp bridge
```

The transport facts are still local infrastructure obligations, not hidden
global assumptions.
