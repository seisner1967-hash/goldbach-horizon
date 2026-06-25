# TS194 Audit - Critical-Line Actual Amplitude Energy Bridge

## Scope

TS194 connects the TS193 expanded-density energy computation back to the
actual TS190 critical-line amplitude.  TS193 proved that the truncated
integrals of `criticalLineAmplitudeEnergyExpandedDensity X` converge to
`X / 3` as the lower endpoint tends to `-infty`.  TS194 proves that the
truncated integrals of the actual squared amplitude
`(triangleSplineCriticalAmplitude X u)^2` eventually agree with those
expanded-density integrals, and therefore have the same limit.

This sprint does not introduce a standalone improper integral object.  It
keeps that promotion as a local future contract.

## Main declarations

- `TS194.Goldbach.criticalLineTruncatedActualEnergy`
- `TS194.Goldbach.criticalLineActualEnergy_eq_expanded_on_truncated_interval`
- `TS194.Goldbach.criticalLineTruncatedActualEnergy_eq_expanded_of_le_log`
- `TS194.Goldbach.criticalLineTruncatedActualEnergy_tendsto_X_div_three`
- `TS194.Goldbach.CriticalLineActualImproperEnergyObjectContract`
- `TS194.Goldbach.CriticalLineActualAmplitudeEnergyBridgeLedger`
- `TS194.Goldbach.criticalLineActualAmplitudeEnergyBridgeLedger`
- `TS194.Goldbach.CriticalLineActualAmplitudeEnergyBridgeTarget`
- `TS194.Goldbach.criticalLineActualAmplitudeEnergyBridgeTarget`

## What TS194 proves

For every `X > 0`, TS194 proves

```lean
Tendsto
  (fun a : Real => criticalLineTruncatedActualEnergy X a)
  atBot
  (nhds ((X : Real) / 3))
```

The proof uses the eventual range `a <= log X`.  On that range, every point of
the directed interval `a..log X` lies on the support side `exp u <= X`, so the
TS191 pointwise expansion identifies the actual squared critical amplitude with
the expanded energy density.  The TS193 convergence theorem then transfers the
limit `X / 3`.

## Non-claims

TS194 deliberately does not prove:

- a standalone improper Lebesgue integral object;
- the Wall 0 measure transport `dx / x = du`;
- the Mellin-as-Fourier integral equivalence;
- Plancherel;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- Goldbach.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS194.CriticalLineActualAmplitudeEnergyBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS194
git diff --check
git status --short
```
