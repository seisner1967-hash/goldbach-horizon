# TS197 Audit - Critical-Line X-Side Interval Convergence Bridge

## Scope

TS197 transfers the TS194 critical-line truncated-energy convergence across the
compact change of variables proved in TS196.

TS196 proved a compact set-integral identity under `x = exp u`.  TS197 adds the
missing bridge to the TS194 interval-integral convergence theorem: it identifies
the compact set integral over `Icc a (log X)` with the directed interval
integral over `a..log X`, then proves that the x-side compact energies with
lower endpoint `exp a` converge to `X / 3` as `a -> -infty`.

## Main declarations

- `TS197.Goldbach.criticalLineTruncatedXSideEnergy`
- `TS197.Goldbach.compactActualEnergy_setIntegral_eq_truncatedActual`
- `TS197.Goldbach.criticalLineTruncatedXSideEnergy_comp_exp_eq`
- `TS197.Goldbach.criticalLineTruncatedXSideEnergy_comp_exp_tendsto`
- `TS197.Goldbach.CriticalLineXSideImproperEnergyObjectContract`
- `TS197.Goldbach.CriticalLineXSideIntervalConvergenceBridgeLedger`
- `TS197.Goldbach.criticalLineXSideIntervalConvergenceBridgeLedger`
- `TS197.Goldbach.CriticalLineXSideIntervalConvergenceBridgeTarget`
- `TS197.Goldbach.criticalLineXSideIntervalConvergenceBridgeTarget`

## What TS197 proves

TS197 defines the compact x-side truncated energy as

```lean
MeasureTheory.integral
  (volume.restrict (Set.Icc b (X : Real)))
  (fun x : Real => TS196.Goldbach.criticalLineXSideEnergyDensity X x)
```

It proves that, for `a <= log X`,

```lean
criticalLineTruncatedXSideEnergy X (Real.exp a) =
  TS194.Goldbach.criticalLineTruncatedActualEnergy X a
```

using TS196's compact change of variables and the boundary-insensitive
conversion between `Icc` set integrals and `Ioc` interval integrals.  It then
transfers the TS194 limit and proves

```lean
Tendsto
  (fun a : Real => criticalLineTruncatedXSideEnergy X (Real.exp a))
  atBot
  (nhds ((X : Real) / 3))
```

for `X > 0`.

## Non-claims

TS197 deliberately does not prove:

- a standalone improper Lebesgue integral object on `(0, X]`;
- the full Wall 0 measure transport;
- the Haar/multiplicative transport `dx / x = du`;
- the Mellin-as-Fourier integral equivalence;
- Plancherel;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- circle-method or Gallagher correlation;
- Goldbach.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS197.CriticalLineXSideIntervalConvergenceBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS197
git diff --check
git status --short
```
