# TS198 Audit - Critical-Line X-Side Improper Energy Object

## Scope

TS198 mirrors the TS195 logarithmic-side energy object in the original
coordinate.  TS197 had proved that the x-side compact energies with lower
endpoint `exp a` tend to `X / 3` as `a -> -infty`.  TS198 packages that
convergence as a named limit-based object and also rewrites the same convergence
in the natural x-side filter `b -> 0+`.

The sprint does not define a general Lebesgue improper integral over `(0, X]`.
It stores a real value together with the convergence certificates needed by
later contracts.

## Main declarations

- `TS198.Goldbach.CriticalLineXSideImproperEnergyObject`
- `TS198.Goldbach.criticalLineTruncatedXSideEnergy_tendsto_nhdsGT_zero`
- `TS198.Goldbach.criticalLineXSideImproperEnergyObject`
- `TS198.Goldbach.criticalLineXSideImproperEnergy`
- `TS198.Goldbach.criticalLineXSideImproperEnergyObject_value`
- `TS198.Goldbach.criticalLineXSideImproperEnergy_eq_X_div_three`
- `TS198.Goldbach.xSideImproperEnergyObject_satisfies_contract`
- `TS198.Goldbach.CriticalLineXSideImproperEnergyObjectLedger`
- `TS198.Goldbach.criticalLineXSideImproperEnergyObjectLedger`
- `TS198.Goldbach.CriticalLineXSideImproperEnergyObjectTarget`
- `TS198.Goldbach.criticalLineXSideImproperEnergyObjectTarget`

## What is proved

TS198 proves that the TS197 x-side convergence can be read in the original
coordinate filter:

```lean
Tendsto
  (fun b : Real =>
    TS197.Goldbach.criticalLineTruncatedXSideEnergy X b)
  (nhdsWithin 0 (Set.Ioi 0))
  (nhds ((X : Real) / 3))
```

This is obtained from `Real.tendsto_comp_exp_atBot` and the TS197 theorem
`criticalLineTruncatedXSideEnergy_comp_exp_tendsto`.

It then defines the canonical x-side improper-energy object with value
`(X : Real) / 3`, proves that the scalar wrapper evaluates to `X / 3`, and
shows that the local TS197 object contract is consumed by the TS197 convergence
theorem.

## Non-claims

TS198 does not prove:

- a standalone general Lebesgue improper integral over `(0, X]`;
- the full Wall 0 measure transport;
- Haar transport `dx / x = du`;
- Mellin-as-Fourier compatibility;
- Plancherel;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- circle-method or Gallagher correlation;
- Goldbach.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS198.CriticalLineXSideImproperEnergyObject
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS198
git diff --check
git status --short
```
