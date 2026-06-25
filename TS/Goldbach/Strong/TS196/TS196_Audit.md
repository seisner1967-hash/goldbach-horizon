# TS196 Audit - Critical-Line Compact Change-of-Variables Probe

## Scope

TS196 attacks the compact part of Wall 0, the logarithmic change of variables
between critical-line coordinates and original coordinates.  It does not prove
the full improper measure transport `dx / x = du`, and it does not identify
the Mellin and Fourier transforms.

Instead, TS196 proves a finite compact set-integral change of variables for the
concrete critical-line energy density.  On compact intervals ending at `log X`,
the actual squared critical-line amplitude is the Jacobian-weighted pullback
of the original-coordinate triangle-spline square density under `x = exp u`.

## Main declarations

- `TS196.Goldbach.criticalLineXSideEnergyDensity`
- `TS196.Goldbach.criticalLineCompactLogEnergyDensity`
- `TS196.Goldbach.criticalLineActualSquare_eq_compactLogDensity`
- `TS196.Goldbach.exp_image_Icc_log`
- `TS196.Goldbach.exp_hasDerivWithinAt_Icc`
- `TS196.Goldbach.exp_injOn_Icc`
- `TS196.Goldbach.compactChangeOfVariables_xSide_eq_logSide`
- `TS196.Goldbach.compactActualEnergy_setIntegral_eq_xSide`
- `TS196.Goldbach.CompactChangeOfVariablesProbeOutcome`
- `TS196.Goldbach.CriticalLineCompactChangeOfVariablesLedger`
- `TS196.Goldbach.criticalLineCompactChangeOfVariablesLedger`
- `TS196.Goldbach.CriticalLineCompactChangeOfVariablesTarget`
- `TS196.Goldbach.criticalLineCompactChangeOfVariablesTarget`

## What TS196 proves

TS196 proves the pointwise identity

```lean
(TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2 =
  criticalLineCompactLogEnergyDensity X u
```

where the compact logarithmic density is

```lean
Real.exp u * criticalLineXSideEnergyDensity X (Real.exp u)
```

It also proves the compact image identity

```lean
Real.exp '' Set.Icc a (Real.log (X : Real)) =
  Set.Icc (Real.exp a) (X : Real)
```

for `X > 0`, and uses Mathlib's one-dimensional Jacobian theorem
`integral_image_eq_integral_abs_deriv_smul` to prove the compact set-integral
change of variables.  Finally, it combines this with the pointwise identity to
show that the compact logarithmic set integral of the actual squared amplitude
equals the compact original-coordinate square-energy set integral.

## Non-claims

TS196 deliberately does not prove:

- the full improper Wall 0 measure transport;
- the Haar/multiplicative transport `dx / x = du`;
- the Mellin-as-Fourier integral equivalence;
- the interval-integral/improper bridge from TS194/TS195 to the x-side object;
- Plancherel;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- circle-method or Gallagher correlation;
- Goldbach.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS196.CriticalLineCompactChangeOfVariablesProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS196
git diff --check
git status --short
```
