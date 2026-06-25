TS191 Audit - Critical-Line Amplitude Energy Primitive

Scope

TS191 continues the TS189/TS190 work on Wall 0 by extracting the exact
algebraic energy calculation for the critical-line logarithmic amplitude.

TS190 proved that, on the support side `exp u <= X`, the amplitude is

`(1 - exp u / X) * exp (u / 2)`.

TS191 squares that expression, rewrites it as an elementary exponential
density, and evaluates the natural primitive at the upper endpoint `log X`.
This proves the algebraic core of the paper calculation whose final improper
integral should be `X / 3`.

Main declarations

- `TS191.Goldbach.criticalLineAmplitudeEnergyDensity`
- `TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity`
- `TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive`
- `TS191.Goldbach.criticalLineAmplitudeEnergyDensity_eq_expanded_of_exp_le_X`
- `TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive_at_log_eq_X_div_three`
- `TS191.Goldbach.CriticalLineAmplitudeImproperEnergyContract`
- `TS191.Goldbach.CriticalLineAmplitudeEnergyPrimitiveLedger`
- `TS191.Goldbach.criticalLineAmplitudeEnergyPrimitiveLedger`
- `TS191.Goldbach.CriticalLineAmplitudeEnergyPrimitiveTarget`
- `TS191.Goldbach.criticalLineAmplitudeEnergyPrimitiveTarget`

What TS191 proves

For every positive natural scale `X`, TS191 proves the support-side square
expansion

`criticalLineAmplitudeEnergyDensity X u =
 criticalLineAmplitudeEnergyExpandedDensity X u`

whenever `exp u <= X`.

It also proves the exact endpoint primitive evaluation

`criticalLineAmplitudeEnergyPrimitive X (log X) = X / 3`.

This is the finite algebraic heart of the critical-line energy computation.

What remains contract-only

TS191 registers a local `CriticalLineAmplitudeImproperEnergyContract` for the
remaining improper-integral step.  A future sprint must still prove the
lower-tail vanishing from `-infty` and promote the primitive calculation into
the exact Lebesgue or improper integral statement.

Non-claims

TS191 does not claim:

- The full improper integral over `(-infty, log X]`.
- The Wall 0 measure transport `dx / x = du`.
- The Mellin-as-Fourier integral equivalence.
- The contour explicit formula.
- Zeta-zero summability.
- Goldbach.

Verification commands

```powershell
lake build TS.Goldbach.Strong.TS191.CriticalLineAmplitudeEnergyPrimitive
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS191
git diff --check
git status --short
```

Expected result: build succeeds, the audit grep returns no matches, and the
diff is whitespace-clean.
