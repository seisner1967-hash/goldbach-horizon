TS192 Audit - Critical-Line Primitive Lower-Tail Limit

Scope

TS192 continues the TS191 critical-line energy computation.  TS191 proved the
support-side square expansion of the critical-line amplitude and the exact
upper-endpoint primitive value

`criticalLineAmplitudeEnergyPrimitive X (log X) = X / 3`.

TS192 proves the missing lower-tail boundary value: the same primitive tends
to `0` as `u -> -infty`.

Main declarations

- `TS192.Goldbach.tendsto_exp_two_mul_atBot_zero`
- `TS192.Goldbach.tendsto_exp_three_mul_atBot_zero`
- `TS192.Goldbach.criticalLineAmplitudeEnergyPrimitive_tendsto_atBot_zero`
- `TS192.Goldbach.CriticalLinePrimitiveBoundaryStatement`
- `TS192.Goldbach.criticalLinePrimitiveBoundaryStatement`
- `TS192.Goldbach.CriticalLineImproperEnergyFTCContract`
- `TS192.Goldbach.CriticalLinePrimitiveLowerTailLimitLedger`
- `TS192.Goldbach.criticalLinePrimitiveLowerTailLimitLedger`
- `TS192.Goldbach.CriticalLinePrimitiveLowerTailLimitTarget`
- `TS192.Goldbach.criticalLinePrimitiveLowerTailLimitTarget`

What TS192 proves

TS192 proves the elementary lower-tail exponential decay facts:

`exp (2*u) -> 0` as `u -> -infty`

and

`exp (3*u) -> 0` as `u -> -infty`.

It then proves

`criticalLineAmplitudeEnergyPrimitive X u -> 0`

as `u -> -infty` for every natural scale `X`.  This combines with the TS191
upper-endpoint result into `CriticalLinePrimitiveBoundaryStatement`.

Contract still registered

TS192 defines `CriticalLineImproperEnergyFTCContract` for the remaining
improper-integral and FTC step.  The integral proposition is supplied as a
field of the contract, so the full integral theorem is not hidden behind a
trivial placeholder.

Non-claims

TS192 does not claim:

- The full Lebesgue improper integral over `(-infty, log X]`.
- The Wall 0 measure transport `dx / x = du`.
- The Mellin-as-Fourier integral equivalence.
- The contour explicit formula.
- Zeta-zero summability.
- Goldbach.

Verification commands

```powershell
lake build TS.Goldbach.Strong.TS192.CriticalLinePrimitiveLowerTailLimit
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS192
git diff --check
git status --short
```

Expected result: build succeeds, the audit grep returns no matches, and the
diff is whitespace-clean.
