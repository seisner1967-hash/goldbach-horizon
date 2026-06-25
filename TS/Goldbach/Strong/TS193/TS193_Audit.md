TS193 Audit - Critical-Line Truncated FTC Energy Bridge

Scope

TS193 continues the TS191/TS192 critical-line energy computation.  TS191
proved the upper endpoint value of the primitive, and TS192 proved the
lower-tail limit of the same primitive.  TS193 proves the finite-interval FTC
bridge that turns those boundary values into a convergence theorem for
truncated interval integrals.

Main declarations

- `TS193.Goldbach.criticalLineEnergyPrimitive_hasDerivAt`
- `TS193.Goldbach.criticalLineExpandedDensity_intervalIntegrable`
- `TS193.Goldbach.criticalLineTruncatedExpandedEnergy`
- `TS193.Goldbach.criticalLineTruncatedExpandedEnergy_eq_primitive_sub`
- `TS193.Goldbach.criticalLineTruncatedExpandedEnergy_tendsto_X_div_three`
- `TS193.Goldbach.CriticalLineImproperIntegralObjectContract`
- `TS193.Goldbach.CriticalLineTruncatedFTCEnergyBridgeLedger`
- `TS193.Goldbach.criticalLineTruncatedFTCEnergyBridgeLedger`
- `TS193.Goldbach.CriticalLineTruncatedFTCEnergyBridgeTarget`
- `TS193.Goldbach.criticalLineTruncatedFTCEnergyBridgeTarget`

What TS193 proves

TS193 proves that the TS191 primitive differentiates to the expanded
critical-line energy density:

```lean
TS193.Goldbach.criticalLineEnergyPrimitive_hasDerivAt
```

It proves the finite-interval FTC identity:

```lean
TS193.Goldbach.criticalLineTruncatedExpandedEnergy_eq_primitive_sub
```

and the truncated improper-energy convergence theorem:

```lean
TS193.Goldbach.criticalLineTruncatedExpandedEnergy_tendsto_X_div_three
```

Thus the directed interval integrals from a finite lower endpoint `a` to
`log X` converge to `X / 3` as `a -> -infty`.

Contract still registered

TS193 defines `CriticalLineImproperIntegralObjectContract` for the future step
that turns this convergence theorem into a named improper Lebesgue integral
object.  The sprint deliberately avoids pretending that this object has already
been constructed.

Non-claims

TS193 does not claim:

- A standalone full improper Lebesgue integral object.
- The Wall 0 measure transport `dx / x = du`.
- The Mellin-as-Fourier integral equivalence.
- Plancherel.
- The Riemann-von Mangoldt contour explicit formula.
- Zeta-zero summability.
- Goldbach.

Verification commands

```powershell
lake build TS.Goldbach.Strong.TS193.CriticalLineTruncatedFTCEnergyBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS193
git diff --check
git status --short
```

Expected result: build succeeds, the audit grep returns no matches, and the
diff is whitespace-clean.
