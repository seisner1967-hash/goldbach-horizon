# TS262 Audit

## Scope

TS262 proves that double conjugation preserves complex analyticity and reduces
the TS261 input contract to Schwarz reflection for `riemannZeta` alone.

## Proved

- `doubleConjugation_realDerivative_eq` identifies the real derivative map.
- `conjugatedFunction_hasDerivAt` proves the exact conjugated derivative formula.
- `conjugatedFunction_differentiableAt` transports complex differentiability.
- `deriv_conjugatedFunction` records the derivative value.
- `conjugatedFunction_analyticAt` proves local complex analyticity.
- `conjugatedFunction_analyticAt_iff` proves the two-way analytic equivalence.
- `conjugatedFunctionAnalyticityStatement` discharges the first TS261 input.
- The routing theorems reduce all downstream reality results to Schwarz
  reflection and a supplied TS260 realization.

## Not proved

- Schwarz reflection for `riemannZeta` is not proved.
- No concrete multiplicity realization or zero-family contract is constructed.
- No explicit-formula identity or analytic bound is proved.
- No Gallagher estimate or Goldbach statement is proved.

## Commands

```powershell
lake build TS.Goldbach.Strong.TS262.DoubleConjugationAnalyticity
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS262
git diff --check
```

The scan is expected to return no matches.
