# TS260 Audit

## Scope

TS260 connects the abstract TS185 multiplicity to Mathlib's canonical
`AnalyticAt.order` for the Riemann zeta function.  It reduces multiplicity
conjugation to one named equality between analytic orders.

## Proved

- `riemannZeta_differentiableOn_compl_one` proves differentiability away from
  the pole at one.
- `zeroSet_ne_one` derives exclusion of the pole from the TS185 critical strip.
- `riemannZeta_analyticAt_zeroSet` proves analyticity at every selected zero.
- `riemannZetaVanishingOrderAt` and `riemannZetaVanishingOrderAtZero` use
  Mathlib's canonical `AnalyticAt.order : ENat`.
- `riemannZetaVanishingOrderAt_eq_nat_iff` exposes the local analytic
  factorization characterized by `order_eq_nat_iff`.
- `RiemannZetaZeroMultiplicityRealizationContract` identifies the natural
  TS185 multiplicity with the finite analytic order.
- `multiplicityConjugation_of_realization` reduces multiplicity conjugation to
  conjugation invariance of the analytic order.
- `ts259Extension_of_realization` and the truncation theorems route this result
  through TS259 and TS258.

## Not proved

- Conjugation invariance of the analytic zeta order is not proved.
- No concrete multiplicity realization contract is constructed.
- No explicit-formula identity or analytic bound is proved.
- No Gallagher estimate or Goldbach statement is proved.

## Commands

```powershell
lake build TS.Goldbach.Strong.TS260.RiemannZetaVanishingOrderRealization
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS260
git diff --check
```

The scan is expected to return no matches.
