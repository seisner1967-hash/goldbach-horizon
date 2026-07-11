# TS261 Audit

## Scope

TS261 proves the generic transport of `AnalyticAt.order` through the double
conjugation `z |-> star (f (star z))`.  It reduces the TS260 zeta target to two
named analytic inputs.

## Proved

- `eventually_precomp_star` transports neighborhood properties by conjugation.
- `conjugatedFunction_eventuallyEq_zero` transports the locally-zero branch.
- `conjugatedFunction_factorization_eventually` transports every finite local
  factorization with the same natural exponent.
- `conjugatedFunction_order_eq` proves equality of canonical analytic orders,
  including both `Top` and finite `ENat` branches.
- `conjugatedRiemannZeta_eq` converts Schwarz reflection into function equality.
- `riemannZetaVanishingOrderConjugation_of_inputs` discharges the exact TS260
  target from the two named inputs.
- The downstream theorems route realizations through TS260, TS259, and TS258.

## Not proved

- Analyticity of the double-conjugated function is not supplied.
- Schwarz reflection for `riemannZeta` is not supplied.
- No concrete multiplicity realization is constructed.
- No explicit-formula identity or analytic bound is proved.
- No Gallagher estimate or Goldbach statement is proved.

## Commands

```powershell
lake build TS.Goldbach.Strong.TS261.RiemannZetaVanishingOrderConjugationReduction
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS261
git diff --check
```

The scan is expected to return no matches.
