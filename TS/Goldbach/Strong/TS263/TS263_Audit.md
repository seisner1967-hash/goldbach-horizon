# TS263 Audit - Riemann Zeta Schwarz Reflection

## Scope

TS263 proves Schwarz reflection for Mathlib's `riemannZeta` on the whole
complex plane and routes the result through TS262, TS261, TS260, TS259, and
TS258.

## Proof route

1. Conjugate each Dirichlet-series term with `Complex.cpow_conj`.
2. Use `Complex.conj_tsum` on the half-plane `1 < re s`.
3. Apply the analytic identity principle on `Complex \ {1}`.
4. Check Mathlib's assigned value at `s = 1` is real.

## Proved

- `riemannZeta_schwarzReflection_of_one_lt_re`
- `riemannZeta_schwarzReflection_ne_one`
- `riemannZeta_schwarzReflection`
- complete TS261 input assembly
- zeta analytic-order conjugation for every TS185 contract
- downstream multiplicity conjugation and finite-sum reality from any
  concrete order realization

## Non-claims

- no concrete TS185 zero family is constructed
- no concrete multiplicity realization is constructed
- no explicit-formula identity is proved
- no zero-contribution or residual bound is proved
- no Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS263.RiemannZetaSchwarzReflection
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS263
git diff --check
```
