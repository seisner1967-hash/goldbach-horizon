# TS268 Audit - Natural-Scale Complex-Power Bound

## Scope

TS268 extracts the natural-scale complex power from every concrete TS266
weighted term and proves its modulus at most `max 1 X`, sharpening to `X` for
natural scales at least one.  The remaining multiplicity-denominator factor is
isolated and bounded by an exact finite supremum.

## Proof route

1. Read `0 < rho.re < 1` from the concrete TS264 zero predicate.
2. Split the natural scale into `X = 0` and `0 < X`.
3. Apply `Complex.norm_natCast_cpow_of_re_ne_zero` at zero.
4. Apply `Complex.norm_natCast_cpow_of_pos` and monotonicity of real `rpow` at
   positive scales.
5. Factor the weighted TS266 term into scale and residual complex factors.
6. Take the exact finite `NNReal` supremum of the residual-factor magnitude.
7. Build a scale-visible TS266 uniform bound and compare it with the least
   TS267 exact bound.
8. Combine with exact or future counting bounds through TS266.

## Proved

- `abs ((X : Complex) ^ rho) <= max 1 X` for every concrete selected zero
- `abs ((X : Complex) ^ rho) <= X` when `1 <= X`
- exact weighted-term factorization into scale and multiplicity-denominator
- exact absolute-value factorization
- a finite exact residual-factor supremum and its termwise domination
- a scale-visible function filling the TS266 uniform-term input
- comparison of the least TS267 bound with the scale-visible bound
- exact-count and arbitrary-count contribution bounds with explicit scale

## Non-claims

- no Riemann Hypothesis or critical-line equality is used
- no numerical lower bound for the first zero height is used
- the residual-factor supremum remains noncomputable
- no effective multiplicity or denominator estimate is proved
- no effective zero-counting bound or zero-density theorem is proved
- no global zero summability, contour shift, or residue calculation is proved
- no explicit-formula identity, Gallagher estimate, or OTSA bridge is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS268.NaturalScaleComplexPowerBound
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS268
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS268
git diff --check
```
