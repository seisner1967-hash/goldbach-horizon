# TS276 Audit - Linear Factor Angular Average

## Scope

TS276 discharges the `LinearFactorAngularAverageStatement` port left open by
TS275.  For every root strictly inside a positive averaging circle, it proves
both interval integrability of the logarithmic linear factor and the exact
normalized angular average

```text
average_theta log |c + R exp(i theta) - rho| = log R.
```

The proof uses the complex logarithm on the slit plane and Cauchy's formula at
the center of the unit disk.  It does not use a Fourier expansion or exchange
an infinite sum with an integral.

## Proof route

1. Normalize the root displacement by `a = (rho - c) / R` and prove
   `abs a < 1`.
2. Define `L_a(z) = Complex.log (1 - star(a) * z)`.
3. Prove the logarithm argument remains in `Complex.slitPlane` throughout the
   closed unit disk.
4. Deduce continuity on the closed disk and complex differentiability in the
   open disk.
5. Apply the locked Mathlib Cauchy formula at the center and reduce the circle
   integral to `I` times the ordinary angular integral of `L_a`.
6. Take real parts using `Complex.log_re` to prove the normalized boundary-log
   integral is zero.
7. Prove the unit-circle identity
   `|u-a| = |1-star(a)*u|`.
8. Extract the positive scale `R` from the original linear factor and obtain
   the pointwise identity `log |z-rho| = log R + unitBoundaryLog`.
9. Integrate this identity to prove the exact average and construct the TS275
   statement for every `JensenFactorZeroData`.

## Proved

- slit-plane safety for the normalized logarithm
- closed-disk continuity and open-disk differentiability
- vanishing complex angular integral by Cauchy's formula
- vanishing real normalized boundary-log integral
- exact unit-circle conjugation geometry
- integrability of every selected logarithmic linear factor
- exact angular average equal to `log R`
- a concrete constructor for `TS275.Goldbach.LinearFactorAngularAverageStatement`

## Non-claims

- no Fourier series or infinite-sum interchange is used
- no logarithmic mean-value theorem for a general nonvanishing quotient is proved
- no buffered factorization is constructed for a concrete analytic function
- no complete Jensen divisor theorem is claimed
- no concrete Riemann xi function is defined
- no zeta zero-counting estimate or effective constant is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- no OTSA conclusion bridge is supplied
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS276.LinearFactorAngularAverage
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS276
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS276
git diff --check
```
