# TS269 Audit - Imaginary-Square Denominator Bound

## Scope

TS269 proves the universal denominator estimate
`abs rho.im ^ 2 <= Complex.abs (rho * (rho + 1))`, derives quadratic decay of
the TS268 residual factor in the high imaginary zone, and partitions the exact
TS265 selection into low exact and high quadratic components.

## Proof route

1. Bound `abs rho.im` by both `Complex.abs rho` and
   `Complex.abs (rho + 1)`.
2. Multiply the two inequalities and use multiplicativity of complex modulus.
3. In the zone `1 <= abs rho.im`, reverse the positive denominators to bound
   the residual factor by multiplicity divided by `abs rho.im ^ 2`.
4. Filter the TS265 `Finset` into disjoint low and high selections.
5. Prove that full-selection membership is equivalent to low-or-high membership.
6. Split the exact TS266 norm mass across the two selections.
7. Retain the low mass exactly and majorize the high mass termwise.
8. Transport the resulting bound to the real TS255 zero contribution.

## Proved

- the imaginary-square denominator lower bound for every complex number
- quadratic residual decay whenever `1 <= abs rho.im`
- exact low/high membership characterizations
- disjointness and completeness of the low/high finite partition
- exact decomposition of the TS266 norm mass
- a high-zone quadratic envelope bound
- the full real contribution bounded by low exact plus high quadratic masses

## Non-claims

- no false `max 1 (abs rho.im ^ 2)` denominator lower bound is used
- no numerical first-zero height or low-zone exclusion is proved
- no Riemann Hypothesis or zero-simplicity claim is used
- no effective multiplicity count or zero-counting estimate is proved
- no global weighted summability or zero-density theorem is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS269.ImaginarySquareDenominatorBound
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS269
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS269
git diff --check
```
