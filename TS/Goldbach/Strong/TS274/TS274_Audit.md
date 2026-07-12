# TS274 Audit - Minimal Jensen Inequality Backport

## Scope

TS274 backports the finite counting core of Jensen's inequality for an exact
finite family of zeros in two concentric disks.  It proves that every selected
zero contributes at least `log (R / r)`, sums this estimate with natural
multiplicities, and divides by the positive common weight.  Thus any upper
bound on the weighted Jensen mass yields the standard finite multiplicity
counting quotient.

The locked Mathlib revision does not contain the modern circle-average,
harmonic mean-value, and divisor infrastructure.  TS274 therefore names the
remaining weighted boundary estimate at its exact conclusion.  It does not
replace that analytic step by `True` and does not claim the complete modern
`sum_divisor_le` theorem.

## Proof route

1. Package a finite zero family in an inner disk with positive radii `r < R`.
2. Prove every selected zero has positive distance from the center.
3. Prove `1 < R / r` and hence `0 < log (R / r)`.
4. Use denominator monotonicity and monotonicity of `Real.log` to prove
   `log (R / r) <= log (R / |z-c|)` for every selected zero.
5. Multiply by the nonnegative natural multiplicity and sum over the `Finset`.
6. Prove `count * log (R / r) <= weightedMass`.
7. Divide by the positive logarithmic gap to obtain the Jensen count quotient.
8. Specialize the budget to `log (M / |f(c)|)` and prove its elementary
   nonnegativity under the expected center-norm domination.

## Proved

- positivity of the outer radius and logarithmic radius gap
- positivity of every selected zero's distance from the center
- the pointwise lower bound for finite Jensen weights
- the multiplicity-weighted finite sum inequality
- exact transport between natural count and real multiplicity mass
- the finite Jensen multiplicity-counting quotient from a weighted upper bound
- the boundary-logarithm specialization of that quotient

## Non-claims

- no circle-average identity is backported
- no harmonic mean-value theorem is backported
- no analytic zero `Finset` is constructed from a general analytic function
- no concrete Riemann xi function is defined
- no zeta zero-counting estimate or effective constant is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS274.MinimalJensenInequalityBackport
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS274
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS274
git diff --check
```
