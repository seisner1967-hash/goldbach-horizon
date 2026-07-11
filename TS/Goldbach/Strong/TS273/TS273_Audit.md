# TS273 Audit - Log-Linear Multiplicity Counting Reduction

## Scope

TS273 reduces the abstract TS270 global counting contract to the analytically
meaningful estimate `N_mult(T) <= C * T * log(T + 2)` for `T >= 1`.  It extends
this estimate to all real heights using exact count monotonicity and a safe
`max T 1` envelope, then transports the resulting contract through TS272 to the
full finite zero contribution.  A separate disk-counting interface records the
future Jensen route without claiming unavailable library support.

## Proof route

1. Define `C * max T 1 * log(max T 1 + 2)` and prove it nonnegative.
2. Prove exact multiplicity counts monotone from the finite-set inclusion.
3. Package the large-height log-linear counting obligation.
4. Package a Jensen-disk count and its height-to-disk comparison.
5. Derive the large-height estimate from the two disk-counting inequalities.
6. Extend the large-height estimate below one by monotonicity through height one.
7. Build the TS270 global multiplicity-counting contract.
8. Instantiate the TS272 amortized and full real zero-contribution bounds.

## Proved

- nonnegativity of the safe global log-linear envelope
- monotonicity of the exact multiplicity-counting function
- Jensen-disk input implies the large-height log-linear estimate
- large-height estimate implies the TS270 global contract
- both analytic inputs route to the full TS272 finite zero bound

## Non-claims

- the locked Mathlib Jensen inequality is not backported
- no concrete Riemann xi function or entire proof is constructed
- no xi-divisor identification or circle-growth estimate is proved
- no effective log-linear counting constant is proved
- no infinite shell convergence or global weighted summability is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS273.LogLinearMultiplicityCountingReduction
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS273
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS273
git diff --check
```
