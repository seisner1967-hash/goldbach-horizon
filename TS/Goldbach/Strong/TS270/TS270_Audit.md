# TS270 Audit - High-Zone Multiplicity Counting Interface

## Scope

TS270 replaces plain cardinality by the exact multiplicity count that actually
appears in the TS269 high-zone envelope.  It proves an unconditional bound of
the weighted high residual mass by this exact count, packages a generic future
upper bound for the count, and transports any such bound to the real TS255 zero
contribution.

## Proof route

1. Define the exact multiplicity count below an arbitrary real height.
2. Define the exact high-zone multiplicity count at natural scale.
3. Prove that the high count is bounded by the full count up to height `X`.
4. Remove the common `max 1 X` factor from the high quadratic envelope.
5. Use `1 <= abs rho.im` to prove `1 <= abs rho.im ^ 2`.
6. Bound each high residual envelope by its analytic multiplicity.
7. Sum termwise and rewrite the real cast of the natural-valued sum.
8. Package future upper bounds for the high or global multiplicity counts.
9. Transport either bound through TS269 to the real zero contribution.

## Proved

- exact multiplicity-counting functions without a zero-simplicity assumption
- high-zone multiplicity count bounded by the full count up to height `X`
- exact scale factorization of the high quadratic envelope mass
- nonnegativity of the high weighted residual mass
- high weighted residual mass bounded by exact high multiplicity count
- an exact-count instance of the generic counting contract
- transport of every generic multiplicity-counting bound to the real zero sum
- transport of every global height-counting bound to the real zero sum
- natural-scale sharpening from `max 1 X` to `X` when `1 <= X`

## Non-claims

- no zero is asserted simple
- no numerical first-zero height or low-zone exclusion is proved
- no effective formula for the multiplicity count is proved
- no `N(T)` asymptotic or zero-density theorem is proved
- no global weighted summability is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS270.HighZoneMultiplicityCountingInterface
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS270
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS270
git diff --check
```
