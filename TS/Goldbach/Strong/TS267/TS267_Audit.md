# TS267 Audit - Exact Finite Uniform Spectral-Term Bound

## Scope

TS267 fills the TS266 uniform-term input with the exact finite supremum of the
selected multiplicity-weighted term magnitudes.  It also names the exact real
cardinality and obtains an unconditional cardinality-times-supremum bound.

## Proof route

1. Package each complex term magnitude as an `NNReal`.
2. Take the `Finset.sup` over the exact TS265 selection.
3. Use `Finset.le_sup` to dominate every selected term.
4. Use `Finset.sup_le` to prove minimality among all TS266 uniform bounds.
5. Cast the exact finite cardinality to `Real`.
6. Apply the TS266 product reduction to the two exact functions.

## Proved

- the exact finite supremum is nonnegative
- it dominates every selected multiplicity-weighted spectral term
- it fills `ConcreteFiniteHeightZeroUniformTermBoundStatement`
- it is no larger than every other nonnegative TS266 uniform bound
- exact cardinality fills `ConcreteFiniteHeightZeroCountingBoundStatement`
- the real zero contribution is bounded by exact cardinality times exact
  finite supremum
- any future counting bound combines directly with the exact uniform bound

## Non-claims

- the exact supremum and exact cardinality remain noncomputable
- no closed-form estimate in `X` is proved
- no effective multiplicity bound is proved
- no effective lower bound for `abs (rho * (rho + 1))` is proved
- no zero-counting asymptotic or zero-density theorem is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS267.ExactFiniteUniformSpectralTermBound
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS267
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS267
git diff --check
```
