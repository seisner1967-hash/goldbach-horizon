# TS265 Audit - Concrete Finite-Height Zero Truncation

## Scope

TS265 proves that the concrete nontrivial Riemann-zeta zeros below every real
height form a finite set, constructs the exact `Finset`, and instantiates the
TS256 truncation contract with height `X`.

## Proof route

1. Prove zeta is not locally zero at any point away from one by analytic
   uniqueness and `riemannZeta_zero`.
2. Use `riemannZeta_residue_one` to obtain a punctured neighborhood of one
   without zeta zeros.
3. Apply `isClosed_and_discrete_iff` to the global zeta-zero set.
4. Use the cofinite/cocompact characterization to prove finite intersection
   with every compact set.
5. Bound a selected zero by `abs re + abs im <= 1 + T` and place it in a
   compact closed ball.
6. Convert the finite set with `Set.Finite.toFinset` and fill all TS256 fields.

## Proved

- the global zeta-zero set is closed and discrete
- its intersection with every compact set is finite
- all concrete nontrivial zeros with `abs im <= T` form a finite set
- `zerosUpToHeight T` has the exact expected membership characterization
- `concreteFiniteHeightTruncationData` is a complete TS256 truncation
- the concrete truncated spectral sum is real
- its real projection is lossless
- its real absolute value equals the complex spectral modulus

## Non-claims

- the `Finset` is noncomputable; no numerical enumeration algorithm is given
- no formula or upper bound for the number of zeros is proved
- no zero-density theorem or global spectral summability is proved
- no bound for the truncated zero contribution is proved
- no explicit-formula identity or residual bound is proved
- no Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS265.ConcreteFiniteHeightZeroTruncation
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS265
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS265
git diff --check
```
