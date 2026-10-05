# Frozen BOOLEAN_COEFFICIENTS signatures

```lean
theorem support_single_one_add {σ : Type*} [DecidableEq σ] (i : σ) (e : σ →₀ ℕ) :
    (Finsupp.single i 1 + e).support = insert i e.support

theorem coefficientAtom_single_one_add {σ : Type*} [DecidableEq σ] (i : σ) (e : σ →₀ ℕ) :
    coefficientAtom (Finsupp.single i 1 + e) = bitMul i (coefficientAtom e)

theorem coefficients_monomial {σ : Type*} [DecidableEq σ] (e : σ →₀ ℕ) (c : ℚ) :
    coefficients (MvPolynomial.monomial e c) = c • coefficientAtom e

theorem coefficients_X_mul
    {σ : Type*} [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ ℚ) :
    coefficients (MvPolynomial.X i * p) = bitMul i (coefficients p)
```
