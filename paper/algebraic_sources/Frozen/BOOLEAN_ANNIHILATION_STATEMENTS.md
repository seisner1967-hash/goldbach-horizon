# Frozen BOOLEAN_ANNIHILATION signature

```lean
theorem coefficients_boolean_mul
    {σ : Type*} [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ ℚ) :
    coefficients
      (((MvPolynomial.X i : MvPolynomial σ ℚ) ^ 2 -
        MvPolynomial.X i) * p) = 0
```
