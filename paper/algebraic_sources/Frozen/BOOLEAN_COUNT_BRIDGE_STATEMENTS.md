# Frozen BOOLEAN_COUNT_BRIDGE signature

```lean
theorem coefficients_count_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (p : MvPolynomial σ ℚ) :
    coefficients
      (((∑ i : σ, (MvPolynomial.X i : MvPolynomial σ ℚ)) -
        MvPolynomial.C m) * p) =
      countMul m (coefficients p)
```
