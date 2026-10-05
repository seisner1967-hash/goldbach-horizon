# Frozen BOOLEAN_COEFFICIENT_DEGREE signatures

```lean
theorem support_card_le_exponent_sum
    {σ : Type*} [DecidableEq σ] (e : σ →₀ ℕ) :
    e.support.card ≤ e.sum (fun _ exponent => exponent)

theorem coefficients_eq_zero_of_totalDegree_lt_card
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (s : Finset σ)
    (h : p.totalDegree < s.card) :
    coefficients p s = 0
```
