# Frozen BOOLEAN_MULTIPLIER_RIGIDITY signatures

```lean
theorem countMul_eq_diagonal_add_up
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (f : Finset σ → ℚ) (s : Finset σ) :
    countMul m f s = ((s.card : ℚ) - m) * f s + BooleanLattice.up f s

theorem top_layer_vanishes_of_countMul_degree_le
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (k : ℕ) (hk : 2 * k < Fintype.card σ)
    (f : Finset σ → ℚ)
    (habove : ∀ s : Finset σ, k < s.card → f s = 0)
    (himage : ∀ s : Finset σ, k < s.card → countMul m f s = 0) :
    ∀ s : Finset σ, k ≤ s.card → f s = 0
```
