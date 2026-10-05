# Frozen COUNT_VARIABLE_COMMUTATION signature

```lean
theorem bitMul_countMul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) (m : ℚ) (f : Finset σ → ℚ) :
    bitMul i (countMul m f) = countMul m (bitMul i f)
```
