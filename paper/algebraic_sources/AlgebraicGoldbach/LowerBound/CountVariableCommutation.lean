import AlgebraicGoldbach.LowerBound.BooleanMultiplierRigidity

set_option autoImplicit false

namespace AlgebraicGoldbach.BooleanCoefficients

open scoped BigOperators

/-- The unchanged actual variable action commutes with the actual finite count
action on arbitrary rational subset functions. -/
theorem bitMul_countMul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) (m : ℚ) (f : Finset σ → ℚ) :
    bitMul i (countMul m f) = countMul m (bitMul i f) := by
  have hcomm (j : σ) (g : Finset σ → ℚ) :
      bitMul i (bitMul j g) = bitMul j (bitMul i g) := by
    funext s
    by_cases hij : i = j
    · subst j
      rfl
    · by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
        simp [bitMul, hi, hj, Finset.mem_erase, hij, Ne.symm hij,
          Finset.erase_right_comm, add_assoc, add_left_comm, add_comm]
  funext s
  have hsum : (∑ j : σ, bitMul j (bitMul i f) s) =
      ∑ j : σ, bitMul i (bitMul j f) s := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact congrFun (hcomm j f).symm s
  simp only [countMul]
  rw [hsum]
  by_cases hi : i ∈ s
  · simp only [bitMul, hi, if_true, countMul, Finset.sum_add_distrib]
    ring
  · simp [bitMul, hi]

end AlgebraicGoldbach.BooleanCoefficients
