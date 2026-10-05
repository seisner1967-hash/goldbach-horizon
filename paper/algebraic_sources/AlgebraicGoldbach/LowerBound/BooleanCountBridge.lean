import AlgebraicGoldbach.LowerBound.BooleanMultiplierRigidity

set_option autoImplicit false

namespace AlgebraicGoldbach.BooleanCoefficients

open scoped BigOperators

/-- The actual support-collision coefficient map carries multiplication by the
ordinary rational count polynomial to the unchanged count action. -/
theorem coefficients_count_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (p : MvPolynomial σ ℚ) :
    coefficients
      (((∑ i : σ, (MvPolynomial.X i : MvPolynomial σ ℚ)) -
        MvPolynomial.C m) * p) =
      countMul m (coefficients p) := by
  funext s
  rw [sub_mul, Finset.sum_mul, map_sub, map_sum]
  rw [MvPolynomial.C_mul', map_smul]
  simp only [coefficients_X_mul, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, countMul]

end AlgebraicGoldbach.BooleanCoefficients
