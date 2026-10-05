import AlgebraicGoldbach.LowerBound.BooleanCoefficients

set_option autoImplicit false

namespace AlgebraicGoldbach.BooleanCoefficients

/-- The actual support-collision coefficient map annihilates every ordinary
multiple of a Boolean variable equation, with no finiteness premise. -/
theorem coefficients_boolean_mul
    {σ : Type*} [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ ℚ) :
    coefficients
      (((MvPolynomial.X i : MvPolynomial σ ℚ) ^ 2 -
        MvPolynomial.X i) * p) = 0 := by
  have hidem (f : Finset σ → ℚ) : bitMul i (bitMul i f) = bitMul i f := by
    funext s
    by_cases hi : i ∈ s <;> simp [bitMul, hi]
  rw [pow_two, sub_mul, mul_assoc, map_sub]
  simp only [coefficients_X_mul, hidem, sub_self]

end AlgebraicGoldbach.BooleanCoefficients
