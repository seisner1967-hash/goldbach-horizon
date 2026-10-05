import AlgebraicGoldbach.LowerBound.BooleanCoefficients

set_option autoImplicit false

namespace AlgebraicGoldbach.BooleanCoefficients

/-- The support cardinality of a genuine ordinary natural exponent vector is
bounded by its ordinary exponent sum. Positivity is used only for exponents. -/
theorem support_card_le_exponent_sum
    {σ : Type*} [DecidableEq σ] (e : σ →₀ ℕ) :
    e.support.card ≤ e.sum (fun _ exponent => exponent) := by
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun i hi =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- Actual support-collision coefficients vanish strictly above the ordinary
polynomial degree. No restriction on rational coefficient signs is used. -/
theorem coefficients_eq_zero_of_totalDegree_lt_card
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (s : Finset σ)
    (h : p.totalDegree < s.card) :
    coefficients p s = 0 := by
  change (Finsupp.linearCombination ℚ coefficientAtom p) s = 0
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro e he
  have hcard : e.support.card < s.card :=
    lt_of_le_of_lt ((support_card_le_exponent_sum e).trans
      (MvPolynomial.le_totalDegree he)) h
  have hne : e.support ≠ s := by
    intro heq
    rw [heq] at hcard
    exact Nat.lt_irrefl s.card hcard
  simp [coefficientAtom, hne]

end AlgebraicGoldbach.BooleanCoefficients
