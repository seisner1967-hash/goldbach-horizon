import Mathlib

set_option autoImplicit false

namespace AlgebraicGoldbach.BooleanCoefficients

variable {σ : Type*} [DecidableEq σ]

/-- The coefficient atom of an ordinary exponent vector, indexed by its actual
finite support. Distinct exponent vectors with the same support use this same
atom, so their ordinary rational coefficients are added by `coefficients`. -/
def coefficientAtom (e : σ →₀ ℕ) (s : Finset σ) : ℚ :=
  if e.support = s then 1 else 0

/-- Actual support-collision coefficients of an ordinary rational polynomial.
The polynomial is its genuine finitely supported ordinary exponent-vector map;
the codomain has its ordinary pointwise rational module structure. -/
noncomputable def coefficients : MvPolynomial σ ℚ →ₗ[ℚ] (Finset σ → ℚ) :=
  Finsupp.linearCombination ℚ coefficientAtom

/-- Boolean variable multiplication on finite-support coefficients. The `f s`
term records the exponent vectors already containing the multiplied variable. -/
def bitMul (i : σ) (f : Finset σ → ℚ) (s : Finset σ) : ℚ :=
  if i ∈ s then f s + f (s.erase i) else 0

/-- Multiplication by one variable adds that variable to the actual support of
an ordinary natural exponent vector, including when its exponent was positive. -/
theorem support_single_one_add (i : σ) (e : σ →₀ ℕ) :
    (Finsupp.single i 1 + e).support = insert i e.support := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [Finsupp.mem_support_iff]
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      hji, Ne.symm hji]

/-- Exact variable compatibility for each genuine ordinary exponent atom. -/
theorem coefficientAtom_single_one_add (i : σ) (e : σ →₀ ℕ) :
    coefficientAtom (Finsupp.single i 1 + e) = bitMul i (coefficientAtom e) := by
  funext s
  rw [coefficientAtom, support_single_one_add]
  by_cases his : i ∈ s
  · by_cases hie : i ∈ e.support
    · have hne : e.support ≠ s.erase i := by
        intro heq
        have : i ∈ s.erase i := heq ▸ hie
        exact Finset.not_mem_erase i s this
      simp [bitMul, coefficientAtom, his, Finset.insert_eq_of_mem hie, hne]
    · have hne : e.support ≠ s := by
        intro heq
        exact hie (heq.symm ▸ his)
      have hpreimage : insert i e.support = s ↔ e.support = s.erase i := by
        constructor
        · intro heq
          rw [← heq, Finset.erase_insert hie]
        · intro heq
          rw [heq, Finset.insert_erase his]
      simp [bitMul, coefficientAtom, his, hne, hpreimage]
  · have hne : insert i e.support ≠ s := by
      intro heq
      exact his (heq ▸ Finset.mem_insert_self i e.support)
    simp [bitMul, his, hne]

/-- Support-collision coefficients of an actual ordinary monomial, with any
rational scalar, including zero and negative scalars. -/
theorem coefficients_monomial (e : σ →₀ ℕ) (c : ℚ) :
    coefficients (MvPolynomial.monomial e c) = c • coefficientAtom e := by
  change Finsupp.linearCombination ℚ coefficientAtom (Finsupp.single e c) = _
  exact Finsupp.linearCombination_single ℚ c e

/-- Multiplication by an actual polynomial variable acts by Boolean bit
multiplication on the coefficients aggregated by ordinary exponent support. -/
theorem coefficients_X_mul
    {σ : Type*} [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ ℚ) :
    coefficients (MvPolynomial.X i * p) = bitMul i (coefficients p) := by
  induction p using MvPolynomial.induction_on' with
  | h1 e c =>
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
        coefficients_monomial, coefficients_monomial, coefficientAtom_single_one_add]
      funext s
      by_cases his : i ∈ s <;> simp [bitMul, his, mul_add]
  | h2 p q hp hq =>
      rw [mul_add, map_add, map_add, hp, hq]
      funext s
      by_cases his : i ∈ s <;>
        simp [bitMul, his, add_assoc, add_comm, add_left_comm]

end AlgebraicGoldbach.BooleanCoefficients
