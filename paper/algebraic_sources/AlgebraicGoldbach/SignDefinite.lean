import AlgebraicGoldbach.Soundness
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
This obstruction concerns canonical rational coefficients of one sign.
It does not apply to mixed-sign interval products or to finite-field order.
-/

namespace AlgebraicGoldbach.SignDefinite

noncomputable section

open scoped BigOperators
open MvPolynomial

def NonnegativeCoefficients {N : ℕ} (P : R N ℚ) : Prop :=
  ∀ d, 0 ≤ coeff d P

def SignDefiniteCoefficients {N : ℕ} (P : R N ℚ) : Prop :=
  NonnegativeCoefficients P ∨ ∀ d, coeff d P ≤ 0

def SievePoint (N : ℕ) (x : Fin (N + 1) → ℚ) : Prop :=
  ∀ i, ¬ Nat.Prime i.val → x i = 0

theorem coefficient_on_primes_eq_zero {N : ℕ} (P : R N ℚ)
    (hcoeff : NonnegativeCoefficients P)
    (htruth : eval (primePoint N ℚ) P = 0)
    (d : Fin (N + 1) →₀ ℕ)
    (hprime : ∀ i ∈ d.support, Nat.Prime i.val) : coeff d P = 0 := by
  classical
  have hpoint : ∀ i : Fin (N + 1), 0 ≤ primePoint N ℚ i := by
    intro i
    simp only [primePoint]
    split <;> norm_num
  have hnonneg : ∀ e ∈ P.support,
      0 ≤ coeff e P * ∏ i ∈ e.support, primePoint N ℚ i ^ e i := by
    intro e he
    exact mul_nonneg (hcoeff e)
      (Finset.prod_nonneg fun i hi => pow_nonneg (hpoint i) _)
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
    (by simpa only [eval_eq] using htruth)
  by_cases hd : d ∈ P.support
  · have hprod : (∏ i ∈ d.support, primePoint N ℚ i ^ d i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [primePoint, hprime i hi]
    simpa only [hprod, mul_one] using hterms d hd
  · exact not_mem_support_iff.mp hd

theorem nonnegative_equation_vanishes_on_sievePoint {N : ℕ} (P : R N ℚ)
    (hcoeff : NonnegativeCoefficients P)
    (htruth : eval (primePoint N ℚ) P = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x) : eval x P = 0 := by
  classical
  rw [eval_eq]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hprime : ∀ i ∈ d.support, Nat.Prime i.val
  · simp [coefficient_on_primes_eq_zero P hcoeff htruth d hprime]
  · push_neg at hprime
    obtain ⟨i, hi, hnot⟩ := hprime
    have hpow : x i ^ d i = 0 := by
      rw [hx i hnot]
      exact zero_pow (Finsupp.mem_support_iff.mp hi)
    have hprod : (∏ j ∈ d.support, x j ^ d j) = 0 :=
      Finset.prod_eq_zero hi hpow
    simp [hprod]

theorem sign_definite_equation_vanishes_on_sievePoint {N : ℕ} (P : R N ℚ)
    (hcoeff : SignDefiniteCoefficients P)
    (htruth : eval (primePoint N ℚ) P = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x) : eval x P = 0 := by
  rcases hcoeff with hpos | hneg
  · exact nonnegative_equation_vanishes_on_sievePoint P hpos htruth x hx
  · have hn : NonnegativeCoefficients (-P) := by
      intro d
      rw [coeff_neg]
      exact neg_nonneg.mpr (hneg d)
    have ht : eval (primePoint N ℚ) (-P) = 0 := by simp [htruth]
    have hz := nonnegative_equation_vanishes_on_sievePoint (-P) hn ht x hx
    simpa using hz

theorem sign_definite_family_preserves_sieve_common_zero {N : ℕ}
    {ι κ : Type*} (F : ι → R N ℚ) (P : κ → R N ℚ)
    (hcoeff : ∀ j, SignDefiniteCoefficients (P j))
    (htruth : ∀ j, eval (primePoint N ℚ) (P j) = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x)
    (hF : ∀ j, eval x (F j) = 0) :
    ∀ j : ι ⊕ κ, eval x (Sum.elim F P j) = 0 := by
  intro j
  cases j with
  | inl i => exact hF i
  | inr k =>
      exact sign_definite_equation_vanishes_on_sievePoint (P k)
        (hcoeff k) (htruth k) x hx

theorem sign_definite_strengthening_has_no_certificate {N : ℕ}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → R N ℚ) (P : κ → R N ℚ)
    (hcoeff : ∀ j, SignDefiniteCoefficients (P j))
    (htruth : ∀ j, eval (primePoint N ℚ) (P j) = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x)
    (hF : ∀ j, eval x (F j) = 0)
    (hBool : ∀ i, eval x (booleanConstraint i) = 0)
    (hg : eval x (g N ℚ) = 0)
    (A : ι ⊕ κ → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) :
    ¬ Certificate (Sum.elim F P) A U B := by
  intro hcert
  exact certificate_excludes_common_zero (Sum.elim F P) A U B hcert x
    (sign_definite_family_preserves_sieve_common_zero F P hcoeff htruth x hx hF)
    hBool hg

end

end AlgebraicGoldbach.SignDefinite
