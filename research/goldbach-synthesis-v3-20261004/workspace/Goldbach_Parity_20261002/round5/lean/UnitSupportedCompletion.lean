import CompositeCompletion
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic

/-!
Exact composite Fourier completion on physical profiles supported on units.
The Gauss sums of chi and its inverse remain distinct. No primitivity,
conductor bound, or estimate of the complex physical moment is assumed.
-/

namespace GoldbachResearch.UnitSupportedCompletion

open scoped BigOperators Classical
open GoldbachResearch.CompositeCompletion

variable {q : ℕ} [NeZero q]

noncomputable def tau (χ : DirichletCharacter ℂ q) : ℂ :=
  gaussSum χ ZMod.stdAddChar

noncomputable def kappa (χ : DirichletCharacter ℂ q) : ℂ :=
  χ⁻¹ (-1) * tau χ⁻¹ * tau χ

theorem physicalMoment_eq_sum (χ : DirichletCharacter ℂ q) (F : ZMod q → ℂ) :
    physicalMoment χ F = ∑ z : ZMod q, F z * χ⁻¹ z := by
  rw [physicalMoment, sum_units_eq_filter (fun z : ZMod q => F z * χ⁻¹ z)]
  apply Finset.sum_subset (by intro a ha; exact Finset.mem_univ a)
  intro z hz hnot
  have hnonunit : ¬ IsUnit z := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  rw [MulChar.map_nonunit χ⁻¹ hnonunit, mul_zero]

theorem unit_phase_inner (χ : DirichletCharacter ℂ q) {z : ZMod q}
    (hz : IsUnit z) :
    (∑ h : (ZMod q)ˣ, χ (h : ZMod q) * ZMod.stdAddChar (-(h : ZMod q) * z)) =
      χ⁻¹ (-z) * tau χ := by
  calc
    _ = characterPhase χ⁻¹ ((-hz.unit : (ZMod q)ˣ) : ZMod q) := by
      rw [characterPhase]
      simp only [inv_inv]
      apply Finset.sum_congr rfl
      intro h hh
      have hphase : -(h : ZMod q) * z =
          ((-hz.unit : (ZMod q)ˣ) : ZMod q) * (h : ZMod q) := by
        rw [Units.val_neg, hz.unit_spec]
        ring
      rw [hphase]
    _ = χ⁻¹ (-z) * tau χ := by
      rw [characterPhase_unit]
      simp only [inv_inv, Units.val_neg, hz.unit_spec, tau]
      ring

theorem unit_supported_frequencyMoment (χ : DirichletCharacter ℂ q)
    (F : ZMod q → ℂ) (hF : ∀ z, ¬ IsUnit z → F z = 0) :
    unitFrequencyMoment χ F = χ⁻¹ (-1) * tau χ * physicalMoment χ F := by
  simp only [unitFrequencyMoment, fourierWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z : ZMod q, F z *
        (∑ h : (ZMod q)ˣ, χ (h : ZMod q) * ZMod.stdAddChar (-(h : ZMod q) * z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = ∑ z : ZMod q, (χ⁻¹ (-1) * tau χ) * (F z * χ⁻¹ z) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hzu : IsUnit z
      · rw [unit_phase_inner χ hzu, neg_eq_neg_one_mul, map_mul]
        ring
      · rw [hF z hzu]
        simp
    _ = χ⁻¹ (-1) * tau χ * physicalMoment χ F := by
      rw [← Finset.mul_sum, ← physicalMoment_eq_sum]

theorem gauss_conjugation (χ : DirichletCharacter ℂ q) :
    star (tau χ) = χ⁻¹ (-1) * tau χ⁻¹ := by
  rw [tau, gaussSum]
  simp only [star_sum, star_mul, MulChar.star_apply']
  simp_rw [show ∀ x : ZMod q, star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) by
    intro x
    exact (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm]
  have hsub := Equiv.sum_comp (Equiv.neg (ZMod q))
    (fun x : ZMod q => ZMod.stdAddChar (-x) * χ⁻¹ x)
  rw [← hsub]
  simp only [Equiv.neg_apply, neg_neg]
  have hneg (x : ZMod q) : χ⁻¹ (-x) = χ⁻¹ (-1) * χ⁻¹ x := by
    rw [neg_eq_neg_one_mul, map_mul]
  rw [tau, gaussSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hneg x]
  ring

omit [NeZero q] in
theorem character_neg_one_cancellation (χ : DirichletCharacter ℂ q) :
    χ (-1) * χ⁻¹ (-1) = 1 := by
  rw [MulChar.inv_apply_eq_inv']
  exact mul_inv_cancel₀ ((isUnit_one.neg : IsUnit (-1 : ZMod q)).map χ).ne_zero

omit [NeZero q] in
theorem character_neg_one_square (χ : DirichletCharacter ℂ q) :
    χ (-1) ^ 2 = 1 := by
  rw [← map_pow]
  norm_num

theorem inverse_gauss_conjugation (χ : DirichletCharacter ℂ q) :
    tau χ⁻¹ = χ (-1) * star (tau χ) := by
  rw [gauss_conjugation, ← mul_assoc, character_neg_one_cancellation, one_mul]

theorem kappa_eq_normSq (χ : DirichletCharacter ℂ q) :
    kappa χ = (Complex.normSq (tau χ) : ℂ) := by
  rw [kappa, ← gauss_conjugation]
  exact Complex.normSq_eq_conj_mul_self.symm

theorem unit_supported_gauss_product (χ : DirichletCharacter ℂ q)
    (F : ZMod q → ℂ) (hF : ∀ z, ¬ IsUnit z → F z = 0) :
    tau χ⁻¹ * unitFrequencyMoment χ F = kappa χ * physicalMoment χ F := by
  rw [unit_supported_frequencyMoment χ F hF, kappa]
  ring

theorem unit_supported_nonunitDefect (χ : DirichletCharacter ℂ q)
    (F : ZMod q → ℂ) (hF : ∀ z, ¬ IsUnit z → F z = 0) :
    nonunitDefect χ F = ((q : ℂ) - kappa χ) * physicalMoment χ F := by
  have h := composite_completion χ F
  change tau χ⁻¹ * unitFrequencyMoment χ F =
    (q : ℂ) * physicalMoment χ F - nonunitDefect χ F at h
  rw [unit_supported_gauss_product χ F hF] at h
  linear_combination h

theorem double_unit_supported_completion (χ : DirichletCharacter ℂ q)
    (F G : ZMod q → ℂ)
    (hF : ∀ z, ¬ IsUnit z → F z = 0) (hG : ∀ z, ¬ IsUnit z → G z = 0) :
    (tau χ⁻¹ ^ 2 / (q : ℂ) ^ 2) * unitFrequencyMoment χ F * unitFrequencyMoment χ G =
      (kappa χ / (q : ℂ)) ^ 2 * physicalMoment χ F * physicalMoment χ G := by
  calc
    _ = ((tau χ⁻¹ * unitFrequencyMoment χ F) *
        (tau χ⁻¹ * unitFrequencyMoment χ G)) / (q : ℂ) ^ 2 := by ring
    _ = ((kappa χ * physicalMoment χ F) *
        (kappa χ * physicalMoment χ G)) / (q : ℂ) ^ 2 := by
      rw [unit_supported_gauss_product χ F hF, unit_supported_gauss_product χ G hG]
    _ = _ := by
      rw [div_pow]
      ring

#print axioms physicalMoment_eq_sum
#print axioms unit_phase_inner
#print axioms unit_supported_frequencyMoment
#print axioms gauss_conjugation
#print axioms character_neg_one_cancellation
#print axioms character_neg_one_square
#print axioms inverse_gauss_conjugation
#print axioms kappa_eq_normSq
#print axioms unit_supported_gauss_product
#print axioms unit_supported_nonunitDefect
#print axioms double_unit_supported_completion

end GoldbachResearch.UnitSupportedCompletion
