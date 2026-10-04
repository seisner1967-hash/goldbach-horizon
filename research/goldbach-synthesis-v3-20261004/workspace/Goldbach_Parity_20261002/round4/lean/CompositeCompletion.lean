import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
Exact cyclic Fourier completion with all nonunit frequencies retained.
The modulus is any nonzero natural number. No source-field or primitive-character
assumption is used in the composite completion identities.
-/

namespace GoldbachResearch.CompositeCompletion

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q]

noncomputable def fourierWeight (F : ZMod q → ℂ) (h : ZMod q) : ℂ :=
  ∑ z : ZMod q, F z * ZMod.stdAddChar (-h * z)

noncomputable def characterPhase (χ : DirichletCharacter ℂ q) (h : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ, χ⁻¹ (x : ZMod q) * ZMod.stdAddChar (h * (x : ZMod q))

noncomputable def physicalMoment (χ : DirichletCharacter ℂ q)
    (F : ZMod q → ℂ) : ℂ :=
  ∑ x : (ZMod q)ˣ, F (x : ZMod q) * χ⁻¹ (x : ZMod q)

noncomputable def unitFrequencyMoment (χ : DirichletCharacter ℂ q)
    (F : ZMod q → ℂ) : ℂ :=
  ∑ h : (ZMod q)ˣ, fourierWeight F (h : ZMod q) * χ (h : ZMod q)

noncomputable def nonunitDefect (χ : DirichletCharacter ℂ q)
    (F : ZMod q → ℂ) : ℂ :=
  ∑ h ∈ (Finset.univ : Finset (ZMod q)).filter (fun h => ¬ IsUnit h),
    fourierWeight F h * characterPhase χ h

theorem fourierWeight_eq_dft (F : ZMod q → ℂ) (h : ZMod q) :
    fourierWeight F h = ZMod.dft F h := by
  rw [fourierWeight, ZMod.dft_apply]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [show -h * z = -(z * h) by ring]
  ring

theorem inverse_fourier_sum (F : ZMod q → ℂ) (x : ZMod q) :
    (∑ h : ZMod q, fourierWeight F h * ZMod.stdAddChar (h * x)) =
      (q : ℂ) * F x := by
  have hinv := congrFun (ZMod.dft_dft F) (-x)
  change (∑ h : ZMod q, ZMod.stdAddChar (-(h * (-x))) * ZMod.dft F h) =
    (q : ℂ) * F (-(-x)) at hinv
  simp only [mul_neg, neg_neg] at hinv
  simp_rw [fourierWeight_eq_dft]
  simpa only [mul_comm] using hinv

theorem all_frequency_completion (χ : DirichletCharacter ℂ q) (F : ZMod q → ℂ) :
    (∑ h : ZMod q, fourierWeight F h * characterPhase χ h) =
      (q : ℂ) * physicalMoment χ F := by
  simp only [characterPhase, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : (ZMod q)ˣ, χ⁻¹ (x : ZMod q) *
        (∑ h : ZMod q, fourierWeight F h * ZMod.stdAddChar (h * (x : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = (q : ℂ) * physicalMoment χ F := by
      simp_rw [inverse_fourier_sum]
      rw [physicalMoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem sum_units_eq_filter (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, f (u : ZMod q)) =
      ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, f x := by
  let e : (ZMod q)ˣ ↪ ZMod q := ⟨Units.val, Units.ext⟩
  have hmap : (Finset.univ : Finset (ZMod q)).filter IsUnit = Finset.univ.map e := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_true_left, e, IsUnit]
  rw [hmap, Finset.sum_map]
  rfl

theorem characterPhase_eq_gaussShift (χ : DirichletCharacter ℂ q) (h : ZMod q) :
    characterPhase χ h = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift h) := by
  classical
  rw [characterPhase, sum_units_eq_filter
    (fun x : ZMod q => χ⁻¹ x * ZMod.stdAddChar (h * x)), gaussSum]
  simp only [AddChar.mulShift_apply]
  apply Finset.sum_subset (by intro a ha; exact Finset.mem_univ a)
  intro a ha hnot
  have hnonunit : ¬ IsUnit a := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  simp only [MulChar.map_nonunit χ⁻¹ hnonunit, zero_mul]

theorem characterPhase_unit (χ : DirichletCharacter ℂ q) (h : (ZMod q)ˣ) :
    characterPhase χ (h : ZMod q) =
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (h : ZMod q) := by
  rw [characterPhase_eq_gaussShift]
  have hshift := gaussSum_mulShift χ⁻¹ ZMod.stdAddChar h
  have hcancel : χ (h : ZMod q) * χ⁻¹ (h : ZMod q) = 1 := by
    rw [MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ (h.isUnit.map χ).ne_zero
  calc
    _ = χ (h : ZMod q) * (χ⁻¹ (h : ZMod q) *
        gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (h : ZMod q))) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = gaussSum χ⁻¹ ZMod.stdAddChar * χ (h : ZMod q) := by
      rw [hshift, mul_comm]

theorem nonunit_partition (χ : DirichletCharacter ℂ q) (F : ZMod q → ℂ) :
    (∑ h : ZMod q, fourierWeight F h * characterPhase χ h) =
      gaussSum χ⁻¹ ZMod.stdAddChar * unitFrequencyMoment χ F + nonunitDefect χ F := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod q)) IsUnit]
  rw [← sum_units_eq_filter]
  simp_rw [characterPhase_unit]
  rw [nonunitDefect, unitFrequencyMoment, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  ring

theorem composite_completion (χ : DirichletCharacter ℂ q) (F : ZMod q → ℂ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * unitFrequencyMoment χ F =
      (q : ℂ) * physicalMoment χ F - nonunitDefect χ F := by
  have hall := all_frequency_completion χ F
  rw [nonunit_partition] at hall
  linear_combination hall

theorem composite_completion_ratio (χ : DirichletCharacter ℂ q) (F : ZMod q → ℂ) :
    (gaussSum χ⁻¹ ZMod.stdAddChar / (q : ℂ)) * unitFrequencyMoment χ F =
      physicalMoment χ F - nonunitDefect χ F / (q : ℂ) := by
  have hq : (q : ℂ) ≠ 0 := NeZero.ne (q : ℂ)
  calc
    _ = (gaussSum χ⁻¹ ZMod.stdAddChar * unitFrequencyMoment χ F) / (q : ℂ) := by
      ring
    _ = ((q : ℂ) * physicalMoment χ F - nonunitDefect χ F) / (q : ℂ) := by
      rw [composite_completion]
    _ = _ := by
      field_simp [hq]
      ring

theorem double_composite_completion (χ : DirichletCharacter ℂ q)
    (F G : ZMod q → ℂ) :
    (gaussSum χ⁻¹ ZMod.stdAddChar ^ 2 / (q : ℂ) ^ 2) *
      unitFrequencyMoment χ F * unitFrequencyMoment χ G =
      (physicalMoment χ F - nonunitDefect χ F / (q : ℂ)) *
        (physicalMoment χ G - nonunitDefect χ G / (q : ℂ)) := by
  calc
    _ = ((gaussSum χ⁻¹ ZMod.stdAddChar / (q : ℂ)) * unitFrequencyMoment χ F) *
        ((gaussSum χ⁻¹ ZMod.stdAddChar / (q : ℂ)) * unitFrequencyMoment χ G) := by
      rw [← div_pow]
      ring
    _ = _ := by rw [composite_completion_ratio, composite_completion_ratio]

theorem zero_gauss_retains_defect (χ : DirichletCharacter ℂ q) (F : ZMod q → ℂ)
    (hzero : gaussSum χ⁻¹ ZMod.stdAddChar = 0) :
    (q : ℂ) * physicalMoment χ F = nonunitDefect χ F := by
  have h := composite_completion χ F
  rw [hzero, zero_mul] at h
  linear_combination -h

theorem zero_frequency_is_nonunit [Nontrivial (ZMod q)] :
    (0 : ZMod q) ∈ (Finset.univ : Finset (ZMod q)).filter (fun h => ¬ IsUnit h) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_isUnit_zero

#print axioms fourierWeight_eq_dft
#print axioms inverse_fourier_sum
#print axioms all_frequency_completion
#print axioms sum_units_eq_filter
#print axioms characterPhase_eq_gaussShift
#print axioms characterPhase_unit
#print axioms nonunit_partition
#print axioms composite_completion
#print axioms composite_completion_ratio
#print axioms double_composite_completion
#print axioms zero_gauss_retains_defect
#print axioms zero_frequency_is_nonunit

end GoldbachResearch.CompositeCompletion
