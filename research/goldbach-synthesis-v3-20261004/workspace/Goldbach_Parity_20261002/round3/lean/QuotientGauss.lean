import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-!
Exact multiplicative transform of the Kloosterman kernel over the unit group.
The source ring can be finite and composite. All three phase parameters are units.
No conductor bound, primitive-character assumption, positivity or mean estimate
is part of these identities.
-/

namespace GoldbachResearch.QuotientGauss

open scoped BigOperators

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable def unitGauss (χ : MulChar R ℂ) (ψ : AddChar R ℂ) : ℂ :=
  ∑ u : Rˣ, χ (u : R) * ψ (u : R)

noncomputable def kloosterman (ψ : AddChar R ℂ) (A B : R) : ℂ :=
  ∑ x : Rˣ, ψ (A * (x : R) + B * ((x⁻¹ : Rˣ) : R))

theorem unitGauss_eq_gaussSum (χ : MulChar R ℂ) (ψ : AddChar R ℂ) :
    unitGauss χ ψ = gaussSum χ ψ := by
  classical
  let e : Rˣ ↪ R := ⟨Units.val, Units.ext⟩
  calc
    unitGauss χ ψ = ∑ a ∈ Finset.univ.map e, χ a * ψ a := by
      simp only [unitGauss, Finset.sum_map, e, Function.Embedding.coeFn_mk]
    _ = ∑ a : R, χ a * ψ a := by
      apply Finset.sum_subset (by intro a ha; exact Finset.mem_univ a)
      intro a ha hnot
      have hnonunit : ¬ IsUnit a := by
        intro hu
        apply hnot
        exact Finset.mem_map.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
      rw [MulChar.map_nonunit χ hnonunit, zero_mul]
    _ = gaussSum χ ψ := rfl

omit [Fintype R] [DecidableEq R] in
theorem inverse_character_unit (χ : MulChar R ℂ) (u : Rˣ) :
    χ⁻¹ (u : R) = χ ((u⁻¹ : Rˣ) : R) := by
  rw [MulChar.inv_apply, Ring.inverse_unit]

theorem unitGauss_shift (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (a : Rˣ) :
    (∑ u : Rˣ, χ (u : R) * ψ ((a : R) * (u : R))) =
      χ ((a⁻¹ : Rˣ) : R) * unitGauss χ ψ := by
  classical
  have hsub := Equiv.sum_comp (Equiv.mulLeft a⁻¹)
    (fun u : Rˣ => χ (u : R) * ψ ((a : R) * (u : R)))
  rw [← hsub]
  change (∑ u : Rˣ, χ ((a⁻¹ * u : Rˣ) : R) *
    ψ ((a : R) * ((a⁻¹ * u : Rˣ) : R))) = _
  have hc (u : Rˣ) : (a : R) * ((a⁻¹ * u : Rˣ) : R) = (u : R) := by
    rw [← Units.val_mul]
    simp
  simp_rw [hc]
  simp only [Units.val_mul, map_mul]
  rw [unitGauss, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

theorem inverse_unitGauss_shift (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (a : Rˣ) :
    (∑ u : Rˣ, χ⁻¹ (u : R) * ψ ((a : R) * (u : R))) =
      χ (a : R) * unitGauss χ⁻¹ ψ := by
  rw [unitGauss_shift, inverse_character_unit, inv_inv]

theorem inverse_phase_sum (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (a : Rˣ) :
    (∑ x : Rˣ, χ (x : R) * ψ ((a : R) * ((x⁻¹ : Rˣ) : R))) =
      χ (a : R) * unitGauss χ⁻¹ ψ := by
  classical
  have hsub := Equiv.sum_comp (Equiv.inv Rˣ)
    (fun x : Rˣ => χ (x : R) * ψ ((a : R) * ((x⁻¹ : Rˣ) : R)))
  rw [← hsub]
  simp only [Equiv.inv_apply, inv_inv, ← inverse_character_unit]
  exact inverse_unitGauss_shift χ ψ a

theorem kloosterman_unit_transform (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (h b l : Rˣ) :
    (∑ eta : Rˣ, χ⁻¹ (eta : R) *
      kloosterman ψ ((eta * h * b : Rˣ) : R) (l : R)) =
      unitGauss χ⁻¹ ψ ^ 2 * χ ((h * b * l : Rˣ) : R) := by
  classical
  simp only [kloosterman, Finset.mul_sum, AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : Rˣ,
        ((∑ eta : Rˣ, χ⁻¹ (eta : R) *
          ψ (((h * b * x : Rˣ) : R) * (eta : R))) *
          ψ ((l : R) * ((x⁻¹ : Rˣ) : R))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro eta heta
      simp only [Units.val_mul]
      rw [show ((eta : R) * (h : R) * (b : R)) * (x : R) =
        ((h : R) * (b : R) * (x : R)) * (eta : R) by ring]
      ring
    _ = ∑ x : Rˣ, (χ ((h * b * x : Rˣ) : R) * unitGauss χ⁻¹ ψ) *
          ψ ((l : R) * ((x⁻¹ : Rˣ) : R)) := by
      simp_rw [inverse_unitGauss_shift]
    _ = (unitGauss χ⁻¹ ψ * χ ((h * b : Rˣ) : R)) *
        ∑ x : Rˣ, χ (x : R) * ψ ((l : R) * ((x⁻¹ : Rˣ) : R)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Units.val_mul, map_mul]
      ring
    _ = unitGauss χ⁻¹ ψ ^ 2 * χ ((h * b * l : Rˣ) : R) := by
      rw [inverse_phase_sum]
      simp only [Units.val_mul, map_mul]
      ring

theorem kloosterman_gaussSum_transform (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (h b l : Rˣ) :
    (∑ eta : Rˣ, χ⁻¹ (eta : R) *
      kloosterman ψ ((eta * h * b : Rˣ) : R) (l : R)) =
      gaussSum χ⁻¹ ψ ^ 2 * χ ((h * b * l : Rˣ) : R) := by
  simpa only [unitGauss_eq_gaussSum] using kloosterman_unit_transform χ ψ h b l

theorem zmod_standard_transform {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (h b l : (ZMod N)ˣ) :
    (∑ eta : (ZMod N)ˣ, χ⁻¹ (eta : ZMod N) *
      kloosterman ZMod.stdAddChar ((eta * h * b : (ZMod N)ˣ) : ZMod N) (l : ZMod N)) =
      gaussSum χ⁻¹ ZMod.stdAddChar ^ 2 * χ ((h * b * l : (ZMod N)ˣ) : ZMod N) := by
  exact kloosterman_gaussSum_transform χ ZMod.stdAddChar h b l

theorem kloosterman_conjugate_transform (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (h b l : Rˣ) :
    (∑ eta : Rˣ, star (χ (eta : R)) *
      kloosterman ψ ((eta * h * b : Rˣ) : R) (l : R)) =
      gaussSum (star χ) ψ ^ 2 * χ ((h * b * l : Rˣ) : R) := by
  simpa only [MulChar.star_apply', MulChar.star_eq_inv] using
    kloosterman_gaussSum_transform χ ψ h b l

theorem kloosterman_transform_real_part (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (h b l : Rˣ) :
    (∑ eta : Rˣ, (χ⁻¹ (eta : R) *
      kloosterman ψ ((eta * h * b : Rˣ) : R) (l : R)).re) =
      (gaussSum χ⁻¹ ψ ^ 2 * χ ((h * b * l : Rˣ) : R)).re := by
  have hcomplex := congrArg Complex.re (kloosterman_gaussSum_transform χ ψ h b l)
  simpa only [Complex.re_sum] using hcomplex

theorem weighted_transform_real_part {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (h b l : ι → Rˣ) :
    (∑ t ∈ s, c t * ∑ eta : Rˣ, (χ⁻¹ (eta : R) *
      kloosterman ψ ((eta * h t * b t : Rˣ) : R) (l t : R)).re) =
    ∑ t ∈ s, c t * (gaussSum χ⁻¹ ψ ^ 2 * χ ((h t * b t * l t : Rˣ) : R)).re := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [kloosterman_transform_real_part]

#print axioms unitGauss_eq_gaussSum
#print axioms inverse_character_unit
#print axioms unitGauss_shift
#print axioms inverse_unitGauss_shift
#print axioms inverse_phase_sum
#print axioms kloosterman_unit_transform
#print axioms kloosterman_gaussSum_transform
#print axioms zmod_standard_transform
#print axioms kloosterman_conjugate_transform
#print axioms kloosterman_transform_real_part
#print axioms weighted_transform_real_part

end GoldbachResearch.QuotientGauss
