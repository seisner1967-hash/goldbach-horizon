import ContinuousTraceTails22
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/- Source only. This module treats the genuine real archimedean integrand on
   x≥2. It neither defines nor assumes a formula of Weil for arithmetic data. -/

noncomputable section
open Set MeasureTheory

namespace GoldbachContinuous22

def archIntegrand (Y x : ℝ) : ℝ :=
  (realTest Y x + realTest Y (1 / x) / x - 2 * realTest Y 1 / x) / (x - 1 / x)

def archMajorant (Y x : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (Real.exp (-x / Y) / Y + 1 / (Y * x ^ 3) + 2 / (Y * x ^ 2))

theorem realTest_nonneg {Y x : ℝ} (hY : 0 < Y) (hx : 0 ≤ x) :
    0 ≤ realTest Y x := by
  unfold realTest
  positivity

theorem realTest_inv_le {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) :
    realTest Y (1 / x) ≤ 1 / (Y * x) := by
  have hexp : Real.exp (-(1 / x) / Y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by positivity)
  unfold realTest
  calc
    (1 / x / Y) * Real.exp (-(1 / x) / Y) ≤ (1 / x / Y) * 1 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 1 / (Y * x) := by ring

/-- Pointwise majorant derived from the actual denominator and numerator. -/
theorem abs_archIntegrand_le {Y x : ℝ} (hY : 0 < Y) (hx : 2 ≤ x) :
    |archIntegrand Y x| ≤ archMajorant Y x := by
  have hx0 : 0 < x := by linarith
  have hfx := realTest_nonneg hY hx0.le
  have hfi := realTest_nonneg hY (one_div_pos.mpr hx0).le
  have hf1 := realTest_nonneg hY (show 0 ≤ (1 : ℝ) by norm_num)
  have hbi := realTest_inv_le hY hx0
  have hb1 := realTest_one_le hY
  have hnum : |realTest Y x + realTest Y (1 / x) / x - 2 * realTest Y 1 / x| ≤
      realTest Y x + 1 / (Y * x ^ 2) + 2 / (Y * x) := by
    calc
      |realTest Y x + realTest Y (1 / x) / x - 2 * realTest Y 1 / x| ≤
          |realTest Y x + realTest Y (1 / x) / x| + |2 * realTest Y 1 / x| :=
        abs_sub_le _ _
      _ ≤ |realTest Y x| + |realTest Y (1 / x) / x| + |2 * realTest Y 1 / x| :=
        add_le_add_right (abs_add _ _) _
      _ = realTest Y x + realTest Y (1 / x) / x + 2 * realTest Y 1 / x := by
        rw [abs_of_nonneg hfx, abs_of_nonneg (div_nonneg hfi hx0.le),
          abs_of_nonneg (by positivity : 0 ≤ 2 * realTest Y 1 / x)]
      _ ≤ realTest Y x + (1 / (Y * x)) / x + 2 * (1 / Y) / x := by
        gcongr
      _ = realTest Y x + 1 / (Y * x ^ 2) + 2 / (Y * x) := by ring
  have hd := arch_denominator_pos hx
  have hden := arch_denominator_inv_le hx
  have hp : 0 ≤ realTest Y x + 1 / (Y * x ^ 2) + 2 / (Y * x) := by positivity
  unfold archIntegrand
  rw [abs_div, abs_of_pos hd, div_eq_mul_inv, ← one_div]
  calc
    _ ≤ (realTest Y x + 1 / (Y * x ^ 2) + 2 / (Y * x)) * (4 / (3 * x)) :=
      mul_le_mul hnum hden (one_div_nonneg.mpr hd.le) hp
    _ = archMajorant Y x := by
      unfold realTest archMajorant
      field_simp [hY.ne', hx0.ne']
      ring

theorem rpow_neg_nat_eq_inv_pow (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(n : ℝ)) = 1 / x ^ n := by
  simp only [Real.rpow_neg hx, Real.rpow_natCast, one_div]

theorem integrable_inverse_power {R : ℝ} (hR : 0 < R) (n : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (fun x : ℝ => 1 / x ^ n) (Ioi R) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := Real.integrableOn_Ioi_rpow_of_lt (by linarith : -(n : ℝ) < -1) hR
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  exact rpow_neg_nat_eq_inv_pow n (hR.trans hx).le

theorem integral_inverse_square {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ in Ioi R, 1 / x ^ 2) = 1 / R := by
  have h := Real.integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hR
  have heq : (fun x : ℝ => x ^ (-2 : ℝ)) =ᵐ[volume.restrict (Ioi R)]
      (fun x : ℝ => 1 / x ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact rpow_neg_nat_eq_inv_pow 2 (hR.trans hx).le
  rw [integral_congr_ae heq] at h
  norm_num only [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at h
  simpa only [neg_div_neg_eq, div_one, one_div] using h

theorem integral_inverse_cube {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ in Ioi R, 1 / x ^ 3) = 1 / (2 * R ^ 2) := by
  have h := Real.integral_Ioi_rpow_of_lt (show (-3 : ℝ) < -1 by norm_num) hR
  have heq : (fun x : ℝ => x ^ (-3 : ℝ)) =ᵐ[volume.restrict (Ioi R)]
      (fun x : ℝ => 1 / x ^ 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact rpow_neg_nat_eq_inv_pow 3 (hR.trans hx).le
  rw [integral_congr_ae heq] at h
  norm_num only [show (-3 : ℝ) + 1 = -2 by norm_num] at h
  rw [rpow_neg_nat_eq_inv_pow 2 hR.le] at h
  calc
    _ = -(1 / R ^ 2) / (-2) := h
    _ = 1 / (2 * R ^ 2) := by ring

theorem scaled_exp_tail_integrable {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => Real.exp (-x / Y) / Y) (Ioi R) := by
  have h : IntegrableOn (fun x : ℝ => Real.exp (-x / Y)) (Ioi 0) := by
    have h0 := real_laplace_integrable (show 0 < (1 : ℝ) by norm_num)
      (one_div_pos.mpr hY)
    simpa only [sub_self, Real.rpow_zero, mul_one, neg_div, one_div_mul_eq_div] using h0
  have hr := h.mono_set (Ioi_subset_Ioi hR.le)
  simpa only [div_eq_mul_inv, mul_comm] using hr.const_mul (1 / Y)

theorem integral_scaled_exp_tail {Y R : ℝ} (hY : 0 < Y) :
    (∫ x : ℝ in Ioi R, Real.exp (-x / Y) / Y) = Real.exp (-R / Y) := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) R
    (one_div_pos.mpr hY)
  rw [Real.integral_exp_neg_Ioi] at h
  have heq : (fun x : ℝ => Real.exp (-x / Y) / Y) =
      fun x : ℝ => (1 / Y) * Real.exp (-((1 / Y) * x)) := by
    funext x
    rw [show -x / Y = -((1 / Y) * x) by ring]
    ring
  rw [heq, integral_const_mul, h]
  have hexp : Real.exp (-((1 / Y) * R)) = Real.exp (-R / Y) := by
    congr 1
    ring
  rw [hexp, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (one_div_ne_zero hY.ne'), one_mul]

theorem archMajorant_integrable {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) :
    IntegrableOn (archMajorant Y) (Ioi R) := by
  have h0 := scaled_exp_tail_integrable hY hR
  have h1 := (integrable_inverse_power hR 3 (by norm_num)).const_mul (1 / Y)
  have h2 := (integrable_inverse_power hR 2 (by norm_num)).const_mul (2 / Y)
  have h := ((h0.add h1).add h2).const_mul (4 / 3 : ℝ)
  apply h.congr_fun _ measurableSet_Ioi
  intro x _
  unfold archMajorant
  ring

theorem integral_archMajorant {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) :
    (∫ x : ℝ in Ioi R, archMajorant Y x) = archError Y R := by
  have h0 := scaled_exp_tail_integrable hY hR
  have h1 := (integrable_inverse_power hR 3 (by norm_num)).const_mul (1 / Y)
  have h2 := (integrable_inverse_power hR 2 (by norm_num)).const_mul (2 / Y)
  have heq : archMajorant Y = fun x : ℝ => (4 / 3 : ℝ) *
      (Real.exp (-x / Y) / Y + (1 / Y) * (1 / x ^ 3) + (2 / Y) * (1 / x ^ 2)) := by
    funext x
    unfold archMajorant
    ring
  rw [heq, integral_const_mul, integral_add (h0.add h1) h2, integral_add h0 h1,
    integral_const_mul, integral_const_mul, integral_scaled_exp_tail hY,
    integral_inverse_cube hR, integral_inverse_square hR]
  unfold archError
  ring

/-- Integrability and the closed H6 bound for the actual archimedean tail. -/
theorem arch_tail_integrable_and_bound {Y R : ℝ} (hY : 0 < Y) (hR : 2 ≤ R) :
    IntegrableOn (archIntegrand Y) (Ioi R) ∧
      |∫ x : ℝ in Ioi R, archIntegrand Y x| ≤ archError Y R := by
  have hR0 : 0 < R := by linarith
  have hg := archMajorant_integrable hY hR0
  have hcont : ContinuousOn (archIntegrand Y) (Ioi R) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx2 : 2 ≤ x := hR.trans hx.le
    have hx0 : 0 < x := by linarith
    have hd := arch_denominator_pos hx2
    unfold archIntegrand realTest
    fun_prop (disch := positivity)
  have hle : ∀ x ∈ Ioi R, ‖archIntegrand Y x‖ ≤ archMajorant Y x := by
    intro x hx
    exact abs_archIntegrand_le hY (hR.trans hx.le)
  have hf : IntegrableOn (archIntegrand Y) (Ioi R) := by
    apply hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hle x hx
  refine ⟨hf, ?_⟩
  calc
    |∫ x : ℝ in Ioi R, archIntegrand Y x| ≤ ∫ x : ℝ in Ioi R, ‖archIntegrand Y x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi R, archMajorant Y x := by
      apply integral_mono_ae hf.norm hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hle x hx
    _ = archError Y R := integral_archMajorant hY hR0

end GoldbachContinuous22

#print axioms GoldbachContinuous22.archIntegrand
#print axioms GoldbachContinuous22.archMajorant
#print axioms GoldbachContinuous22.realTest_nonneg
#print axioms GoldbachContinuous22.realTest_inv_le
#print axioms GoldbachContinuous22.abs_archIntegrand_le
#print axioms GoldbachContinuous22.rpow_neg_nat_eq_inv_pow
#print axioms GoldbachContinuous22.integrable_inverse_power
#print axioms GoldbachContinuous22.integral_inverse_square
#print axioms GoldbachContinuous22.integral_inverse_cube
#print axioms GoldbachContinuous22.scaled_exp_tail_integrable
#print axioms GoldbachContinuous22.integral_scaled_exp_tail
#print axioms GoldbachContinuous22.archMajorant_integrable
#print axioms GoldbachContinuous22.integral_archMajorant
#print axioms GoldbachContinuous22.arch_tail_integrable_and_bound
