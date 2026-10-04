import GammaPrerequisites22
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds

/- SOURCE_ONLY. This module constructs the actual Gamma derivative bound using
   the Cauchy integral and a proved circle dominateur. It has not been compiled.
   It is distinct from the frozen Gamma repair preparation. No zero count,
   completeness certificate, Weil identity, or Goldbach coefficient is asserted. -/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace GoldbachContinuous22

/-- Real Gamma has an explicit majorant on the larger strip needed by Cauchy. -/
theorem realGamma_le_nine_fifths_on_extended_strip {sigma : ℝ}
    (hsigma0 : 1 / 2 ≤ sigma) (hsigma1 : sigma ≤ 5 / 2) :
    Real.Gamma sigma ≤ 9 / 5 := by
  have hsqrt : Real.sqrt Real.pi ≤ 9 / 5 := by
    have hsquared := Real.sq_sqrt Real.pi_pos.le
    have hnonneg := Real.sqrt_nonneg Real.pi
    have hpi := Real.pi_lt_d2
    nlinarith
  have hhalf : Real.Gamma (1 / 2) ≤ 9 / 5 := by
    simpa only [Real.Gamma_one_half_eq] using hsqrt
  have hthree : Real.Gamma (3 / 2) = (1 / 2) * Real.Gamma (1 / 2) := by
    convert Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hfive : Real.Gamma (5 / 2) = (3 / 2) * Real.Gamma (3 / 2) := by
    convert Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hupper : Real.Gamma (5 / 2) ≤ 9 / 5 := by
    rw [hfive, hthree]
    nlinarith [Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  let beta : ℝ := (sigma - 1 / 2) / 2
  have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
  have hb1 : beta ≤ 1 := by dsimp [beta]; linarith
  have ha : 0 ≤ 1 - beta := by linarith
  have hconv := Real.convexOn_Gamma.2
    (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0)
    (by norm_num : (5 / 2 : ℝ) ∈ Ioi 0)
    ha hb0 (by ring : (1 - beta) + beta = 1)
  have hid : (1 - beta) • (1 / 2 : ℝ) + beta • (5 / 2 : ℝ) = sigma := by
    simp only [smul_eq_mul]
    dsimp [beta]
    ring
  rw [hid] at hconv
  calc
    Real.Gamma sigma ≤ (1 - beta) * Real.Gamma (1 / 2) +
        beta * Real.Gamma (5 / 2) := by simpa only [smul_eq_mul] using hconv
    _ ≤ (1 - beta) * (9 / 5) + beta * (9 / 5) :=
      add_le_add (mul_le_mul_of_nonneg_left hhalf ha)
        (mul_le_mul_of_nonneg_left hupper hb0)
    _ = 9 / 5 := by ring

theorem quarter_angle_coefficient_le_three_extended {sigma : ℝ}
    (hsigma : sigma ≤ 5 / 2) :
    (1 / Real.cos (Real.pi / 4)) ^ sigma ≤ 3 := by
  have hsquared : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrt_nonneg := Real.sqrt_nonneg (2 : ℝ)
  have hb : 1 ≤ Real.sqrt 2 := by nlinarith
  have hsqrt_upper : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have hid : 1 / Real.cos (Real.pi / 4) = Real.sqrt 2 := by
    rw [Real.cos_pi_div_four]
    field_simp [hsqrt0] <;> nlinarith
  rw [hid]
  calc
    Real.sqrt 2 ^ sigma ≤ Real.sqrt 2 ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    _ = Real.sqrt 2 ^ (3 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.sqrt 2) 3
    _ = 2 * Real.sqrt 2 := by rw [pow_succ, hsquared]
    _ ≤ 3 := by nlinarith

/-- The larger-strip bound is derived from the actual complex-rate rotation. -/
theorem Gamma_extended_strip_exponential_bound {s : ℂ}
    (hs0 : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 5 / 2) :
    ‖Complex.Gamma s‖ ≤ (27 / 5) * Real.exp (-(Real.pi / 4) * |s.im|) := by
  have positive_case : ∀ u : ℂ, 1 / 2 ≤ u.re → u.re ≤ 5 / 2 → 0 ≤ u.im →
      ‖Complex.Gamma u‖ ≤ (27 / 5) * Real.exp (-(Real.pi / 4) * u.im) := by
    intro u hu0 hu1 _
    have hrot := Gamma_rotation_bound (show 0 < u.re by linarith)
      (show -(Real.pi / 2) < Real.pi / 4 by linarith [Real.pi_pos])
      (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])
    have hreal := realGamma_le_nine_fifths_on_extended_strip hu0 hu1
    have hcoef : (1 / Real.cos (Real.pi / 4)) ^ u.re * Real.Gamma u.re ≤ 27 / 5 := by
      have hcos : 0 < Real.cos (Real.pi / 4) := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      calc
        _ ≤ (1 / Real.cos (Real.pi / 4)) ^ u.re * (9 / 5) :=
          mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg (by positivity) _)
        _ ≤ 3 * (9 / 5) := mul_le_mul_of_nonneg_right
          (quarter_angle_coefficient_le_three_extended hu1) (by norm_num)
        _ = 27 / 5 := by norm_num
    calc
      _ ≤ Real.exp (-(Real.pi / 4) * u.im) *
          ((1 / Real.cos (Real.pi / 4)) ^ u.re * Real.Gamma u.re) := hrot
      _ ≤ Real.exp (-(Real.pi / 4) * u.im) * (27 / 5) :=
        mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le
      _ = (27 / 5) * Real.exp (-(Real.pi / 4) * u.im) := mul_comm _ _
  by_cases him : 0 ≤ s.im
  · simpa only [abs_of_nonneg him] using positive_case s hs0 hs1 him
  · have hsneg : s.im < 0 := lt_of_not_ge him
    have hc := positive_case (starRingEnd ℂ s)
      (by simpa using hs0) (by simpa using hs1)
      (by simpa only [Complex.conj_im] using (neg_nonneg.mpr hsneg.le))
    simpa only [Complex.Gamma_conj, RCLike.norm_conj, Complex.conj_im,
      abs_of_neg hsneg, neg_mul, mul_neg] using hc

theorem exp_eighth_pi_le_seven_quarters : Real.exp (Real.pi / 8) ≤ 7 / 4 := by
  have hsquared : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hhalf : Real.exp (1 / 2) ≤ 7 / 4 := by
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]
  exact (Real.exp_le_exp.mpr (by linarith [Real.pi_lt_d2])).trans hhalf

theorem Gamma_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ Complex.Gamma rightHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  change 0 < s.re at hs
  linarith

theorem Gamma_half_disc_domain {s : ℂ} (hs0 : 1 ≤ s.re) :
    closedBall s (1 / 2) ⊆ rightHalfPlane := by
  intro w hw
  have hnorm : ‖w - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have habs : |w.re - s.re| ≤ 1 / 2 := by
    have h := (Complex.abs_re_le_abs (w - s)).trans hnorm
    simpa only [Complex.sub_re, Complex.norm_eq_abs] using h
  change 0 < w.re
  have h := (abs_le.mp habs).1
  linarith

/-- A constructed uniform bound on the Cauchy contour, including its phase shift. -/
theorem Gamma_circle_dominating_bound {s w : ℂ}
    (hs0 : 1 ≤ s.re) (hs1 : s.re ≤ 2) (hw : w ∈ sphere s (1 / 2)) :
    ‖Complex.Gamma w‖ ≤ (189 / 20) * Real.exp (-(Real.pi / 4) * |s.im|) := by
  have hnorm : ‖w - s‖ = 1 / 2 := by
    simpa only [mem_sphere, dist_eq_norm] using hw
  have hre : |w.re - s.re| ≤ 1 / 2 := by
    have h := (Complex.abs_re_le_abs (w - s)).trans_eq hnorm
    simpa only [Complex.sub_re] using h
  have him : |w.im - s.im| ≤ 1 / 2 := by
    have h := (Complex.abs_im_le_abs (w - s)).trans_eq hnorm
    simpa only [Complex.sub_im] using h
  have hwr0 : 1 / 2 ≤ w.re := by have h := (abs_le.mp hre).1; linarith
  have hwr1 : w.re ≤ 5 / 2 := by have h := (abs_le.mp hre).2; linarith
  have htri : |s.im| ≤ |w.im| + 1 / 2 := by
    calc
      |s.im| = |w.im + (s.im - w.im)| := by congr 1; ring
      _ ≤ |w.im| + |s.im - w.im| := abs_add _ _
      _ ≤ |w.im| + 1 / 2 := add_le_add_left (by simpa [abs_sub_comm] using him) _
  have hexp : Real.exp (-(Real.pi / 4) * |w.im|) ≤
      Real.exp (-(Real.pi / 4) * |s.im|) * Real.exp (Real.pi / 8) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  calc
    ‖Complex.Gamma w‖ ≤ (27 / 5) * Real.exp (-(Real.pi / 4) * |w.im|) :=
      Gamma_extended_strip_exponential_bound hwr0 hwr1
    _ ≤ (27 / 5) * (Real.exp (-(Real.pi / 4) * |s.im|) * Real.exp (Real.pi / 8)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ (27 / 5) * (Real.exp (-(Real.pi / 4) * |s.im|) * (7 / 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left exp_eighth_pi_le_seven_quarters (Real.exp_pos _).le)
        (by norm_num)
    _ = (189 / 20) * Real.exp (-(Real.pi / 4) * |s.im|) := by ring

/-- Gprime19 follows from the actual Cauchy derivative formula and contour bound.
    It does not assume the derivative of a rotated integral or a free majorant. -/
theorem Gamma_derivative_strip_exponential_bound {s : ℂ}
    (hs0 : 1 ≤ s.re) (hs1 : s.re ≤ 2) :
    ‖deriv Complex.Gamma s‖ ≤ 19 * Real.exp (-(Real.pi / 4) * |s.im|) := by
  have hdiff : DiffContOnCl ℂ Complex.Gamma (ball s (1 / 2)) :=
    Gamma_differentiableOn_rightHalfPlane.diffContOnCl_ball (Gamma_half_disc_domain hs0)
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (show (0 : ℝ) < 1 / 2 by norm_num) hdiff
    (fun w hw => Gamma_circle_dominating_bound hs0 hs1 hw)
  calc
    ‖deriv Complex.Gamma s‖ ≤
        ((189 / 20) * Real.exp (-(Real.pi / 4) * |s.im|)) / (1 / 2) := hbound
    _ = (189 / 10) * Real.exp (-(Real.pi / 4) * |s.im|) := by ring
    _ ≤ 19 * Real.exp (-(Real.pi / 4) * |s.im|) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le

end GoldbachContinuous22

#print axioms GoldbachContinuous22.realGamma_le_nine_fifths_on_extended_strip
#print axioms GoldbachContinuous22.quarter_angle_coefficient_le_three_extended
#print axioms GoldbachContinuous22.Gamma_extended_strip_exponential_bound
#print axioms GoldbachContinuous22.exp_eighth_pi_le_seven_quarters
#print axioms GoldbachContinuous22.Gamma_differentiableOn_rightHalfPlane
#print axioms GoldbachContinuous22.Gamma_half_disc_domain
#print axioms GoldbachContinuous22.Gamma_circle_dominating_bound
#print axioms GoldbachContinuous22.Gamma_derivative_strip_exponential_bound
