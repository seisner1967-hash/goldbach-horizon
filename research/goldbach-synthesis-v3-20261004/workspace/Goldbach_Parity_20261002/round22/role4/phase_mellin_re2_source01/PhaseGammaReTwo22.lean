import GammaPrerequisites22
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-! SOURCE ONLY. Genuine Gamma on Re(s)=2, rotated through atan(t/2).
The pi/2 decay and the phase factor are derived; no improved Gamma estimate,
zeta estimate or Mellin representation is supplied as a premise. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def reTwoS (t : ℝ) : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I

def reTwoBeta (t : ℝ) : ℝ := Real.arctan (t / 2)

def reTwoW (a theta : ℝ) : ℂ := (a : ℂ) - (theta : ℂ) * Complex.I

def reTwoGap (a theta : ℝ) : ℝ := Real.pi / 2 - |Complex.arg (reTwoW a theta)|

theorem reTwoS_re (t : ℝ) : (reTwoS t).re = 2 := by simp [reTwoS]

theorem reTwoS_im (t : ℝ) : (reTwoS t).im = t := by simp [reTwoS]

theorem reTwoBeta_mem (t : ℝ) : reTwoBeta t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  Real.arctan_mem_Ioo (t / 2)

/-- The comparison with the identity is paid by the actual arctan derivative. -/
theorem reTwo_arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hder : ∀ y : ℝ, deriv Real.arctan y ≤ 1 := by
    intro y
    rw [Real.deriv_arctan]
    apply (div_le_iff₀ (by positivity : 0 < 1 + y ^ 2)).mpr
    nlinarith [sq_nonneg y]
  have h := image_sub_le_mul_sub_of_deriv_le Real.differentiable_arctan hder hx
  simpa only [Real.arctan_zero, sub_zero, one_mul] using h

theorem reTwoBeta_cos_coefficient (t : ℝ) :
    (1 / Real.cos (reTwoBeta t)) ^ (2 : ℝ) = (t ^ 2 + 4) / 4 := by
  unfold reTwoBeta
  rw [Real.rpow_two, div_pow, one_pow, Real.cos_sq_arctan, one_div_one_div]
  ring

theorem reTwoBeta_product_abs (t : ℝ) :
    t * reTwoBeta t = |t| * Real.arctan (|t| / 2) := by
  unfold reTwoBeta
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), neg_div, Real.arctan_neg]
    ring

/-- The loss at the pi/2 edge is at most two, with no limiting angle used. -/
theorem reTwoBeta_defect_le_two (t : ℝ) :
    Real.pi * |t| / 2 - t * reTwoBeta t ≤ 2 := by
  rw [reTwoBeta_product_abs]
  by_cases ht : |t| = 0
  · simp only [ht, mul_zero, zero_mul, zero_sub]
    norm_num
  · have hp : 0 < |t| := (abs_nonneg t).lt_of_ne' ht
    have hi := Real.arctan_inv_of_pos (by positivity : 0 < |t| / 2)
    have harg : (|t| / 2)⁻¹ = 2 / |t| := by
      field_simp [hp.ne'] <;> ring
    rw [harg] at hi
    have h := mul_le_mul_of_nonneg_left
      (reTwo_arctan_le_self (by positivity : 0 ≤ 2 / |t|)) hp.le
    rw [hi] at h
    have he : |t| * (2 / |t|) = 2 := by field_simp [hp.ne'] <;> ring
    rw [he] at h
    nlinarith

/-- G2, from the independently checked complex Laplace rotation theorem. -/
theorem norm_Gamma_reTwo_le (t : ℝ) :
    ‖Complex.Gamma (reTwoS t)‖ ≤
      (t ^ 2 + 4) / 4 * Real.exp (2 - Real.pi * |t| / 2) := by
  have hb := reTwoBeta_mem t
  have hrot := Gamma_rotation_bound (s := reTwoS t)
    (show 0 < (reTwoS t).re by rw [reTwoS_re]; norm_num) hb.1 hb.2
  rw [reTwoS_re, reTwoS_im, Real.Gamma_two, mul_one,
    reTwoBeta_cos_coefficient] at hrot
  calc
    _ ≤ Real.exp (-reTwoBeta t * t) * ((t ^ 2 + 4) / 4) := hrot
    _ ≤ Real.exp (2 - Real.pi * |t| / 2) * ((t ^ 2 + 4) / 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [reTwoBeta_defect_le_two t]
    _ = _ := mul_comm _ _

theorem reTwoW_re (a theta : ℝ) : (reTwoW a theta).re = a := by simp [reTwoW]

theorem reTwoW_ne_zero {a : ℝ} (ha : 0 < a) (theta : ℝ) : reTwoW a theta ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  rw [reTwoW_re, Complex.zero_re] at hr
  exact ha.ne' hr

theorem reTwoGap_pos {a : ℝ} (ha : 0 < a) (theta : ℝ) : 0 < reTwoGap a theta := by
  unfold reTwoGap
  apply sub_pos.mpr
  exact Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (by simpa only [reTwoW_re] using ha))

/-- Exact norm of the principal power, retaining the real argument factor. -/
theorem norm_reTwo_principal_power {w : ℂ} (hw : w ≠ 0) (t : ℝ) :
    ‖w ^ (-reTwoS t)‖ = ‖w‖ ^ (-2 : ℝ) * Real.exp (t * Complex.arg w) := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_of_ne_zero hw]
  simp only [Complex.neg_re, reTwoS_re, Complex.neg_im, reTwoS_im]
  rw [mul_neg, Real.exp_neg, div_inv_eq_mul]
  rw [mul_comm (Complex.arg w) t] <;> rfl

theorem reTwo_exponent_le_gap (a theta t : ℝ) :
    -Real.pi * |t| / 2 + t * Complex.arg (reTwoW a theta) ≤ -reTwoGap a theta * |t| := by
  have h := le_abs_self (t * Complex.arg (reTwoW a theta))
  rw [abs_mul] at h
  unfold reTwoGap
  nlinarith

theorem reTwoS_continuous : Continuous reTwoS := by unfold reTwoS; fun_prop

theorem Gamma_reTwo_continuous : Continuous (fun t : ℝ => Complex.Gamma (reTwoS t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hg := (Complex.differentiableAt_Gamma (reTwoS t) (fun n => by
    intro hn
    have hr := congrArg Complex.re hn
    simp only [reTwoS_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith)).continuousAt
  exact hg.comp reTwoS_continuous.continuousAt

theorem reTwoGap_continuousAt {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => reTwoGap q.1 q.2) p := by
  have hw : Continuous (fun q : ℝ × ℝ => reTwoW q.1 q.2) := by unfold reTwoW; fun_prop
  have hslit : reTwoW p.1 p.2 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa only [reTwoW_re] using hp))
  have harg := (Complex.continuousAt_arg hslit).comp hw.continuousAt
  exact continuousAt_const.sub harg.abs

theorem reTwoGap_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => reTwoGap p.1 p.2) {p | 0 < p.1} :=
  fun p hp => (reTwoGap_continuousAt hp).continuousWithinAt

end GoldbachContinuous22

#print axioms GoldbachContinuous22.reTwoS
#print axioms GoldbachContinuous22.reTwoBeta
#print axioms GoldbachContinuous22.reTwoW
#print axioms GoldbachContinuous22.reTwoGap
#print axioms GoldbachContinuous22.reTwoS_re
#print axioms GoldbachContinuous22.reTwoS_im
#print axioms GoldbachContinuous22.reTwoBeta_mem
#print axioms GoldbachContinuous22.reTwo_arctan_le_self
#print axioms GoldbachContinuous22.reTwoBeta_cos_coefficient
#print axioms GoldbachContinuous22.reTwoBeta_product_abs
#print axioms GoldbachContinuous22.reTwoBeta_defect_le_two
#print axioms GoldbachContinuous22.norm_Gamma_reTwo_le
#print axioms GoldbachContinuous22.reTwoW_re
#print axioms GoldbachContinuous22.reTwoW_ne_zero
#print axioms GoldbachContinuous22.reTwoGap_pos
#print axioms GoldbachContinuous22.norm_reTwo_principal_power
#print axioms GoldbachContinuous22.reTwo_exponent_le_gap
#print axioms GoldbachContinuous22.reTwoS_continuous
#print axioms GoldbachContinuous22.Gamma_reTwo_continuous
#print axioms GoldbachContinuous22.reTwoGap_continuousAt
#print axioms GoldbachContinuous22.reTwoGap_continuousOn
