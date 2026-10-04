import ComplexGammaMellinLocal22
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! SOURCE ONLY. One read-only local import is the actual independently
checked Local26. No Lambda, Tail, zeta or coefficient module is imported.
The linked norm/argument geometry is proved from the actual principal arg,
the double-angle identity and the norm square. The decay floor is derived
from an actual reciprocal arctangent identity; no final geometry premise
is supplied. No author compilation, probe or numerical evaluation occurred.
This module does not claim cancellation, a coefficient certificate or D_N. -/

noncomputable section
open Set
open scoped Topology

namespace GoldbachComplexGammaMellin22

def circleMellinPoint (a theta : ℝ) : ℂ := (a : ℂ) - (theta : ℂ) * Complex.I

def circleMellinRadius (a theta : ℝ) : ℝ := Real.sqrt (a ^ 2 + theta ^ 2)

def circleDecayFloor (a : ℝ) : ℝ := Real.arctan (a / Real.pi) / 2

theorem circleMellinPoint_re (a theta : ℝ) : (circleMellinPoint a theta).re = a := by
  simp [circleMellinPoint]

theorem circleMellinPoint_im (a theta : ℝ) : (circleMellinPoint a theta).im = -theta := by
  simp [circleMellinPoint]

theorem circleMellinPoint_ne_zero {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    circleMellinPoint a theta ≠ 0 := by
  apply rightHalfPlane_ne_zero
  simpa only [circleMellinPoint_re] using ha

theorem circleMellinPoint_mem_slitPlane {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    circleMellinPoint a theta ∈ Complex.slitPlane := by
  apply rightHalfPlane_mem_slitPlane
  simpa only [circleMellinPoint_re] using ha

theorem circleMellinPoint_norm_eq_radius (a theta : ℝ) :
    ‖circleMellinPoint a theta‖ = circleMellinRadius a theta := by
  rw [Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq,
    circleMellinPoint_re, circleMellinPoint_im]
  simp only [sq_neg, circleMellinRadius]

theorem circleMellinPoint_norm_sq (a theta : ℝ) :
    ‖circleMellinPoint a theta‖ ^ 2 = a ^ 2 + theta ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    circleMellinPoint_re, circleMellinPoint_im]
  ring

theorem circleMellinPoint_norm_pos {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    0 < ‖circleMellinPoint a theta‖ :=
  norm_pos_iff.mpr (circleMellinPoint_ne_zero ha theta)

theorem circleMellinPoint_abs_theta_le_norm (a theta : ℝ) :
    |theta| ≤ ‖circleMellinPoint a theta‖ := by
  simpa only [circleMellinPoint_im, abs_neg, Complex.norm_eq_abs] using
    Complex.abs_im_le_abs (circleMellinPoint a theta)

theorem circleMellinRadius_pos {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    0 < circleMellinRadius a theta := by
  rw [← circleMellinPoint_norm_eq_radius]
  exact circleMellinPoint_norm_pos ha theta

/-- The argument branch is fixed by the right half-plane, not assumed. -/
theorem circleMellinPoint_arg {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Complex.arg (circleMellinPoint a theta) = -Real.arctan (theta / a) := by
  have hright : 0 < (circleMellinPoint a theta).re := by
    simpa only [circleMellinPoint_re] using ha
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hright))
  have ht := Real.arctan_tan harg.1 harg.2
  rw [Complex.tan_arg, circleMellinPoint_im, circleMellinPoint_re,
    neg_div, Real.arctan_neg] at ht
  exact ht.symm

theorem circleMellinPoint_abs_arg {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    |Complex.arg (circleMellinPoint a theta)| = Real.arctan (|theta| / a) := by
  rw [circleMellinPoint_arg ha theta, abs_neg]
  by_cases ht : 0 ≤ theta
  · have hat : 0 ≤ Real.arctan (theta / a) := by
      simpa only [Real.arctan_zero] using
        Real.arctan_le_arctan (div_nonneg ht ha.le)
    simp only [abs_of_nonneg ht, abs_of_nonneg hat]
  · have htneg : theta < 0 := lt_of_not_ge ht
    have hat : Real.arctan (theta / a) ≤ 0 := by
      simpa only [Real.arctan_zero] using
        Real.arctan_le_arctan (div_nonpos_of_nonpos_of_nonneg htneg.le ha.le)
    simp only [abs_of_neg htneg, abs_of_nonpos hat, neg_div, Real.arctan_neg]

/-- Exact sine/norm relation with the absolute signs paid in both cases. -/
theorem circleMellinPoint_sin_abs_arg {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Real.sin |Complex.arg (circleMellinPoint a theta)| =
      |theta| / ‖circleMellinPoint a theta‖ := by
  by_cases ht : 0 ≤ theta
  · have hat : 0 ≤ Real.arctan (theta / a) := by
      simpa only [Real.arctan_zero] using
        Real.arctan_le_arctan (div_nonneg ht ha.le)
    have harg : Complex.arg (circleMellinPoint a theta) ≤ 0 := by
      rw [circleMellinPoint_arg ha theta]
      linarith
    rw [abs_of_nonpos harg, Real.sin_neg, Complex.sin_arg, circleMellinPoint_im]
    simp only [neg_div, neg_neg, abs_of_nonneg ht, Complex.norm_eq_abs]
  · have htneg : theta < 0 := lt_of_not_ge ht
    have harg : 0 ≤ Complex.arg (circleMellinPoint a theta) :=
      Complex.arg_nonneg_iff.mpr (by rw [circleMellinPoint_im]; linarith)
    rw [abs_of_nonneg harg, Complex.sin_arg, circleMellinPoint_im]
    simp only [abs_of_neg htneg, Complex.norm_eq_abs]

/-- The actual rotation angle preserves the dependence of norm and phase. -/
theorem circleMellinPoint_rotation_cos_sq {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Real.cos (rotationAngle (circleMellinPoint a theta)) ^ 2 =
      (‖circleMellinPoint a theta‖ - |theta|) / (2 * ‖circleMellinPoint a theta‖) := by
  have hn := circleMellinPoint_norm_pos ha theta
  have he : 2 * rotationAngle (circleMellinPoint a theta) =
      |Complex.arg (circleMellinPoint a theta)| + Real.pi / 2 := by
    unfold rotationAngle
    ring
  have hd := Real.cos_two_mul (rotationAngle (circleMellinPoint a theta))
  rw [he, Real.cos_add_pi_div_two, circleMellinPoint_sin_abs_arg ha theta] at hd
  field_simp [hn.ne'] at hd
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hn.ne')).mpr
  nlinarith [hd]

/-- Linked geometry cancels the apparent extra singularity of a separate bound. -/
theorem kernelCoefficient_circle_eq_norm {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    kernelCoefficient (circleMellinPoint a theta) =
      2 / a ^ 2 * (1 + |theta| / ‖circleMellinPoint a theta‖) := by
  let r : ℝ := ‖circleMellinPoint a theta‖
  let c : ℝ := Real.cos (rotationAngle (circleMellinPoint a theta))
  have hr : 0 < r := circleMellinPoint_norm_pos ha theta
  have hright : 0 < (circleMellinPoint a theta).re := by
    simpa only [circleMellinPoint_re] using ha
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [rotationAngle_pos (circleMellinPoint a theta), Real.pi_pos],
      rotationAngle_lt_pi_half hright⟩
  have hrsq : r ^ 2 = a ^ 2 + theta ^ 2 := circleMellinPoint_norm_sq a theta
  have hcsq : c ^ 2 = (r - |theta|) / (2 * r) :=
    circleMellinPoint_rotation_cos_sq ha theta
  have hceq : c ^ 2 * (2 * r) = r - |theta| :=
    (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hr.ne')).mp hcsq
  have hproduct : (c ^ 2 * (2 * r)) * (r + |theta|) =
      (r - |theta|) * (r + |theta|) :=
    congrArg (fun x : ℝ => x * (r + |theta|)) hceq
  have hcore : 2 * r * c ^ 2 * (r + |theta|) = a ^ 2 := by
    nlinarith [hproduct, sq_abs theta, hrsq]
  have hscaled : (2 * r * c ^ 2 * (r + |theta|)) * r = a ^ 2 * r :=
    congrArg (fun x : ℝ => x * r) hcore
  change r ^ (-2 : ℝ) * (1 / c) ^ (2 : ℕ) = 2 / a ^ 2 * (1 + |theta| / r)
  rw [Real.rpow_neg hr.le 2, Real.rpow_two]
  field_simp [hr.ne', hc.ne', ha.ne'] <;> nlinarith [hcore, hscaled]

theorem kernelCoefficient_circle_eq_radius {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    kernelCoefficient (circleMellinPoint a theta) =
      2 / a ^ 2 * (1 + |theta| / Real.sqrt (a ^ 2 + theta ^ 2)) := by
  simpa only [circleMellinPoint_norm_eq_radius, circleMellinRadius] using
    kernelCoefficient_circle_eq_norm ha theta

theorem kernelCoefficient_circle_le_four {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    kernelCoefficient (circleMellinPoint a theta) ≤ 4 / a ^ 2 := by
  rw [kernelCoefficient_circle_eq_norm ha theta]
  have hn := circleMellinPoint_norm_pos ha theta
  have hratio : |theta| / ‖circleMellinPoint a theta‖ ≤ 1 :=
    (div_le_iff₀ hn).mpr (by simpa only [one_mul] using circleMellinPoint_abs_theta_le_norm a theta)
  calc
    _ ≤ (2 / a ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 4 / a ^ 2 := by ring

theorem circleDecayFloor_pos {a : ℝ} (ha : 0 < a) : 0 < circleDecayFloor a := by
  have ht : 0 < Real.arctan (a / Real.pi) := by
    simpa only [Real.arctan_zero] using Real.arctan_lt_arctan (div_pos ha Real.pi_pos)
  exact div_pos ht (by norm_num)

theorem decayGap_circle_eq {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    decayGap (circleMellinPoint a theta) =
      (Real.pi / 2 - Real.arctan (|theta| / a)) / 2 := by
  unfold decayGap rotationAngle
  rw [circleMellinPoint_abs_arg ha theta]
  ring

/-- A true positive uniform decay floor on the closed phase interval. -/
theorem decayGap_circle_ge_floor {a theta : ℝ} (ha : 0 < a)
    (htheta : |theta| ≤ Real.pi) :
    circleDecayFloor a ≤ decayGap (circleMellinPoint a theta) := by
  have hquot : |theta| / a ≤ Real.pi / a :=
    (div_le_div_iff_of_pos_right ha).mpr htheta
  have hmono := Real.arctan_le_arctan hquot
  have hinv : Real.arctan (a / Real.pi) = Real.pi / 2 - Real.arctan (Real.pi / a) := by
    simpa only [inv_div] using Real.arctan_inv_of_pos (div_pos Real.pi_pos ha)
  rw [decayGap_circle_eq ha theta]
  unfold circleDecayFloor
  rw [hinv]
  linarith

theorem circleMellinRadius_continuous :
    Continuous (fun p : ℝ × ℝ => circleMellinRadius p.1 p.2) := by
  unfold circleMellinRadius
  fun_prop

theorem circleDecayFloor_continuous : Continuous circleDecayFloor := by
  unfold circleDecayFloor
  exact (Real.continuous_arctan.comp (continuous_id.div_const Real.pi)).div_const 2

/-- Continuity of the linked closed coefficient, with both denominators paid. -/
theorem circleCoefficientClosed_continuousAt {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ =>
      2 / q.1 ^ 2 * (1 + |q.2| / circleMellinRadius q.1 q.2)) p := by
  have hnorm := circleMellinRadius_pos hp p.2
  unfold circleMellinRadius at hnorm ⊢
  fun_prop (disch := positivity)

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.circleMellinPoint
#print axioms GoldbachComplexGammaMellin22.circleMellinRadius
#print axioms GoldbachComplexGammaMellin22.circleDecayFloor
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_re
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_im
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_ne_zero
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_mem_slitPlane
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_norm_eq_radius
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_norm_sq
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_norm_pos
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_abs_theta_le_norm
#print axioms GoldbachComplexGammaMellin22.circleMellinRadius_pos
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_arg
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_abs_arg
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_sin_abs_arg
#print axioms GoldbachComplexGammaMellin22.circleMellinPoint_rotation_cos_sq
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient_circle_eq_norm
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient_circle_eq_radius
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient_circle_le_four
#print axioms GoldbachComplexGammaMellin22.circleDecayFloor_pos
#print axioms GoldbachComplexGammaMellin22.decayGap_circle_eq
#print axioms GoldbachComplexGammaMellin22.decayGap_circle_ge_floor
#print axioms GoldbachComplexGammaMellin22.circleMellinRadius_continuous
#print axioms GoldbachComplexGammaMellin22.circleDecayFloor_continuous
#print axioms GoldbachComplexGammaMellin22.circleCoefficientClosed_continuousAt
