import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! SOURCE ONLY. The half-line Gamma decay is derived from genuine reflection
and conjugation, and then transported through the principal complex power.
No strengthened Gamma bound, zeta representation or final trace identity is
assumed. The phase gap is positive, but may tend to zero near the branch edge.
No compiler or numerical calculation has been invoked for this module. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace GoldbachContinuous22

def phaseHalf (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

def phaseFiveHalf (t : ℝ) : ℂ := (5 / 2 : ℂ) + (t : ℂ) * Complex.I

def phaseGammaConstant : ℝ := Real.sqrt (2 * Real.pi)

def phaseW (a theta : ℝ) : ℂ := (a : ℂ) - (theta : ℂ) * Complex.I

def phaseGap (a theta : ℝ) : ℝ := Real.pi / 2 - |Complex.arg (phaseW a theta)|

def phaseGammaLeft (a theta t : ℝ) : ℂ :=
  phaseW a theta ^ (-((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma (phaseHalf t)

def phaseGammaRight (a theta t : ℝ) : ℂ :=
  phaseW a theta ^ (-((3 / 2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma (phaseFiveHalf t)

def phaseGammaLeftEnvelope (a theta t : ℝ) : ℝ :=
  ‖phaseW a theta‖ ^ (1 / 2 : ℝ) * phaseGammaConstant *
    Real.exp (-phaseGap a theta * |t|)

def phaseGammaRightEnvelope (a theta t : ℝ) : ℝ :=
  ‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * phaseGammaConstant * (|t| + 2) ^ 2 *
    Real.exp (-phaseGap a theta * |t|)

theorem one_sub_phaseHalf_eq_conj (t : ℝ) : 1 - phaseHalf t = conj (phaseHalf t) := by
  apply Complex.ext <;> simp [phaseHalf] <;> ring

theorem sin_pi_mul_phaseHalf (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * phaseHalf t) = (Real.cosh (Real.pi * t) : ℂ) := by
  have he : (Real.pi : ℂ) * phaseHalf t =
      ((Real.pi * t : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) / 2 := by
    unfold phaseHalf
    push_cast
    ring
  rw [he, Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- The exact reflection identity on the true half-line. -/
theorem norm_Gamma_phaseHalf_sq (t : ℝ) :
    ‖Complex.Gamma (phaseHalf t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (phaseHalf t)
  rw [one_sub_phaseHalf_eq_conj, Complex.Gamma_conj, Complex.mul_conj',
    sin_pi_mul_phaseHalf, ← Complex.ofReal_div] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_pow] using h

theorem exp_abs_le_two_cosh (u : ℝ) : Real.exp |u| ≤ 2 * Real.cosh u := by
  rw [← Real.cosh_abs u, Real.cosh_eq]
  have he := (Real.exp_pos (-|u|)).le
  linarith

/-- Genuine pi/2 decay, proved by squaring with a positive real envelope. -/
theorem norm_Gamma_phaseHalf_le (t : ℝ) :
    ‖Complex.Gamma (phaseHalf t)‖ ≤
      phaseGammaConstant * Real.exp (-Real.pi * |t| / 2) := by
  have hc := Real.cosh_pos (Real.pi * t)
  have hsq := norm_Gamma_phaseHalf_sq t
  have he : Real.exp (Real.pi * |t|) ≤ 2 * Real.cosh (Real.pi * t) := by
    simpa only [abs_mul, abs_of_pos Real.pi_pos] using exp_abs_le_two_cosh (Real.pi * t)
  have hp : ‖Complex.Gamma (phaseHalf t)‖ ^ 2 * Real.cosh (Real.pi * t) = Real.pi :=
    (eq_div_iff hc.ne').mp hsq
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg ‖Complex.Gamma (phaseHalf t)‖)
  have hle : ‖Complex.Gamma (phaseHalf t)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [hp]
  have hsqrt : phaseGammaConstant ^ 2 = 2 * Real.pi := by
    exact Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-Real.pi * |t| / 2) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hbound : ‖Complex.Gamma (phaseHalf t)‖ ^ 2 ≤
      (phaseGammaConstant * Real.exp (-Real.pi * |t| / 2)) ^ 2 := by
    rw [mul_pow, hsqrt, hexp]
    exact hle
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).mp hbound

theorem Gamma_phaseFiveHalf_recurrence (t : ℝ) :
    Complex.Gamma (phaseFiveHalf t) =
      (phaseHalf t + 1) * (phaseHalf t * Complex.Gamma (phaseHalf t)) := by
  have h0 : phaseHalf t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [phaseHalf] at hr
  have h1 : phaseHalf t + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [phaseHalf] at hr
  have he : phaseFiveHalf t = (phaseHalf t + 1) + 1 := by
    unfold phaseFiveHalf phaseHalf
    ring
  rw [he, Complex.Gamma_add_one _ h1, Complex.Gamma_add_one _ h0]

theorem norm_real_add_imag_le (c t : ℝ) (hc : 0 ≤ c) :
    ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ≤ c + |t| := by
  calc
    _ ≤ ‖(c : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem norm_Gamma_phaseFiveHalf_le (t : ℝ) :
    ‖Complex.Gamma (phaseFiveHalf t)‖ ≤
      phaseGammaConstant * (|t| + 2) ^ 2 * Real.exp (-Real.pi * |t| / 2) := by
  have h0 : ‖phaseHalf t‖ ≤ |t| + 2 := by
    have h := norm_real_add_imag_le (1 / 2 : ℝ) t (by norm_num)
    have he : phaseHalf t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      unfold phaseHalf
      norm_cast
    rw [← he] at h
    linarith
  have h1 : ‖phaseHalf t + 1‖ ≤ |t| + 2 := by
    have h := norm_real_add_imag_le (3 / 2 : ℝ) t (by norm_num)
    have he : phaseHalf t + 1 = ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      unfold phaseHalf
      push_cast
      ring
    rw [← he] at h
    linarith
  have hC : 0 ≤ phaseGammaConstant * Real.exp (-Real.pi * |t| / 2) := by
    unfold phaseGammaConstant
    positivity
  rw [Gamma_phaseFiveHalf_recurrence, norm_mul, norm_mul]
  calc
    _ ≤ (|t| + 2) * ((|t| + 2) *
        (phaseGammaConstant * Real.exp (-Real.pi * |t| / 2))) := by
      exact mul_le_mul h1
        (mul_le_mul h0 (norm_Gamma_phaseHalf_le t) (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

theorem phaseW_re (a theta : ℝ) : (phaseW a theta).re = a := by simp [phaseW]

theorem phaseW_ne_zero {a : ℝ} (ha : 0 < a) (theta : ℝ) : phaseW a theta ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  rw [phaseW_re, Complex.zero_re] at hr
  exact ha.ne' hr

theorem phaseGap_pos {a : ℝ} (ha : 0 < a) (theta : ℝ) : 0 < phaseGap a theta := by
  unfold phaseGap
  apply sub_pos.mpr
  exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa only [phaseW_re] using ha))

/-- The principal branch contribution is exposed exactly, not bounded away. -/
theorem norm_principal_cpow_vertical {w : ℂ} (hw : w ≠ 0) (c t : ℝ) :
    ‖w ^ (-((c : ℂ) + (t : ℂ) * Complex.I))‖ =
      ‖w‖ ^ (-c) * Real.exp (t * Complex.arg w) := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_of_ne_zero hw]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
    Complex.neg_im, Complex.add_im, Complex.mul_im, zero_mul, add_zero, mul_one]
  rw [mul_neg, Real.exp_neg, div_inv_eq_mul]
  rw [mul_comm (Complex.arg w) t] <;> rfl

theorem phase_exponent_le_gap (a theta t : ℝ) :
    -Real.pi * |t| / 2 + t * Complex.arg (phaseW a theta) ≤ -phaseGap a theta * |t| := by
  have ht := le_abs_self (t * Complex.arg (phaseW a theta))
  rw [abs_mul] at ht
  unfold phaseGap
  nlinarith

theorem norm_phaseGammaLeft_le {a : ℝ} (ha : 0 < a) (theta t : ℝ) :
    ‖phaseGammaLeft a theta t‖ ≤ phaseGammaLeftEnvelope a theta t := by
  unfold phaseGammaLeft phaseGammaLeftEnvelope
  rw [norm_mul, norm_principal_cpow_vertical (phaseW_ne_zero ha theta)]
  have hg := norm_Gamma_phaseHalf_le t
  have hpow := Real.rpow_nonneg (norm_nonneg (phaseW a theta)) (1 / 2 : ℝ)
  calc
    _ ≤ ‖phaseW a theta‖ ^ (1 / 2 : ℝ) * Real.exp (t * Complex.arg (phaseW a theta)) *
        (phaseGammaConstant * Real.exp (-Real.pi * |t| / 2)) := by
      norm_num only [neg_neg] at *
      exact mul_le_mul_of_nonneg_left hg (mul_nonneg hpow (Real.exp_pos _).le)
    _ = ‖phaseW a theta‖ ^ (1 / 2 : ℝ) * phaseGammaConstant *
        Real.exp (-Real.pi * |t| / 2 + t * Complex.arg (phaseW a theta)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (phase_exponent_le_gap a theta t))
      (mul_nonneg hpow (Real.sqrt_nonneg _))

theorem norm_phaseGammaRight_le {a : ℝ} (ha : 0 < a) (theta t : ℝ) :
    ‖phaseGammaRight a theta t‖ ≤ phaseGammaRightEnvelope a theta t := by
  unfold phaseGammaRight phaseGammaRightEnvelope
  rw [norm_mul, norm_principal_cpow_vertical (phaseW_ne_zero ha theta)]
  have hg := norm_Gamma_phaseFiveHalf_le t
  have hpow := Real.rpow_nonneg (norm_nonneg (phaseW a theta)) (-3 / 2 : ℝ)
  calc
    _ ≤ ‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * Real.exp (t * Complex.arg (phaseW a theta)) *
        (phaseGammaConstant * (|t| + 2) ^ 2 * Real.exp (-Real.pi * |t| / 2)) := by
      norm_num only [neg_div] at *
      exact mul_le_mul_of_nonneg_left hg (mul_nonneg hpow (Real.exp_pos _).le)
    _ = ‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * phaseGammaConstant * (|t| + 2) ^ 2 *
        Real.exp (-Real.pi * |t| / 2 + t * Complex.arg (phaseW a theta)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (phase_exponent_le_gap a theta t))
      (mul_nonneg (mul_nonneg hpow (Real.sqrt_nonneg _)) (sq_nonneg _))

theorem phaseGap_continuousAt {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => phaseGap q.1 q.2) p := by
  have hw : Continuous (fun q : ℝ × ℝ => phaseW q.1 q.2) := by
    unfold phaseW
    fun_prop
  have hslit : phaseW p.1 p.2 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa only [phaseW_re] using hp))
  have harg := (Complex.continuousAt_arg hslit).comp hw.continuousAt
  exact continuousAt_const.sub harg.abs

theorem phaseGap_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => phaseGap p.1 p.2) {p | 0 < p.1} :=
  fun p hp => (phaseGap_continuousAt hp).continuousWithinAt

end GoldbachContinuous22

#print axioms GoldbachContinuous22.phaseHalf
#print axioms GoldbachContinuous22.phaseFiveHalf
#print axioms GoldbachContinuous22.phaseGammaConstant
#print axioms GoldbachContinuous22.phaseW
#print axioms GoldbachContinuous22.phaseGap
#print axioms GoldbachContinuous22.phaseGammaLeft
#print axioms GoldbachContinuous22.phaseGammaRight
#print axioms GoldbachContinuous22.phaseGammaLeftEnvelope
#print axioms GoldbachContinuous22.phaseGammaRightEnvelope
#print axioms GoldbachContinuous22.one_sub_phaseHalf_eq_conj
#print axioms GoldbachContinuous22.sin_pi_mul_phaseHalf
#print axioms GoldbachContinuous22.norm_Gamma_phaseHalf_sq
#print axioms GoldbachContinuous22.exp_abs_le_two_cosh
#print axioms GoldbachContinuous22.norm_Gamma_phaseHalf_le
#print axioms GoldbachContinuous22.Gamma_phaseFiveHalf_recurrence
#print axioms GoldbachContinuous22.norm_real_add_imag_le
#print axioms GoldbachContinuous22.norm_Gamma_phaseFiveHalf_le
#print axioms GoldbachContinuous22.phaseW_re
#print axioms GoldbachContinuous22.phaseW_ne_zero
#print axioms GoldbachContinuous22.phaseGap_pos
#print axioms GoldbachContinuous22.norm_principal_cpow_vertical
#print axioms GoldbachContinuous22.phase_exponent_le_gap
#print axioms GoldbachContinuous22.norm_phaseGammaLeft_le
#print axioms GoldbachContinuous22.norm_phaseGammaRight_le
#print axioms GoldbachContinuous22.phaseGap_continuousAt
#print axioms GoldbachContinuous22.phaseGap_continuousOn




