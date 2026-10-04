import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/- Source revision02 after the conserved attempt1 and attempt2 compiler failures. This revision
   has not been compiled. The mathematical statement and hypotheses are unchanged.
   This source derives complex Laplace and the rotation bound for genuine Gamma.
   It does not assert the Weil formula, a zero count, or a bound for D_N. -/

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology

namespace GoldbachContinuous22

/-- The real Gamma factor used after rotation is uniformly at most one. -/
theorem realGamma_le_one_on_unit_strip {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    Real.Gamma (beta + 1) ≤ 1 := by
  have hconv := Real.convexOn_Gamma.2
    (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (by norm_num : (2 : ℝ) ∈ Ioi 0)
    (by linarith : 0 ≤ 1 - beta) hbeta0
    (by ring : (1 - beta) + beta = 1)
  have hid : (1 - beta) • (1 : ℝ) + beta • (2 : ℝ) = beta + 1 := by
    simp only [smul_eq_mul]
    ring
  rw [hid] at hconv
  simpa only [Real.Gamma_one, Real.Gamma_two, smul_eq_mul,
    mul_one, sub_add_cancel] using hconv

/-- Integrability at an arbitrary positive real Laplace rate, rather than rate one. -/
theorem real_laplace_integrable {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-(r * t)) * t ^ (a - 1)) (Ioi 0) := by
  have hcomp : IntegrableOn
      (fun t : ℝ => Real.exp (-(r * t)) * (r * t) ^ (a - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) 0 hr).mpr
    simpa using Real.GammaIntegral_convergent ha
  have hscale := hcomp.const_mul ((r ^ (a - 1))⁻¹)
  apply hscale.congr
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  have hrpow : r ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  rw [Real.mul_rpow hr.le ht.le]
  field_simp [hrpow]
  ring

/-- The actual complex Laplace integrand, with the principal power at positive t. -/
def laplaceIntegrand (z s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z * (t : ℂ)) * (t : ℂ) ^ (s - 1)

/-- Exact norm reduction; no decay in Im(s) is claimed by this lemma. -/
theorem norm_laplaceIntegrand {z s : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖laplaceIntegrand z s t‖ =
      Real.exp (-(z.re * t)) * t ^ (s.re - 1) := by
  rw [laplaceIntegrand, norm_mul, Complex.norm_eq_abs,
    Complex.abs_exp, Complex.norm_eq_abs,
    Complex.abs_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.sub_re, Complex.one_re, neg_mul]

/-- Measurability is proved from continuity on the positive ray. -/
theorem laplaceIntegrand_aestronglyMeasurable (z s : ℂ) :
    AEStronglyMeasurable (laplaceIntegrand z s) (volume.restrict (Ioi 0)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply continuousOn_of_forall_continuousAt
  intro t ht
  unfold laplaceIntegrand
  have hpow : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (s - 1)) t :=
    (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr ht)).comp
      Complex.continuous_ofReal.continuousAt
  exact ((continuous_const.mul Complex.continuous_ofReal).cexp.continuousAt).mul hpow

/-- Absolute convergence for a genuine complex rate in the right half-plane. -/
theorem complex_laplace_integrable {z s : ℂ} (hz : 0 < z.re) (hs : 0 < s.re) :
    IntegrableOn (laplaceIntegrand z s) (Ioi 0) := by
  rw [IntegrableOn, ← integrable_norm_iff (laplaceIntegrand_aestronglyMeasurable z s)]
  apply (real_laplace_integrable hs hz).congr
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  exact (norm_laplaceIntegrand ht).symm

/-- The existing cache formula, explicitly restricted to a real positive rate. -/
theorem real_rate_laplace_identity {s : ℂ} {r : ℝ}
    (hs : 0 < s.re) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(r * t : ℂ))) =
      (1 / (r : ℂ)) ^ s * Complex.Gamma s := by
  exact Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr

def laplaceTransform (s z : ℂ) : ℂ := ∫ t : ℝ in Ioi 0, laplaceIntegrand z s t

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

theorem hasDerivAt_laplaceIntegrand (z s : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => laplaceIntegrand w s t)
      (-(t : ℂ) * laplaceIntegrand z s t) z := by
  have hd := (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp).mul_const
    ((t : ℂ) ^ (s - 1))
  convert hd using 1 <;> dsimp [laplaceIntegrand] <;> ring

/-- The derivative has a fixed integrable bound on a ball of radius Re(z)/2. -/
theorem laplace_derivative_local_bound {z w s : ℂ} {t : ℝ}
    (hz : 0 < z.re) (hw : w ∈ ball z (z.re / 2)) (ht : 0 < t) :
    ‖-(t : ℂ) * laplaceIntegrand w s t‖ ≤
      Real.exp (-(z.re / 2 * t)) * t ^ s.re := by
  have habs : |w.re - z.re| < z.re / 2 := by
    have hnorm : ‖w - z‖ < z.re / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hw
    have h := (Complex.abs_re_le_abs (w - z)).trans_lt hnorm
    simpa only [Complex.sub_re, Complex.norm_eq_abs] using h
  have hrate : z.re / 2 ≤ w.re := by
    have h := (abs_lt.mp habs).1
    linarith
  have hexp : Real.exp (-(w.re * t)) ≤ Real.exp (-(z.re / 2 * t)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    norm_laplaceIntegrand ht]
  have hid : t * (Real.exp (-(w.re * t)) * t ^ (s.re - 1)) =
      Real.exp (-(w.re * t)) * t ^ s.re := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    field_simp [ht.ne']
  rw [hid]
  exact mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg ht.le _)

/-- Complex differentiation under the integral with a constructed local dominateur. -/
theorem hasDerivAt_laplaceTransform {z s : ℂ} (hz : 0 < z.re) (hs : 0 < s.re) :
    HasDerivAt (laplaceTransform s)
      (∫ t : ℝ in Ioi 0, -(t : ℂ) * laplaceIntegrand z s t) z := by
  let bound : ℝ → ℝ := fun t => Real.exp (-(z.re / 2 * t)) * t ^ s.re
  have hbint : Integrable bound (volume.restrict (Ioi 0)) := by
    simpa only [bound, add_sub_cancel_right] using
      real_laplace_integrable (show 0 < s.re + 1 by linarith)
        (show 0 < z.re / 2 by positivity)
  have hmeas : ∀ᶠ w : ℂ in 𝓝 z,
      AEStronglyMeasurable (fun t => laplaceIntegrand w s t)
        (volume.restrict (Ioi 0)) :=
    Eventually.of_forall (fun w => laplaceIntegrand_aestronglyMeasurable w s)
  have hdmeas : AEStronglyMeasurable
      (fun t : ℝ => -(t : ℂ) * laplaceIntegrand z s t)
      (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.neg.aestronglyMeasurable).mul
      (laplaceIntegrand_aestronglyMeasurable z s)
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ w ∈ ball z (z.re / 2),
        ‖-(t : ℂ) * laplaceIntegrand w s t‖ ≤ bound t := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with t ht
    intro w hw
    exact laplace_derivative_local_bound hz hw ht
  have hdiff : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ w ∈ ball z (z.re / 2),
        HasDerivAt (fun v : ℂ => laplaceIntegrand v s t)
          (-(t : ℂ) * laplaceIntegrand w s t) w := by
    filter_upwards with t
    intro w _
    exact hasDerivAt_laplaceIntegrand w s t
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (show 0 < z.re / 2 by positivity) hmeas (complex_laplace_integrable hz hs)
    hdmeas hbound hbint hdiff).2

theorem rightHalfPlane_isOpen : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem rightHalfPlane_isPreconnected : IsPreconnected rightHalfPlane := by
  have hc : Convex ℝ rightHalfPlane := by
    simpa only [rightHalfPlane] using (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  exact hc.isPreconnected

theorem laplaceTransform_analytic {s : ℂ} (hs : 0 < s.re) :
    AnalyticOnNhd ℂ (laplaceTransform s) rightHalfPlane := by
  apply DifferentiableOn.analyticOnNhd _ rightHalfPlane_isOpen
  intro z hz
  exact (hasDerivAt_laplaceTransform hz hs).differentiableAt.differentiableWithinAt

theorem laplace_rhs_analytic (s : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => z ^ (-s) * Complex.Gamma s) rightHalfPlane := by
  apply DifferentiableOn.analyticOnNhd _ rightHalfPlane_isOpen
  intro z hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  exact (((hasDerivAt_id z).cpow_const hslit).mul_const
    (Complex.Gamma s)).differentiableAt.differentiableWithinAt

theorem laplaceTransform_real_rate {s : ℂ} {r : ℝ} (hs : 0 < s.re) (hr : 0 < r) :
    laplaceTransform s (r : ℂ) = (r : ℂ) ^ (-s) * Complex.Gamma s := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(r * t : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change Complex.exp (-(r : ℂ) * (t : ℂ)) * (t : ℂ) ^ (s - 1) =
        (t : ℂ) ^ (s - 1) * Complex.exp (-(r * t : ℂ))
      rw [neg_mul]
      exact mul_comm _ _
    _ = (1 / (r : ℂ)) ^ s * Complex.Gamma s := real_rate_laplace_identity hs hr
    _ = (r : ℂ) ^ (-s) * Complex.Gamma s := by
      rw [one_div, Complex.inv_cpow, ← Complex.cpow_neg]
      simp only [Complex.arg_ofReal_of_nonneg hr.le]
      exact Real.pi_ne_zero.symm

/-- The complex-rate Laplace identity is derived by analytic continuation from
    positive real rates; it is not an assumption supplied to a final theorem. -/
theorem complex_rate_laplace_identity {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    laplaceTransform s z = z ^ (-s) * Complex.Gamma s := by
  let rates : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hrates : Tendsto rates atTop (𝓝 1) := by
    simpa only [rates, add_zero] using
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomplex : Tendsto (fun n : ℕ => (rates n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using Complex.continuous_ofReal.tendsto 1 |>.comp hrates
  have hclosure : (1 : ℂ) ∈ closure
      ({w : ℂ | laplaceTransform s w = w ^ (-s) * Complex.Gamma s} \ {(1 : ℂ)}) := by
    apply mem_closure_of_tendsto hcomplex
    apply Eventually.of_forall
    intro n
    have hpos : 0 < rates n := by dsimp [rates]; positivity
    have hgt : 1 < rates n := by
      dsimp [rates]
      exact lt_add_of_pos_right 1 (by positivity)
    constructor
    · exact laplaceTransform_real_rate hs hpos
    · simp only [mem_singleton_iff, Complex.ofReal_eq_one]
      exact ne_of_gt hgt
  exact (laplaceTransform_analytic hs).eqOn_of_preconnected_of_mem_closure
    (laplace_rhs_analytic s) rightHalfPlane_isPreconnected
    (by simp [rightHalfPlane]) hclosure hz

/-- Absolute integration gives this exact rate-dependent majorant. -/
theorem norm_laplaceTransform_le {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ‖laplaceTransform s z‖ ≤ (1 / z.re) ^ s.re * Real.Gamma s.re := by
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖laplaceIntegrand z s t‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * Real.exp (-(z.re * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [norm_laplaceIntegrand ht, mul_comm]
    _ = (1 / z.re) ^ s.re * Real.Gamma s.re :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs hz

theorem norm_rotation_power {s : ℂ} {theta : ℝ}
    (htheta0 : -(Real.pi / 2) < theta) (htheta1 : theta < Real.pi / 2) :
    ‖(Complex.exp ((theta : ℂ) * Complex.I)) ^ s‖ = Real.exp (-theta * s.im) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · rw [Complex.norm_eq_abs, Complex.abs_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, zero_sub, mul_one, add_zero, neg_mul]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    linarith [Real.pi_pos]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    linarith [Real.pi_pos]

/-- The rotation bound is obtained from the proved complex-rate identity. -/
theorem Gamma_rotation_bound {s : ℂ} {theta : ℝ} (hs : 0 < s.re)
    (htheta0 : -(Real.pi / 2) < theta) (htheta1 : theta < Real.pi / 2) :
    ‖Complex.Gamma s‖ ≤ Real.exp (-theta * s.im) *
      ((1 / Real.cos theta) ^ s.re * Real.Gamma s.re) := by
  let z : ℂ := Complex.exp ((theta : ℂ) * Complex.I)
  have hzr : z.re = Real.cos theta := by simp [z, Complex.exp_re]
  have hcos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo ⟨htheta0, htheta1⟩
  have hz : 0 < z.re := hzr.symm ▸ hcos
  have hnz : z ≠ 0 := Complex.exp_ne_zero _
  have hid : z ^ s * z ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hnz, add_neg_cancel, Complex.cpow_zero]
  have hGamma : Complex.Gamma s = z ^ s * laplaceTransform s z := by
    rw [complex_rate_laplace_identity hs hz, ← mul_assoc, hid, one_mul]
  rw [hGamma, norm_mul]
  have hnorm : ‖z ^ s‖ = Real.exp (-theta * s.im) :=
    norm_rotation_power htheta0 htheta1
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [hzr] using norm_laplaceTransform_le hs hz

theorem quarter_angle_coefficient_le_two {sigma : ℝ} (hsigma : sigma ≤ 2) :
    (1 / Real.cos (Real.pi / 4)) ^ sigma ≤ 2 := by
  have hc : 0 < Real.cos (Real.pi / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hb : 1 ≤ 1 / Real.cos (Real.pi / 4) := by
    apply (le_div_iff₀ hc).mpr
    simpa only [one_mul] using Real.cos_le_one (Real.pi / 4)
  have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have htwo : (1 / Real.cos (Real.pi / 4)) ^ (2 : ℝ) = 2 := by
    rw [Real.rpow_two, Real.cos_pi_div_four]
    field_simp [hsqrt0]
  exact (Real.rpow_le_rpow_of_exponent_le hb hsigma).trans_eq htwo

/-- H2 for the actual Gamma function, stated on the entire closed strip [1,2]. -/
theorem Gamma_strip_exponential_bound {s : ℂ} (hs0 : 1 ≤ s.re) (hs1 : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 2 * Real.exp (-(Real.pi / 4) * |s.im|) := by
  have positive_case : ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 2 → 0 ≤ u.im →
      ‖Complex.Gamma u‖ ≤ 2 * Real.exp (-(Real.pi / 4) * u.im) := by
    intro u hu0 hu1 _
    have hrot := Gamma_rotation_bound (show 0 < u.re by linarith)
      (show -(Real.pi / 2) < Real.pi / 4 by linarith [Real.pi_pos])
      (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])
    have hreal : Real.Gamma u.re ≤ 1 := by
      convert realGamma_le_one_on_unit_strip
        (show 0 ≤ u.re - 1 by linarith) (show u.re - 1 ≤ 1 by linarith) using 1
      congr 1
      ring
    have hcos : 0 < Real.cos (Real.pi / 4) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hcoef : (1 / Real.cos (Real.pi / 4)) ^ u.re * Real.Gamma u.re ≤ 2 := by
      calc
        _ ≤ (1 / Real.cos (Real.pi / 4)) ^ u.re * 1 :=
          mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg (by positivity) _)
        _ ≤ 2 := by simpa only [mul_one] using quarter_angle_coefficient_le_two hu1
    calc
      _ ≤ Real.exp (-(Real.pi / 4) * u.im) *
          ((1 / Real.cos (Real.pi / 4)) ^ u.re * Real.Gamma u.re) := hrot
      _ ≤ Real.exp (-(Real.pi / 4) * u.im) * 2 :=
        mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le
      _ = 2 * Real.exp (-(Real.pi / 4) * u.im) := mul_comm _ _
  by_cases him : 0 ≤ s.im
  · simpa only [abs_of_nonneg him] using positive_case s hs0 hs1 him
  · have hsneg : s.im < 0 := lt_of_not_ge him
    have hc := positive_case (starRingEnd ℂ s)
      (by simpa using hs0) (by simpa using hs1)
      (by simpa only [Complex.conj_im] using (neg_nonneg.mpr hsneg.le))
    simpa only [Complex.Gamma_conj, RCLike.norm_conj, Complex.conj_im,
      abs_of_neg (lt_of_not_ge him), neg_mul, mul_neg] using hc

end GoldbachContinuous22

#print axioms GoldbachContinuous22.realGamma_le_one_on_unit_strip
#print axioms GoldbachContinuous22.real_laplace_integrable
#print axioms GoldbachContinuous22.laplaceIntegrand
#print axioms GoldbachContinuous22.norm_laplaceIntegrand
#print axioms GoldbachContinuous22.laplaceIntegrand_aestronglyMeasurable
#print axioms GoldbachContinuous22.complex_laplace_integrable
#print axioms GoldbachContinuous22.real_rate_laplace_identity
#print axioms GoldbachContinuous22.laplaceTransform
#print axioms GoldbachContinuous22.rightHalfPlane
#print axioms GoldbachContinuous22.hasDerivAt_laplaceIntegrand
#print axioms GoldbachContinuous22.laplace_derivative_local_bound
#print axioms GoldbachContinuous22.hasDerivAt_laplaceTransform
#print axioms GoldbachContinuous22.rightHalfPlane_isOpen
#print axioms GoldbachContinuous22.rightHalfPlane_isPreconnected
#print axioms GoldbachContinuous22.laplaceTransform_analytic
#print axioms GoldbachContinuous22.laplace_rhs_analytic
#print axioms GoldbachContinuous22.laplaceTransform_real_rate
#print axioms GoldbachContinuous22.complex_rate_laplace_identity
#print axioms GoldbachContinuous22.norm_laplaceTransform_le
#print axioms GoldbachContinuous22.norm_rotation_power
#print axioms GoldbachContinuous22.Gamma_rotation_bound
#print axioms GoldbachContinuous22.quarter_angle_coefficient_le_two
#print axioms GoldbachContinuous22.Gamma_strip_exponential_bound
