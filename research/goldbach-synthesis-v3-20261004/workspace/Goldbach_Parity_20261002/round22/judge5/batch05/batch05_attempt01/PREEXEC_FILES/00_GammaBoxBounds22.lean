import GammaDerivative22
import Mathlib.Analysis.Calculus.MeanValue

/- SOURCE_ONLY. Genuine weighted Gamma term and its box transport. The box
   membership hypotheses are geometric data, not a zero existence/completeness
   certificate. No numerical evaluation of a Gamma centre is imported. -/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace GoldbachContinuous22

def weightedGammaTerm (Y : ℝ) (rho : ℂ) : ℂ :=
  Complex.exp ((Real.log Y : ℂ) * rho) * Complex.Gamma (rho + 1)

def spectralBoxDomain (gammaLo : ℝ) : Set ℂ :=
  Complex.re ⁻¹' Icc 0 1 ∩ Complex.im ⁻¹' Ici gammaLo

def gammaBoxRadius (Y gammaLo deltaBeta deltaGamma : ℝ) : ℝ :=
  Y * Real.exp (-(Real.pi / 4) * gammaLo) * (19 + 2 * Real.log Y) *
    (deltaBeta + deltaGamma)

theorem weightedGammaTerm_eq_cpow {Y : ℝ} (hY : 0 < Y) (rho : ℂ) :
    weightedGammaTerm Y rho = (Y : ℂ) ^ rho * Complex.Gamma (rho + 1) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'),
    ← Complex.ofReal_log hY.le]
  rfl

theorem spectralBoxDomain_convex (gammaLo : ℝ) : Convex ℝ (spectralBoxDomain gammaLo) := by
  exact ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.reLm).inter
    ((convex_Ici gammaLo).linear_preimage Complex.imLm)

theorem norm_weightedGamma_exponential_le {Y : ℝ} {rho : ℂ}
    (hY : 1 ≤ Y) (hrho : rho.re ≤ 1) :
    ‖Complex.exp ((Real.log Y : ℂ) * rho)‖ ≤ Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
  calc
    ‖Complex.exp ((Real.log Y : ℂ) * rho)‖ = Real.exp (Real.log Y * rho.re) := by
      rw [Complex.norm_eq_abs, Complex.abs_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    _ ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Y := Real.exp_log hY0

theorem hasDerivAt_weightedGammaTerm (Y : ℝ) {rho : ℂ} (hrho0 : 0 ≤ rho.re) :
    HasDerivAt (weightedGammaTerm Y)
      (Complex.exp ((Real.log Y : ℂ) * rho) *
        ((Real.log Y : ℂ) * Complex.Gamma (rho + 1) + deriv Complex.Gamma (rho + 1))) rho := by
  have hmem : rho + 1 ∈ rightHalfPlane := by
    change 0 < (rho + 1).re
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hg : DifferentiableAt ℂ Complex.Gamma (rho + 1) :=
    Gamma_differentiableOn_rightHalfPlane.differentiableAt
      (rightHalfPlane_isOpen.mem_nhds hmem)
  have hgamma := hg.hasDerivAt.comp rho ((hasDerivAt_id rho).add_const 1)
  have hexp := ((hasDerivAt_id rho).const_mul (Real.log Y : ℂ)).cexp
  convert hexp.mul hgamma using 1 <;> dsimp [weightedGammaTerm] <;> ring

/-- Actual derivative bound on every point of the geometric strip and height domain. -/
theorem norm_deriv_weightedGammaTerm_le {Y gammaLo : ℝ} {rho : ℂ}
    (hY : 1 ≤ Y) (hgammaLo : 0 ≤ gammaLo)
    (hrho : rho ∈ spectralBoxDomain gammaLo) :
    ‖deriv (weightedGammaTerm Y) rho‖ ≤
      Y * Real.exp (-(Real.pi / 4) * gammaLo) * (19 + 2 * Real.log Y) := by
  have hr0 : 0 ≤ rho.re := hrho.1.1
  have hr1 : rho.re ≤ 1 := hrho.1.2
  have hri : gammaLo ≤ rho.im := hrho.2
  have him0 : 0 ≤ rho.im := hgammaLo.trans hri
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hs0 : 1 ≤ (rho + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hs1 : (rho + 1).re ≤ 2 := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hGamma : ‖Complex.Gamma (rho + 1)‖ ≤
      2 * Real.exp (-(Real.pi / 4) * |rho.im|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using
      Gamma_strip_exponential_bound hs0 hs1
  have hGammaPrime : ‖deriv Complex.Gamma (rho + 1)‖ ≤
      19 * Real.exp (-(Real.pi / 4) * |rho.im|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using
      Gamma_derivative_strip_exponential_bound hs0 hs1
  have hexp : Real.exp (-(Real.pi / 4) * |rho.im|) ≤
      Real.exp (-(Real.pi / 4) * gammaLo) := by
    rw [abs_of_nonneg him0]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  rw [(hasDerivAt_weightedGammaTerm Y hr0).deriv, norm_mul]
  calc
    _ ≤ ‖Complex.exp ((Real.log Y : ℂ) * rho)‖ *
        (‖(Real.log Y : ℂ) * Complex.Gamma (rho + 1)‖ + ‖deriv Complex.Gamma (rho + 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖Complex.exp ((Real.log Y : ℂ) * rho)‖ *
        (Real.log Y * ‖Complex.Gamma (rho + 1)‖ + ‖deriv Complex.Gamma (rho + 1)‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ Y * (Real.log Y * (2 * Real.exp (-(Real.pi / 4) * |rho.im|)) +
        19 * Real.exp (-(Real.pi / 4) * |rho.im|)) :=
      mul_le_mul (norm_weightedGamma_exponential_le hY hr1)
        (add_le_add (mul_le_mul_of_nonneg_left hGamma hlog) hGammaPrime)
        (add_nonneg (mul_nonneg hlog (norm_nonneg _)) (norm_nonneg _)) hY0
    _ = Y * Real.exp (-(Real.pi / 4) * |rho.im|) * (19 + 2 * Real.log Y) := by ring
    _ ≤ Y * Real.exp (-(Real.pi / 4) * gammaLo) * (19 + 2 * Real.log Y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hY0) (by positivity)

theorem weightedGammaTerm_lipschitz_on_boxDomain {Y gammaLo : ℝ} {rho0 rho : ℂ}
    (hY : 1 ≤ Y) (hgammaLo : 0 ≤ gammaLo)
    (hrho0 : rho0 ∈ spectralBoxDomain gammaLo) (hrho : rho ∈ spectralBoxDomain gammaLo) :
    ‖weightedGammaTerm Y rho - weightedGammaTerm Y rho0‖ ≤
      (Y * Real.exp (-(Real.pi / 4) * gammaLo) * (19 + 2 * Real.log Y)) * ‖rho - rho0‖ := by
  apply (spectralBoxDomain_convex gammaLo).norm_image_sub_le_of_norm_deriv_le
      _ _ hrho0 hrho
  · intro z hz
    exact (hasDerivAt_weightedGammaTerm Y hz.1.1).differentiableAt
  · intro z hz
    exact norm_deriv_weightedGammaTerm_le hY hgammaLo hz

/-- The stated rectangle radii enclose the entire weighted term, not only its centre. -/
theorem weightedGammaTerm_box_error_le {Y gammaLo deltaBeta deltaGamma : ℝ} {rho0 rho : ℂ}
    (hY : 1 ≤ Y) (hgammaLo : 0 ≤ gammaLo)
    (hrho0 : rho0 ∈ spectralBoxDomain gammaLo) (hrho : rho ∈ spectralBoxDomain gammaLo)
    (hbeta : |rho.re - rho0.re| ≤ deltaBeta)
    (hgamma : |rho.im - rho0.im| ≤ deltaGamma) :
    ‖weightedGammaTerm Y rho - weightedGammaTerm Y rho0‖ ≤
      gammaBoxRadius Y gammaLo deltaBeta deltaGamma := by
  have hnorm : ‖rho - rho0‖ ≤ deltaBeta + deltaGamma := by
    have h := Complex.abs_le_abs_re_add_abs_im (rho - rho0)
    have h' : ‖rho - rho0‖ ≤ |rho.re - rho0.re| + |rho.im - rho0.im| := by
      simpa only [Complex.norm_eq_abs, Complex.sub_re, Complex.sub_im] using h
    exact h'.trans (add_le_add hbeta hgamma)
  have hc : 0 ≤ Y * Real.exp (-(Real.pi / 4) * gammaLo) * (19 + 2 * Real.log Y) := by
    have hY0 : 0 ≤ Y := zero_le_one.trans hY
    have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
    positivity
  exact (weightedGammaTerm_lipschitz_on_boxDomain hY hgammaLo hrho0 hrho).trans
    (mul_le_mul_of_nonneg_left hnorm hc)

theorem gammaBoxRadius_nonneg {Y gammaLo deltaBeta deltaGamma : ℝ}
    (hY : 1 ≤ Y) (hbeta : 0 ≤ deltaBeta) (hgamma : 0 ≤ deltaGamma) :
    0 ≤ gammaBoxRadius Y gammaLo deltaBeta deltaGamma := by
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
  unfold gammaBoxRadius
  positivity

/-- The closed radius formula is jointly continuous whenever Y is positive. -/
theorem gammaBoxRadius_continuousAt {Y gammaLo deltaBeta deltaGamma : ℝ} (hY : 0 < Y) :
    ContinuousAt (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
      gammaBoxRadius p.1 p.2.1 p.2.2.1 p.2.2.2) (Y, gammaLo, deltaBeta, deltaGamma) := by
  have hfirst : ContinuousAt (fun p : ℝ × (ℝ × (ℝ × ℝ)) => p.1)
      (Y, gammaLo, deltaBeta, deltaGamma) := continuous_fst.continuousAt
  have hheight : ContinuousAt (fun p : ℝ × (ℝ × (ℝ × ℝ)) => p.2.1)
      (Y, gammaLo, deltaBeta, deltaGamma) := (continuous_fst.comp continuous_snd).continuousAt
  have hbeta : ContinuousAt (fun p : ℝ × (ℝ × (ℝ × ℝ)) => p.2.2.1)
      (Y, gammaLo, deltaBeta, deltaGamma) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
  have hgamma : ContinuousAt (fun p : ℝ × (ℝ × (ℝ × ℝ)) => p.2.2.2)
      (Y, gammaLo, deltaBeta, deltaGamma) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt
  have hlog := (Real.continuousAt_log hY.ne').comp hfirst
  exact ((hfirst.mul ((continuousAt_const.mul hheight).rexp)).mul
    (continuousAt_const.add (continuousAt_const.mul hlog))).mul (hbeta.add hgamma)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.weightedGammaTerm
#print axioms GoldbachContinuous22.spectralBoxDomain
#print axioms GoldbachContinuous22.gammaBoxRadius
#print axioms GoldbachContinuous22.weightedGammaTerm_eq_cpow
#print axioms GoldbachContinuous22.spectralBoxDomain_convex
#print axioms GoldbachContinuous22.norm_weightedGamma_exponential_le
#print axioms GoldbachContinuous22.hasDerivAt_weightedGammaTerm
#print axioms GoldbachContinuous22.norm_deriv_weightedGammaTerm_le
#print axioms GoldbachContinuous22.weightedGammaTerm_lipschitz_on_boxDomain
#print axioms GoldbachContinuous22.weightedGammaTerm_box_error_le
#print axioms GoldbachContinuous22.gammaBoxRadius_nonneg
#print axioms GoldbachContinuous22.gammaBoxRadius_continuousAt
