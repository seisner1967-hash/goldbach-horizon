import GammaBoxBounds22
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/- SOURCE_ONLY. Actual Mellin-Gamma factor on vertical lines. This module bounds
   only that factor and its L1 tail; it does not assert a bound for zeta'/zeta,
   a contour residue identity, or a zero counting formula. -/

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology

namespace GoldbachContinuous22

def gammaContourPoint (c epsilon t : ℝ) : ℂ :=
  (c : ℂ) + ((epsilon * t : ℝ) : ℂ) * Complex.I

def gammaContourFactor (Y c epsilon t : ℝ) : ℂ :=
  weightedGammaTerm Y (gammaContourPoint c epsilon t)

def gammaContourEnvelope (Y T : ℝ) : ℝ :=
  ((27 / 5) * Y ^ (3 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * T) / (Real.pi / 4)

theorem norm_weightedGammaTerm_on_outer_strip {Y : ℝ} {rho : ℂ}
    (hY : 1 ≤ Y) (hr0 : -(1 / 2) ≤ rho.re) (hr1 : rho.re ≤ 3 / 2) :
    ‖weightedGammaTerm Y rho‖ ≤
      ((27 / 5) * Y ^ (3 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * |rho.im|) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hYnn : 0 ≤ Y := hY0.le
  have hs0 : 1 / 2 ≤ (rho + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hs1 : (rho + 1).re ≤ 5 / 2 := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hgamma : ‖Complex.Gamma (rho + 1)‖ ≤
      (27 / 5) * Real.exp (-(Real.pi / 4) * |rho.im|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using
      Gamma_extended_strip_exponential_bound hs0 hs1
  rw [weightedGammaTerm_eq_cpow hY0, norm_mul, Complex.norm_eq_abs,
    Complex.abs_cpow_eq_rpow_re_of_pos hY0]
  calc
    Y ^ rho.re * ‖Complex.Gamma (rho + 1)‖ ≤
        Y ^ (3 / 2 : ℝ) * ((27 / 5) * Real.exp (-(Real.pi / 4) * |rho.im|)) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hY hr1) hgamma
        (norm_nonneg _) (Real.rpow_nonneg hYnn _)
    _ = ((27 / 5) * Y ^ (3 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * |rho.im|) := by ring

theorem gammaContourFactor_continuous (Y c epsilon : ℝ) (hc : -(1 / 2) ≤ c) :
    Continuous (gammaContourFactor Y c epsilon) := by
  have hp : Continuous (gammaContourPoint c epsilon) := by
    unfold gammaContourPoint
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro t
  have hg : DifferentiableAt ℂ Complex.Gamma (gammaContourPoint c epsilon t + 1) :=
    Gamma_differentiableOn_rightHalfPlane.differentiableAt rightHalfPlane_isOpen
      (by
        change 0 < (gammaContourPoint c epsilon t + 1).re
        simp only [gammaContourPoint, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re]
        linarith)
  exact ((continuousAt_const.mul hp.continuousAt).cexp).mul
    (hg.continuousAt.comp (hp.continuousAt.add continuousAt_const))

theorem norm_gammaContourFactor_le {Y c epsilon t : ℝ} (hY : 1 ≤ Y)
    (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2) (hepsilon : |epsilon| = 1) (ht : 0 ≤ t) :
    ‖gammaContourFactor Y c epsilon t‖ ≤
      ((27 / 5) * Y ^ (3 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * t) := by
  have hre : (gammaContourPoint c epsilon t).re = c := by simp [gammaContourPoint]
  have him : |(gammaContourPoint c epsilon t).im| = t := by
    simp only [gammaContourPoint, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, abs_mul, hepsilon,
      one_mul, abs_of_nonneg ht]
  simpa only [gammaContourFactor, hre, him] using norm_weightedGammaTerm_on_outer_strip hY
    (show -(1 / 2) ≤ (gammaContourPoint c epsilon t).re by simpa only [hre] using hc0)
    (show (gammaContourPoint c epsilon t).re ≤ 3 / 2 by simpa only [hre] using hc1)

theorem real_exponential_tail_integrable {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi T) := by
  have h := real_laplace_integrable (a := (1 : ℝ)) (r := a) (by norm_num) ha
  have hzero : IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi 0) := by
    simpa only [sub_self, Real.rpow_zero, mul_one] using h
  exact hzero.mono_set (Ioi_subset_Ioi hT)

theorem integral_real_exponential_tail {a T : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi T, Real.exp (-(a * t))) = Real.exp (-(a * T)) / a := by
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-t)) T ha
  rw [Real.integral_exp_neg_Ioi] at h
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- The genuine factor has an integrable tail with a closed L1 error envelope.
    The two signs epsilon=1 and epsilon=-1 are both covered. -/
theorem gammaContourFactor_tail_integrable_and_bound {Y c epsilon T : ℝ}
    (hY : 1 ≤ Y) (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2)
    (hepsilon : |epsilon| = 1) (hT : 0 ≤ T) :
    IntegrableOn (gammaContourFactor Y c epsilon) (Ioi T) ∧
      (∫ t : ℝ in Ioi T, ‖gammaContourFactor Y c epsilon t‖) ≤ gammaContourEnvelope Y T := by
  have ha : 0 < Real.pi / 4 := by positivity
  let K : ℝ := (27 / 5) * Y ^ (3 / 2 : ℝ)
  have hg : IntegrableOn (fun t : ℝ => K * Real.exp (-(Real.pi / 4 * t))) (Ioi T) :=
    (real_exponential_tail_integrable ha hT).const_mul K
  have hle : ∀ t ∈ Ioi T, ‖gammaContourFactor Y c epsilon t‖ ≤
      K * Real.exp (-(Real.pi / 4 * t)) := by
    intro t ht
    simpa only [K, neg_mul] using norm_gammaContourFactor_le hY hc0 hc1 hepsilon
      (hT.trans ht.le)
  have hf : IntegrableOn (gammaContourFactor Y c epsilon) (Ioi T) := by
    apply hg.mono' ((gammaContourFactor_continuous Y c epsilon hc0).continuousOn.aestronglyMeasurable
      measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hle t ht
  refine ⟨hf, ?_⟩
  calc
    (∫ t : ℝ in Ioi T, ‖gammaContourFactor Y c epsilon t‖) ≤
        ∫ t : ℝ in Ioi T, K * Real.exp (-(Real.pi / 4 * t)) := by
      apply integral_mono_ae hf.norm hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hle t ht
    _ = gammaContourEnvelope Y T := by
      rw [integral_const_mul, integral_real_exponential_tail ha]
      unfold gammaContourEnvelope K
      simp only [neg_mul]
      ring

theorem gammaContourEnvelope_nonneg {Y T : ℝ} (hY : 0 ≤ Y) :
    0 ≤ gammaContourEnvelope Y T := by
  unfold gammaContourEnvelope
  positivity

theorem gammaContourEnvelope_continuous :
    Continuous (fun p : ℝ × ℝ => gammaContourEnvelope p.1 p.2) := by
  have hpow : Continuous (fun p : ℝ × ℝ => p.1 ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp continuous_fst
  exact ((continuous_const.mul hpow).mul
    ((continuous_const.mul continuous_snd).rexp)).div_const (Real.pi / 4)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.gammaContourPoint
#print axioms GoldbachContinuous22.gammaContourFactor
#print axioms GoldbachContinuous22.gammaContourEnvelope
#print axioms GoldbachContinuous22.norm_weightedGammaTerm_on_outer_strip
#print axioms GoldbachContinuous22.gammaContourFactor_continuous
#print axioms GoldbachContinuous22.norm_gammaContourFactor_le
#print axioms GoldbachContinuous22.real_exponential_tail_integrable
#print axioms GoldbachContinuous22.integral_real_exponential_tail
#print axioms GoldbachContinuous22.gammaContourFactor_tail_integrable_and_bound
#print axioms GoldbachContinuous22.gammaContourEnvelope_nonneg
#print axioms GoldbachContinuous22.gammaContourEnvelope_continuous
