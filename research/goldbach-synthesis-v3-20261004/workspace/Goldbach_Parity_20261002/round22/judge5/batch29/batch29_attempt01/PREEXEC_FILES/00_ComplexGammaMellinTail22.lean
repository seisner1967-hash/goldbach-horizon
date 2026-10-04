import ComplexGammaMellinLocal22
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.SetIntegral

/-! DRAFT SOURCE ONLY. No author compiler, probe or numerical evaluator.
The imported genuine Gamma domination is independently checked in Local26.
This module derives explicit tails, rather than assuming a final error bound.
No zeta trace, arithmetic exchange, boundary cancellation or D_N is asserted.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace GoldbachComplexGammaMellin22

def signedGammaTail (w : ℂ) (H : ℝ) (negative : Bool) : ℂ :=
  ∫ t : ℝ in Ioi H, complexGammaKernel w (if negative then -t else t)

def complexGammaTail (w : ℂ) (H : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    (signedGammaTail w H true + signedGammaTail w H false)

def complexGammaTailRadius (w : ℂ) (H : ℝ) : ℝ :=
  kernelCoefficient w * Real.exp (-decayGap w * H) / (Real.pi * decayGap w)

def complexGammaTruncated (w : ℂ) (H : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ t : ℝ in Icc (-H) H, complexGammaKernel w t

/-- The half-line exponential integral is evaluated by a real change of variable. -/
theorem exponential_Ioi_integral {d : ℝ} (hd : 0 < d) (H : ℝ) :
    (∫ t : ℝ in Ioi H, Real.exp (-d * t)) = Real.exp (-d * H) / d := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u)) H hd
  rw [integral_exp_neg_Ioi] at h
  calc
    _ = d⁻¹ * Real.exp (-(d * H)) := by
      simpa only [neg_mul, smul_eq_mul] using h
    _ = _ := by simp only [neg_mul, div_eq_mul_inv]; ring

/-- Integrability above H follows from the actual Laplace kernel above zero. -/
theorem exponential_Ioi_integrable {d : ℝ} (hd : 0 < d) {H : ℝ} (hH : 0 ≤ H)
    (C : ℝ) : IntegrableOn (fun t : ℝ => C * Real.exp (-d * t)) (Ioi H) := by
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-d * t)) (Ioi 0) := by
    simpa only [sub_self, Real.rpow_zero, mul_one, neg_mul] using
      GoldbachContinuous22.real_laplace_integrable (a := 1) (by norm_num) hd
  have hmul : IntegrableOn (fun t : ℝ => C * Real.exp (-d * t)) (Ioi 0) := h0.const_mul C
  exact IntegrableOn.mono_set hmul (Ioi_subset_Ioi hH)

theorem kernelCoefficient_nonneg (w : ℂ) : 0 ≤ kernelCoefficient w := by
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg w) _) (sq_nonneg _)

theorem rotationAngle_cos_pos {w : ℂ} (hw : 0 < w.re) :
    0 < Real.cos (rotationAngle w) := by
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [rotationAngle_pos w, Real.pi_pos], rotationAngle_lt_pi_half hw⟩

theorem kernelCoefficient_pos {w : ℂ} (hw : 0 < w.re) : 0 < kernelCoefficient w := by
  exact mul_pos (Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (rightHalfPlane_ne_zero hw)) _)
    (pow_pos (div_pos zero_lt_one (rotationAngle_cos_pos hw)) 2)

/-- Both actual signed integrands are L1 on the tail, with no integrability premise. -/
theorem signedGammaTail_integrable {w : ℂ} (hw : 0 < w.re) {H : ℝ} (hH : 0 ≤ H)
    (negative : Bool) :
    IntegrableOn (fun t : ℝ => complexGammaKernel w (if negative then -t else t))
      (Ioi H) := by
  have hm := exponential_Ioi_integrable (decayGap_pos hw) hH (kernelCoefficient w)
  have hsign : Continuous (fun t : ℝ => if negative then -t else t) := by
    cases negative <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  apply hm.mono' ((complexGammaKernel_continuous hw).comp hsign).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := hH.trans_lt ht
  have h := complexGammaKernel_bound hw (if negative then -t else t)
  cases negative <;>
    simpa only [Bool.false_eq_true, if_false, if_true, abs_neg, abs_of_pos htpos] using h

/-- The explicit radius is the integral of the derived true-Gamma majorant. -/
theorem signedGammaTail_norm_le {w : ℂ} (hw : 0 < w.re) {H : ℝ} (hH : 0 ≤ H)
    (negative : Bool) :
    ‖signedGammaTail w H negative‖ ≤
      kernelCoefficient w * Real.exp (-decayGap w * H) / decayGap w := by
  have hi := signedGammaTail_integrable hw hH negative
  have hm := exponential_Ioi_integrable (decayGap_pos hw) hH (kernelCoefficient w)
  have hb : (fun t : ℝ => ‖complexGammaKernel w (if negative then -t else t)‖) ≤ᵐ[
      volume.restrict (Ioi H)] (fun t : ℝ => kernelCoefficient w * Real.exp (-decayGap w * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hH.trans_lt ht
    have h := complexGammaKernel_bound hw (if negative then -t else t)
    cases negative <;>
      simpa only [Bool.false_eq_true, if_false, if_true, abs_neg, abs_of_pos htpos] using h
  calc
    _ ≤ ∫ t : ℝ in Ioi H, ‖complexGammaKernel w (if negative then -t else t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi H, kernelCoefficient w * Real.exp (-decayGap w * t) :=
      integral_mono_ae hi.norm hm hb
    _ = _ := by
      rw [integral_mul_left, exponential_Ioi_integral (decayGap_pos hw)]
      ring

theorem complexGammaTail_norm_le {w : ℂ} (hw : 0 < w.re) {H : ℝ} (hH : 0 ≤ H) :
    ‖complexGammaTail w H‖ ≤ complexGammaTailRadius w H := by
  have hscale : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hpair := (norm_add_le (signedGammaTail w H true) (signedGammaTail w H false)).trans
    (add_le_add (signedGammaTail_norm_le hw hH true) (signedGammaTail_norm_le hw hH false))
  rw [complexGammaTail, norm_mul, hscale]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (kernelCoefficient w * Real.exp (-decayGap w * H) / decayGap w +
          kernelCoefficient w * Real.exp (-decayGap w * H) / decayGap w) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = _ := by
      dsimp only [complexGammaTailRadius]
      field_simp [Real.pi_ne_zero, (decayGap_pos hw).ne'] <;> ring

/-- The negative ray is transported by the actual Lebesgue measure. -/
theorem signedGammaTail_true_eq_Iio (w : ℂ) (H : ℝ) :
    signedGammaTail w H true = ∫ t : ℝ in Iio (-H), complexGammaKernel w t := by
  change (∫ t : ℝ in Ioi H, complexGammaKernel w (-t)) = _
  rw [integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio]

/-- Splitting the actual L1 integral identifies the tail with the truncation error. -/
theorem complexGammaInverse_sub_truncated_eq_tail {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    complexGammaInverse w - complexGammaTruncated w H = complexGammaTail w H := by
  have hi := complexGammaKernel_integrable hw
  have hset : (Icc (-H) H)ᶜ = Iio (-H) ∪ Ioi H := by
    ext t
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro ht
      by_cases hl : -H ≤ t
      · exact Or.inr (lt_of_not_ge (fun h => ht ⟨hl, h⟩))
      · exact Or.inl (lt_of_not_ge hl)
    · intro ht hboth
      rcases ht with hl | hr
      · exact not_lt_of_ge hboth.1 hl
      · exact not_lt_of_ge hboth.2 hr
  have hdis : Disjoint (Iio (-H)) (Ioi H) := by
    apply disjoint_left.mpr
    intro t hl hr
    have hl' : t < -H := hl
    have hr' : H < t := hr
    linarith
  have htail : (∫ t : ℝ in (Icc (-H) H)ᶜ, complexGammaKernel w t) =
      signedGammaTail w H true + signedGammaTail w H false := by
    calc
      _ = (∫ t : ℝ in Iio (-H), complexGammaKernel w t) +
          ∫ t : ℝ in Ioi H, complexGammaKernel w t := by
        rw [hset]
        exact setIntegral_union hdis measurableSet_Ioi hi.integrableOn hi.integrableOn
      _ = _ := by rw [signedGammaTail_true_eq_Iio]; rfl
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (f := complexGammaKernel w) (s := Icc (-H) H) measurableSet_Icc hi
  rw [htail] at hsplit
  dsimp only [complexGammaInverse, complexGammaTruncated, complexGammaTail]
  rw [← hsplit]
  ring

theorem complexGammaInverse_truncation_error_le {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖complexGammaInverse w - complexGammaTruncated w H‖ ≤ complexGammaTailRadius w H := by
  rw [complexGammaInverse_sub_truncated_eq_tail hw hH]
  exact complexGammaTail_norm_le hw hH

theorem rotationAngle_continuousAt {w : ℂ} (hw : 0 < w.re) : ContinuousAt rotationAngle w := by
  have ha := (Complex.continuousAt_arg (rightHalfPlane_mem_slitPlane hw)).abs
  exact (continuousAt_const.add ha).div_const 2

theorem decayGap_continuousAt {w : ℂ} (hw : 0 < w.re) : ContinuousAt decayGap w := by
  exact (rotationAngle_continuousAt hw).sub
    (Complex.continuousAt_arg (rightHalfPlane_mem_slitPlane hw)).abs

theorem kernelCoefficient_continuousAt {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt kernelCoefficient w := by
  have hp : ContinuousAt (fun z : ℂ => ‖z‖ ^ (-2 : ℝ)) w :=
    continuous_norm.continuousAt.rpow_const
      (Or.inl (norm_pos_iff.mpr (rightHalfPlane_ne_zero hw)).ne')
  have hc := Real.continuous_cos.continuousAt.comp (rotationAngle_continuousAt hw)
  exact hp.mul ((continuousAt_const.div hc (rotationAngle_cos_pos hw).ne').pow 2)

/-- Joint continuity is restricted to the genuine open right half-plane. -/
theorem complexGammaTailRadius_continuousAt {p : ℂ × ℝ} (hp : 0 < p.1.re) :
    ContinuousAt (fun q : ℂ × ℝ => complexGammaTailRadius q.1 q.2) p := by
  have hC : ContinuousAt (fun q : ℂ × ℝ => kernelCoefficient q.1) p :=
    (kernelCoefficient_continuousAt hp).comp continuousAt_fst
  have hd : ContinuousAt (fun q : ℂ × ℝ => decayGap q.1) p :=
    (decayGap_continuousAt hp).comp continuousAt_fst
  have he : ContinuousAt (fun q : ℂ × ℝ => Real.exp (-decayGap q.1 * q.2)) p :=
    Real.continuous_exp.continuousAt.comp (hd.neg.mul continuousAt_snd)
  exact (hC.mul he).div (continuousAt_const.mul hd)
    (mul_ne_zero Real.pi_ne_zero (decayGap_pos hp).ne')

theorem complexGammaTailRadius_pos {w : ℂ} (hw : 0 < w.re) (H : ℝ) :
    0 < complexGammaTailRadius w H := by
  exact div_pos (mul_pos (kernelCoefficient_pos hw) (Real.exp_pos _))
    (mul_pos Real.pi_pos (decayGap_pos hw))

theorem complexGammaTailRadius_antitone {w : ℂ} (hw : 0 < w.re) {H H' : ℝ}
    (hH : H ≤ H') : complexGammaTailRadius w H' ≤ complexGammaTailRadius w H := by
  apply div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (kernelCoefficient_nonneg w))
    (mul_nonneg Real.pi_pos.le (decayGap_pos hw).le)
  nlinarith [decayGap_pos hw]

/-- A local uniform tail follows from a constructed ball and the closed center radius. -/
theorem exists_local_uniform_Gamma_tail {w : ℂ} (hw : 0 < w.re) {H : ℝ} (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball w ε, 0 < z.re ∧
      ∀ T : ℝ, H ≤ T → ‖complexGammaTail z T‖ ≤ 2 * complexGammaTailRadius w H := by
  have hp : ContinuousAt (fun z : ℂ => (z, H)) w :=
    (continuousAt_id : ContinuousAt (fun z : ℂ => z) w).prod
      (continuousAt_const : ContinuousAt (fun _ : ℂ => H) w)
  have hr : ContinuousAt (fun z : ℂ => complexGammaTailRadius z H) w := by
    have h := (complexGammaTailRadius_continuousAt (p := (w, H)) hw).comp hp
    simpa only [Function.comp_apply] using h
  have hre : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hw
  have hrad : ∀ᶠ z : ℂ in 𝓝 w, complexGammaTailRadius z H < 2 * complexGammaTailRadius w H :=
    hr.eventually_lt continuousAt_const (by linarith [complexGammaTailRadius_pos hw H])
  apply Metric.eventually_nhds_iff_ball.mp
  filter_upwards [hre, hrad] with z hz hbound
  refine ⟨hz, ?_⟩
  intro T hT
  exact (complexGammaTail_norm_le hz (hH.trans hT)).trans
    ((complexGammaTailRadius_antitone hz hT).trans hbound.le)

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.signedGammaTail
#print axioms GoldbachComplexGammaMellin22.complexGammaTail
#print axioms GoldbachComplexGammaMellin22.complexGammaTailRadius
#print axioms GoldbachComplexGammaMellin22.complexGammaTruncated
#print axioms GoldbachComplexGammaMellin22.exponential_Ioi_integral
#print axioms GoldbachComplexGammaMellin22.exponential_Ioi_integrable
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient_nonneg
#print axioms GoldbachComplexGammaMellin22.rotationAngle_cos_pos
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient_pos
#print axioms GoldbachComplexGammaMellin22.signedGammaTail_integrable
#print axioms GoldbachComplexGammaMellin22.signedGammaTail_norm_le
#print axioms GoldbachComplexGammaMellin22.complexGammaTail_norm_le
#print axioms GoldbachComplexGammaMellin22.signedGammaTail_true_eq_Iio
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse_sub_truncated_eq_tail
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse_truncation_error_le
#print axioms GoldbachComplexGammaMellin22.rotationAngle_continuousAt
#print axioms GoldbachComplexGammaMellin22.decayGap_continuousAt
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient_continuousAt
#print axioms GoldbachComplexGammaMellin22.complexGammaTailRadius_continuousAt
#print axioms GoldbachComplexGammaMellin22.complexGammaTailRadius_pos
#print axioms GoldbachComplexGammaMellin22.complexGammaTailRadius_antitone
#print axioms GoldbachComplexGammaMellin22.exists_local_uniform_Gamma_tail
