import ComplexGammaMellinLambda22
import ComplexGammaMellinTail22

/-! SOURCE ONLY / PENDING_DEPENDENCIES. Lambda30 and the separate Tail03
repair require their actual independent compiler verdicts. Tail29 failed.
No candidate execution is authorized.
The weighted tails below are bounded by integrating the actual pointwise
majorant; no cancellation bound for an unweighted integral is substituted.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace GoldbachComplexGammaMellin22

def signedLambdaMellinTail (w : ℂ) (H : ℝ) (negative : Bool) : ℂ :=
  ∫ t : ℝ in Ioi H,
    lambdaMellinDirichlet (if negative then -t else t) *
      complexGammaKernel w (if negative then -t else t)

def lambdaMellinTail (w : ℂ) (H : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    (signedLambdaMellinTail w H true + signedLambdaMellinTail w H false)

def lambdaMellinTailRadius (w : ℂ) (H : ℝ) : ℝ :=
  6 * complexGammaTailRadius w H

def lambdaMellinTruncated (w : ℂ) (H : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ t : ℝ in Icc (-H) H, lambdaMellinDirichlet t * complexGammaKernel w t

/-- Genuine Lambda mass and genuine Gamma domination give a pointwise product bound. -/
theorem lambdaMellinProduct_bound {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    ‖lambdaMellinDirichlet t * complexGammaKernel w t‖ ≤
      (6 * kernelCoefficient w) * Real.exp (-decayGap w * |t|) := by
  rw [norm_mul]
  calc
    _ ≤ 6 * ‖complexGammaKernel w t‖ :=
      mul_le_mul_of_nonneg_right (norm_lambdaMellinDirichlet_le t) (norm_nonneg _)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (complexGammaKernel_bound hw t)
        (by norm_num : (0 : ℝ) ≤ 6)
      simpa only [mul_assoc] using h

/-- Both actual signed weighted integrands are L1, with no L1 premise. -/
theorem signedLambdaMellinTail_integrable {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) (negative : Bool) :
    IntegrableOn (fun t : ℝ =>
      lambdaMellinDirichlet (if negative then -t else t) *
        complexGammaKernel w (if negative then -t else t)) (Ioi H) := by
  have hm := exponential_Ioi_integrable (decayGap_pos hw) hH (6 * kernelCoefficient w)
  have hsign : Continuous (fun t : ℝ => if negative then -t else t) := by
    cases negative <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have hc := (lambdaMellinDirichlet_continuous.mul
    (complexGammaKernel_continuous hw)).comp hsign
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := hH.trans_lt ht
  have h := lambdaMellinProduct_bound hw (if negative then -t else t)
  cases negative <;>
    simpa only [Bool.false_eq_true, if_false, if_true, abs_neg, abs_of_pos htpos] using h

/-- Each weighted ray is controlled by the integral of its explicit majorant. -/
theorem signedLambdaMellinTail_norm_le {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) (negative : Bool) :
    ‖signedLambdaMellinTail w H negative‖ ≤
      (6 * kernelCoefficient w) * Real.exp (-decayGap w * H) / decayGap w := by
  have hi := signedLambdaMellinTail_integrable hw hH negative
  have hm := exponential_Ioi_integrable (decayGap_pos hw) hH (6 * kernelCoefficient w)
  have hb : (fun t : ℝ =>
      ‖lambdaMellinDirichlet (if negative then -t else t) *
        complexGammaKernel w (if negative then -t else t)‖) ≤ᵐ[
      volume.restrict (Ioi H)]
      (fun t : ℝ => (6 * kernelCoefficient w) * Real.exp (-decayGap w * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hH.trans_lt ht
    have h := lambdaMellinProduct_bound hw (if negative then -t else t)
    cases negative <;>
      simpa only [Bool.false_eq_true, if_false, if_true, abs_neg, abs_of_pos htpos] using h
  calc
    _ ≤ ∫ t : ℝ in Ioi H,
        ‖lambdaMellinDirichlet (if negative then -t else t) *
          complexGammaKernel w (if negative then -t else t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi H,
        (6 * kernelCoefficient w) * Real.exp (-decayGap w * t) :=
      integral_mono_ae hi.norm hm hb
    _ = _ := by
      rw [integral_mul_left, exponential_Ioi_integral (decayGap_pos hw)]
      ring

theorem lambdaMellinTail_norm_le {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖lambdaMellinTail w H‖ ≤ lambdaMellinTailRadius w H := by
  have hscale : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hpair := (norm_add_le (signedLambdaMellinTail w H true)
    (signedLambdaMellinTail w H false)).trans
    (add_le_add (signedLambdaMellinTail_norm_le hw hH true)
      (signedLambdaMellinTail_norm_le hw hH false))
  rw [lambdaMellinTail, norm_mul, hscale]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        ((6 * kernelCoefficient w) * Real.exp (-decayGap w * H) / decayGap w +
          (6 * kernelCoefficient w) * Real.exp (-decayGap w * H) / decayGap w) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = _ := by
      dsimp only [lambdaMellinTailRadius, complexGammaTailRadius]
      field_simp [Real.pi_ne_zero, (decayGap_pos hw).ne'] <;> ring

/-- Lebesgue reflection transports the actual product, including the phase of D. -/
theorem signedLambdaMellinTail_true_eq_Iio (w : ℂ) (H : ℝ) :
    signedLambdaMellinTail w H true =
      ∫ t : ℝ in Iio (-H), lambdaMellinDirichlet t * complexGammaKernel w t := by
  change (∫ t : ℝ in Ioi H,
    lambdaMellinDirichlet (-t) * complexGammaKernel w (-t)) = _
  rw [integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio]

/-- The full Lambda Mellin identity and the actual L1 split give the truncation identity. -/
theorem lambdaMellinThermal_sub_truncated_eq_tail {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    lambdaMellinThermal w - lambdaMellinTruncated w H = lambdaMellinTail w H := by
  have hi := lambdaMellinProduct_integrable hw
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
  have htail : (∫ t : ℝ in (Icc (-H) H)ᶜ,
      lambdaMellinDirichlet t * complexGammaKernel w t) =
      signedLambdaMellinTail w H true + signedLambdaMellinTail w H false := by
    calc
      _ = (∫ t : ℝ in Iio (-H), lambdaMellinDirichlet t * complexGammaKernel w t) +
          ∫ t : ℝ in Ioi H, lambdaMellinDirichlet t * complexGammaKernel w t := by
        rw [hset]
        exact setIntegral_union hdis measurableSet_Ioi hi.integrableOn hi.integrableOn
      _ = _ := by rw [signedLambdaMellinTail_true_eq_Iio]; rfl
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (f := fun t : ℝ => lambdaMellinDirichlet t * complexGammaKernel w t)
    (s := Icc (-H) H) measurableSet_Icc hi
  rw [htail] at hsplit
  rw [lambdaMellinThermal_eq_integral hw]
  dsimp only [lambdaMellinTruncated, lambdaMellinTail]
  rw [← hsplit]
  ring

theorem lambdaMellinThermal_truncation_error_le {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖lambdaMellinThermal w - lambdaMellinTruncated w H‖ ≤ lambdaMellinTailRadius w H := by
  rw [lambdaMellinThermal_sub_truncated_eq_tail hw hH]
  exact lambdaMellinTail_norm_le hw hH

theorem lambdaMellinTailRadius_eq_closed (w : ℂ) (H : ℝ) :
    lambdaMellinTailRadius w H =
      6 * kernelCoefficient w * Real.exp (-decayGap w * H) / (Real.pi * decayGap w) := by
  dsimp only [lambdaMellinTailRadius, complexGammaTailRadius]
  ring

/-- The radius, rather than an asserted moving-threshold complex tail, is jointly continuous. -/
theorem lambdaMellinTailRadius_continuousAt {p : ℂ × ℝ} (hp : 0 < p.1.re) :
    ContinuousAt (fun q : ℂ × ℝ => lambdaMellinTailRadius q.1 q.2) p := by
  exact continuousAt_const.mul (complexGammaTailRadius_continuousAt hp)

theorem lambdaMellinTailRadius_pos {w : ℂ} (hw : 0 < w.re) (H : ℝ) :
    0 < lambdaMellinTailRadius w H :=
  mul_pos (by norm_num) (complexGammaTailRadius_pos hw H)

theorem lambdaMellinTailRadius_antitone {w : ℂ} (hw : 0 < w.re) {H H' : ℝ}
    (hH : H ≤ H') : lambdaMellinTailRadius w H' ≤ lambdaMellinTailRadius w H :=
  mul_le_mul_of_nonneg_left (complexGammaTailRadius_antitone hw hH) (by norm_num)

theorem exists_local_uniform_Lambda_tail {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball w ε, 0 < z.re ∧
      ∀ T : ℝ, H ≤ T → ‖lambdaMellinTail z T‖ ≤ 2 * lambdaMellinTailRadius w H := by
  have hp : ContinuousAt (fun z : ℂ => (z, H)) w :=
    (continuousAt_id : ContinuousAt (fun z : ℂ => z) w).prod
      (continuousAt_const : ContinuousAt (fun _ : ℂ => H) w)
  have hr : ContinuousAt (fun z : ℂ => lambdaMellinTailRadius z H) w := by
    have h := ContinuousAt.comp
      (f := fun z : ℂ => (z, H))
      (g := fun q : ℂ × ℝ => lambdaMellinTailRadius q.1 q.2)
      (x := w) (lambdaMellinTailRadius_continuousAt (p := (w, H)) hw) hp
    simpa only [Function.comp_apply] using h
  have hre : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hw
  have hrad : ∀ᶠ z : ℂ in 𝓝 w,
      lambdaMellinTailRadius z H < 2 * lambdaMellinTailRadius w H :=
    hr.eventually_lt continuousAt_const (by linarith [lambdaMellinTailRadius_pos hw H])
  apply Metric.eventually_nhds_iff_ball.mp
  filter_upwards [hre, hrad] with z hz hbound
  refine ⟨hz, ?_⟩
  intro T hT
  exact (lambdaMellinTail_norm_le hz (hH.trans hT)).trans
    ((lambdaMellinTailRadius_antitone hz hT).trans hbound.le)

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.signedLambdaMellinTail
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTail
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTailRadius
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTruncated
#print axioms GoldbachComplexGammaMellin22.lambdaMellinProduct_bound
#print axioms GoldbachComplexGammaMellin22.signedLambdaMellinTail_integrable
#print axioms GoldbachComplexGammaMellin22.signedLambdaMellinTail_norm_le
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTail_norm_le
#print axioms GoldbachComplexGammaMellin22.signedLambdaMellinTail_true_eq_Iio
#print axioms GoldbachComplexGammaMellin22.lambdaMellinThermal_sub_truncated_eq_tail
#print axioms GoldbachComplexGammaMellin22.lambdaMellinThermal_truncation_error_le
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTailRadius_eq_closed
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTailRadius_continuousAt
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTailRadius_pos
#print axioms GoldbachComplexGammaMellin22.lambdaMellinTailRadius_antitone
#print axioms GoldbachComplexGammaMellin22.exists_local_uniform_Lambda_tail
