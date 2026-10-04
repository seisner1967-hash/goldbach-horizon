import PsiKernelDomination22
import GammaContourComponent22
import Mathlib.MeasureTheory.Integral.Prod

/-! SOURCE ONLY. The concrete mixed integrand is the actual Gamma contour
factor times the paired digamma kernel. Its envelope and product integrability
are constructed below, before using Fubini. No interchange, Gamma bound,
P1, C5 or free majorant is a premise of any final concrete theorem here.
The imported contour component must be the separately repaired genuine source,
never the old staging file with its outstanding neighbourhood API error. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def psiMixedEnvelope (Y t v : ℝ) : ℝ :=
  4 * Y ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|) * psiKernelEnvelope t v

def psiTrueMixedIntegrand (Y t v : ℝ) : ℂ :=
  gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
    contourPsiScaledKernel (leftChiPoint t) v

theorem leftChiPoint_im (t : ℝ) : (leftChiPoint t).im = t := by
  simp only [leftChiPoint, Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, neg_zero]

theorem gammaContourPoint_left_eq (t : ℝ) :
    gammaContourPoint (-(1 / 2 : ℝ)) 1 t = leftChiPoint t := by
  unfold gammaContourPoint leftChiPoint
  push_cast
  ring

theorem Gamma_halfline_exponential_bound {u : ℂ} (hu : u.re = 1 / 2) :
    ‖Complex.Gamma u‖ ≤ 4 * Real.exp (-(Real.pi / 4) * |u.im|) := by
  have hu0 : 0 < u.re := by rw [hu]; norm_num
  have hune : u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    linarith
  have hup : 1 ≤ (u + 1).re := by
    simp only [Complex.add_re, Complex.one_re, hu]
    norm_num
  have hup2 : (u + 1).re ≤ 2 := by
    simp only [Complex.add_re, Complex.one_re, hu]
    norm_num
  have hg := Gamma_strip_exponential_bound hup hup2
  rw [Complex.Gamma_add_one u hune, norm_mul] at hg
  simp only [Complex.add_im, Complex.one_im, add_zero] at hg
  have hn : 1 / 2 ≤ ‖u‖ := by
    simpa only [hu, Complex.norm_eq_abs] using Complex.re_le_abs u
  have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg (Complex.Gamma u))
  linarith

theorem norm_gammaContourFactor_left_le {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    ‖gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t‖ ≤
      4 * Y ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|) := by
  have hhalf : (leftChiPoint t + 1).re = 1 / 2 := by
    rw [Complex.add_re, leftChiPoint_re, Complex.one_re]
    ring
  have hg : ‖Complex.Gamma (leftChiPoint t + 1)‖ ≤
      4 * Real.exp (-(Real.pi / 4) * |t|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero, leftChiPoint_im] using
      Gamma_halfline_exponential_bound hhalf
  rw [gammaContourFactor, gammaContourPoint_left_eq, weightedGammaTerm_eq_cpow hY,
    norm_mul, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hY,
    leftChiPoint_re]
  calc
    Y ^ (-(1 / 2 : ℝ)) * ‖Complex.Gamma (leftChiPoint t + 1)‖ ≤
        Y ^ (-(1 / 2 : ℝ)) * (4 * Real.exp (-(Real.pi / 4) * |t|)) :=
      mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hY.le _)
    _ = 4 * Y ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi / 4) * |t|) := by ring

theorem psiMixedEnvelope_nonneg {Y : ℝ} (hY : 0 ≤ Y) (t v : ℝ) :
    0 ≤ psiMixedEnvelope Y t v := by
  unfold psiMixedEnvelope
  have he := psiKernelEnvelope_nonneg t v
  have hy := Real.rpow_nonneg hY (-(1 / 2 : ℝ))
  positivity

theorem psiMixedEnvelope_joint_continuous (Y : ℝ) :
    Continuous (fun p : ℝ × ℝ => psiMixedEnvelope Y p.1 p.2) := by
  unfold psiMixedEnvelope
  exact (continuous_const.mul
    ((continuous_const.mul continuous_fst.abs).rexp)).mul
      psiKernelEnvelope_joint_continuous

theorem norm_psiTrueMixedIntegrand_le {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {v : ℝ} (hv : 0 < v) :
    ‖psiTrueMixedIntegrand Y t v‖ ≤ psiMixedEnvelope Y t v := by
  unfold psiTrueMixedIntegrand psiMixedEnvelope
  rw [norm_mul]
  exact mul_le_mul (norm_gammaContourFactor_left_le hY t)
    (norm_contourPsiScaledKernel_left_le_envelope t hv) (norm_nonneg _)
    (by have hy := Real.rpow_nonneg hY.le (-(1 / 2 : ℝ)); positivity)

theorem neg_image_Iio_zero :
    (fun t : ℝ => -t) '' Iio (0 : ℝ) = Ioi (0 : ℝ) := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact neg_pos.mpr ht
  · intro hu
    exact ⟨-u, neg_lt_zero.mpr hu, neg_neg u⟩

theorem integrable_abs_extension {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ => f |t|) := by
  have hpos : IntegrableOn (fun t : ℝ => f |t|) (Ioi (0 : ℝ)) := by
    apply hf.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos ht]
  have himage : IntegrableOn f ((fun t : ℝ => -t) '' Iio (0 : ℝ)) := by
    rw [neg_image_Iio_zero]
    exact hf
  have hinj : InjOn (fun t : ℝ => -t) (Iio (0 : ℝ)) := by
    intro a ha b hb hab
    exact neg_injective hab
  have hneg0 := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iio
    (fun t ht => (hasDerivAt_id t).neg.hasDerivWithinAt) hinj f).mp himage
  have hneg : IntegrableOn (fun t : ℝ => f |t|) (Iio (0 : ℝ)) := by
    have hclean : IntegrableOn (fun t : ℝ => f (-t)) (Iio (0 : ℝ)) := by
      simpa only [abs_neg, abs_one, one_smul] using hneg0
    apply hclean.congr
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    rw [abs_of_neg ht]
  have hclosed : IntegrableOn (fun t : ℝ => f |t|) (Ici (0 : ℝ)) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr hpos
  have h := hneg.union hclosed
  rw [Iio_union_Ici] at h
  exact integrableOn_univ.mp h

theorem integrable_exp_negative_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => Real.exp (-a * |t|)) :=
  integrable_abs_extension (integrableOn_exp_negative_scale ha)

theorem integrable_abs_mul_exp_negative_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => |t| * Real.exp (-a * |t|)) := by
  have h := real_laplace_integrable (a := (2 : ℝ)) (r := a) (by norm_num) ha
  have hp : IntegrableOn (fun t : ℝ => t * Real.exp (-a * t)) (Ioi (0 : ℝ)) := by
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at h
    simpa only [neg_mul, mul_comm] using h
  exact integrable_abs_extension hp

theorem integrable_linear_abs_exp_negative_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => (14 + 4 * |t|) * Real.exp (-a * |t|)) := by
  have h := ((integrable_exp_negative_abs ha).const_mul 14).add
    ((integrable_abs_mul_exp_negative_abs ha).const_mul 4)
  apply h.congr
  exact Eventually.of_forall (fun t => by ring)

theorem integrableOn_exp_one_sub :
    IntegrableOn (fun v : ℝ => Real.exp (1 - v)) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_exp_negative_scale (a := (1 : ℝ)) (by norm_num)).const_mul
    (Real.exp 1)
  apply h.congr
  exact Eventually.of_forall (fun v => by
    rw [show 1 - v = 1 + -v by ring, Real.exp_add]
    simp only [neg_one_mul])

theorem integrable_psiMixedEnvelope (Y : ℝ) :
    Integrable (fun p : ℝ × ℝ => psiMixedEnvelope Y p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let k : ℝ := 4 * Y ^ (-(1 / 2 : ℝ))
  have ha : 0 < Real.pi / 4 := by positivity
  have ht1 := (integrable_linear_abs_exp_negative_abs ha).const_mul k
  have ht2 := (integrable_exp_negative_abs ha).const_mul (k * 8)
  have hv1 := integrableOn_exp_one_sub
  have hv2 := integrableOn_exp_negative_scale (a := (3 / 2 : ℝ)) (by norm_num)
  have h := (ht1.prod_mul hv1).add (ht2.prod_mul hv2)
  apply h.congr
  exact Eventually.of_forall (fun p => by
    unfold psiMixedEnvelope psiKernelEnvelope k
    simp only [neg_mul]
    ring)

theorem continuousOn_psiTrueMixedIntegrand (Y : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => psiTrueMixedIntegrand Y p.1 p.2)
      ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have hnum : Continuous (fun p : ℝ × ℝ => psiKernelNumerator p.1 p.2) := by
    unfold psiKernelNumerator psiSlopeCoeff
    fun_prop
  have hden : Continuous (fun p : ℝ × ℝ => 1 - Complex.exp (-2 * (p.2 : ℂ))) := by
    fun_prop
  have hden0 : ∀ p ∈ ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)),
      1 - Complex.exp (-2 * (p.2 : ℂ)) ≠ 0 := by
    intro p hp
    apply norm_pos_iff.mp
    rw [norm_complex_psiDenominator hp.2]
    exact psiDenominator_pos hp.2
  have hk := hnum.continuousOn.div hden.continuousOn hden0
  have hG : Continuous (fun p : ℝ × ℝ => gammaContourFactor Y (-(1 / 2 : ℝ)) 1 p.1) :=
    (gammaContourFactor_continuous Y (-(1 / 2 : ℝ)) 1 le_rfl).comp continuous_fst
  have heq : (fun p : ℝ × ℝ => contourPsiScaledKernel (leftChiPoint p.1) p.2) =
      (fun p : ℝ × ℝ => psiKernelNumerator p.1 p.2 /
        (1 - Complex.exp (-2 * (p.2 : ℂ)))) := by
    funext p
    exact contourPsiScaledKernel_left_eq_numerator p.1 p.2
  have hkActual : ContinuousOn
      (fun p : ℝ × ℝ => contourPsiScaledKernel (leftChiPoint p.1) p.2)
      ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
    rw [heq]
    exact hk
  exact hG.continuousOn.mul hkActual

theorem integrable_psiTrueMixedIntegrand {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun p : ℝ × ℝ => psiTrueMixedIntegrand Y p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeasure : volume.prod (volume.restrict (Ioi (0 : ℝ))) =
      (volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (univ : Set ℝ) (Ioi (0 : ℝ)))
  have hmajorant := integrable_psiMixedEnvelope Y
  rw [hmeasure] at hmajorant ⊢
  apply hmajorant.mono' ((continuousOn_psiTrueMixedIntegrand Y).aestronglyMeasurable
    (measurableSet_univ.prod measurableSet_Ioi))
  filter_upwards [ae_restrict_mem (measurableSet_univ.prod measurableSet_Ioi)] with p hp
  exact norm_psiTrueMixedIntegrand_le hY p.1 hp.2

theorem psiTrueMixedIntegrand_fubini {Y : ℝ} (hY : 0 < Y) :
    (∫ t : ℝ, ∫ v : ℝ in Ioi 0, psiTrueMixedIntegrand Y t v) =
      ∫ v : ℝ in Ioi 0, ∫ t : ℝ, psiTrueMixedIntegrand Y t v := by
  exact integral_integral_swap (integrable_psiTrueMixedIntegrand hY)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.psiMixedEnvelope
#print axioms GoldbachContinuous22.psiTrueMixedIntegrand
#print axioms GoldbachContinuous22.leftChiPoint_im
#print axioms GoldbachContinuous22.gammaContourPoint_left_eq
#print axioms GoldbachContinuous22.Gamma_halfline_exponential_bound
#print axioms GoldbachContinuous22.norm_gammaContourFactor_left_le
#print axioms GoldbachContinuous22.psiMixedEnvelope_nonneg
#print axioms GoldbachContinuous22.psiMixedEnvelope_joint_continuous
#print axioms GoldbachContinuous22.norm_psiTrueMixedIntegrand_le
#print axioms GoldbachContinuous22.neg_image_Iio_zero
#print axioms GoldbachContinuous22.integrable_abs_extension
#print axioms GoldbachContinuous22.integrable_exp_negative_abs
#print axioms GoldbachContinuous22.integrable_abs_mul_exp_negative_abs
#print axioms GoldbachContinuous22.integrable_linear_abs_exp_negative_abs
#print axioms GoldbachContinuous22.integrableOn_exp_one_sub
#print axioms GoldbachContinuous22.integrable_psiMixedEnvelope
#print axioms GoldbachContinuous22.continuousOn_psiTrueMixedIntegrand
#print axioms GoldbachContinuous22.integrable_psiTrueMixedIntegrand
#print axioms GoldbachContinuous22.psiTrueMixedIntegrand_fubini
