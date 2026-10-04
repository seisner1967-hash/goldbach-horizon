import PsiMixedFubini22
import MellinThermalInversion22

/-! SOURCE ONLY. This module evaluates the actual paired digamma contour
integral by Mellin inversion, and evaluates the 1/s term by the genuine
complex-rate Laplace identity at Gamma(1). Every mixed integrability premise
is constructed. The frozen batch06 dependencies have no hypothetical PASS.
No final C5 equality, free interchange or free contour bound is an input. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def c5MellinMode (Y w t : ℝ) : ℂ :=
  gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
    Complex.exp (-(w : ℂ) * leftChiPoint t)

def c5MellinImageKernel (Y v : ℝ) : ℂ :=
  ((Real.exp (-v) : ℂ) * thermalTest Y (Real.exp (-v)) +
    (Real.exp (-2 * v) : ℂ) * thermalTest Y (Real.exp v) -
    2 * (Real.exp (-2 * v) : ℂ) * thermalTest Y 1) /
    ((1 - Real.exp (-2 * v) : ℝ) : ℂ)

theorem c5MellinMode_continuous (Y w : ℝ) : Continuous (c5MellinMode Y w) := by
  have hG := gammaContourFactor_continuous Y (-(1 / 2 : ℝ)) 1 le_rfl
  have he : Continuous (fun t : ℝ => Complex.exp (-(w : ℂ) * leftChiPoint t)) := by
    unfold leftChiPoint
    fun_prop
  exact hG.mul he

theorem norm_c5MellinMode (Y w t : ℝ) :
    ‖c5MellinMode Y w t‖ = Real.exp (w / 2) *
      ‖gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t‖ := by
  have he : ‖Complex.exp (-(w : ℂ) * leftChiPoint t)‖ =
      Real.exp ((-(w : ℂ) * leftChiPoint t).re) := by
    rw [Complex.norm_eq_abs, Complex.abs_exp]
  have hre : (-(w : ℂ) * leftChiPoint t).re = w / 2 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, leftChiPoint_re, mul_zero, sub_zero]
    ring
  rw [c5MellinMode, norm_mul, he, hre, mul_comm]

theorem integrable_c5MellinMode {Y : ℝ} (hY : 1 ≤ Y) (w : ℝ) :
    Integrable (c5MellinMode Y w) := by
  have hG := (gammaContourFactor_vertical_integrable hY le_rfl
    (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2)).norm
  apply (hG.const_mul (Real.exp (w / 2))).mono'
    (c5MellinMode_continuous Y w).aestronglyMeasurable
  exact Eventually.of_forall (fun t => (norm_c5MellinMode Y w t).le)

/-- The positive-real branch x=exp(w) is explicitly reduced to exp(-w*s). -/
theorem c5MellinMode_inversion {Y : ℝ} (hY : 1 ≤ Y) (w : ℝ) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ, c5MellinMode Y w t) =
      thermalTest Y (Real.exp w) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have h := thermalTest_gamma_inversion hY le_rfl
    (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2) (Real.exp_pos w)
  have hpoint (t : ℝ) : leftChiPoint t =
      ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    unfold leftChiPoint
    push_cast
    ring
  have hpower (t : ℝ) : (Real.exp w : ℂ) ^ (-leftChiPoint t) =
      Complex.exp (-(w : ℂ) * leftChiPoint t) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero w)),
      ← Complex.ofReal_log (Real.exp_pos w).le, Real.log_exp]
    congr 1
    ring
  have heq : (fun t : ℝ => c5MellinMode Y w t) =
      (fun t : ℝ => (Real.exp w : ℂ) ^ (-((-(1 / 2 : ℝ) : ℂ) +
          (t : ℂ) * Complex.I)) *
        ((Y : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Complex.Gamma ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I + 1))) := by
    funext t
    simp only [← hpoint t, hpower]
    unfold c5MellinMode gammaContourFactor
    rw [gammaContourPoint_left_eq, weightedGammaTerm_eq_cpow hY0]
    ring
  simpa only [← heq] using h

theorem c5Mixed_pointwise (Y t v : ℝ) :
    psiTrueMixedIntegrand Y t v =
      ((Real.exp (-v) : ℂ) * c5MellinMode Y (-v) t +
        (Real.exp (-2 * v) : ℂ) * c5MellinMode Y v t -
        2 * (Real.exp (-2 * v) : ℂ) * c5MellinMode Y 0 t) /
        ((1 - Real.exp (-2 * v) : ℝ) : ℂ) := by
  have hA : Complex.exp (-(1 - leftChiPoint t) * (v : ℂ)) =
      (Real.exp (-v) : ℂ) * Complex.exp (-((-v : ℝ) : ℂ) * leftChiPoint t) := by
    rw [show -(1 - leftChiPoint t) * (v : ℂ) =
      ((-v : ℝ) : ℂ) + -((-v : ℝ) : ℂ) * leftChiPoint t by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
  have hB : Complex.exp (-(2 + leftChiPoint t) * (v : ℂ)) =
      (Real.exp (-2 * v) : ℂ) * Complex.exp (-(v : ℂ) * leftChiPoint t) := by
    rw [show -(2 + leftChiPoint t) * (v : ℂ) =
      ((-2 * v : ℝ) : ℂ) + -(v : ℂ) * leftChiPoint t by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
  have hE : Complex.exp (-2 * (v : ℂ)) = (Real.exp (-2 * v) : ℂ) := by
    rw [show -2 * (v : ℂ) = ((-2 * v : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  unfold psiTrueMixedIntegrand contourPsiScaledKernel c5MellinMode
  simp only [hA, hB, hE, Complex.ofReal_neg, Complex.ofReal_zero, neg_zero, zero_mul,
    Complex.exp_zero, mul_one, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem c5Mixed_inner_mellin {Y : ℝ} (hY : 1 ≤ Y) (v : ℝ) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ, psiTrueMixedIntegrand Y t v) =
      c5MellinImageKernel Y v := by
  have hA := (integrable_c5MellinMode hY (-v)).const_mul (Real.exp (-v) : ℂ)
  have hB := (integrable_c5MellinMode hY v).const_mul (Real.exp (-2 * v) : ℂ)
  have hC := (integrable_c5MellinMode hY 0).const_mul
    (2 * (Real.exp (-2 * v) : ℂ))
  simp_rw [c5Mixed_pointwise]
  rw [integral_div, integral_sub (hA.add hB) hC, integral_add hA hB,
    integral_mul_left, integral_mul_left, integral_mul_left]
  have ha := c5MellinMode_inversion hY (-v)
  have hb := c5MellinMode_inversion hY v
  have hc := c5MellinMode_inversion hY 0
  calc
    _ = ((Real.exp (-v) : ℂ) * ((1 / (2 * Real.pi)) •
          (∫ t : ℝ, c5MellinMode Y (-v) t)) +
        (Real.exp (-2 * v) : ℂ) * ((1 / (2 * Real.pi)) •
          (∫ t : ℝ, c5MellinMode Y v t)) -
        2 * (Real.exp (-2 * v) : ℂ) * ((1 / (2 * Real.pi)) •
          (∫ t : ℝ, c5MellinMode Y 0 t))) /
          ((1 - Real.exp (-2 * v) : ℝ) : ℂ) := by
      simp only [Complex.real_smul]
      ring
    _ = c5MellinImageKernel Y v := by
      rw [ha, hb, hc, Real.exp_zero]
      rfl

theorem integrable_c5MellinImageKernel {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (c5MellinImageKernel Y) (Ioi (0 : ℝ)) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have h := ((integrable_psiTrueMixedIntegrand hY0).integral_prod_right).smul
    (1 / (2 * Real.pi) : ℝ)
  apply h.congr
  exact Eventually.of_forall (fun v => c5Mixed_inner_mellin hY v)

/-- The interchange uses the genuine paid paired majorant; the numerator
    has never been split into nonintegrable v terms near zero. -/
theorem c5Mixed_global_mellin {Y : ℝ} (hY : 1 ≤ Y) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, ∫ v : ℝ in Ioi 0, psiTrueMixedIntegrand Y t v) =
      ∫ v : ℝ in Ioi 0, c5MellinImageKernel Y v := by
  rw [psiTrueMixedIntegrand_fubini (lt_of_lt_of_le zero_lt_one hY),
    ← integral_smul]
  exact integral_congr_ae (Eventually.of_forall (fun v => c5Mixed_inner_mellin hY v))

def c5PoleMixed (Y t v : ℝ) : ℂ :=
  gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
    Complex.exp (leftChiPoint t * (v : ℂ))

theorem norm_c5PoleMixed (Y t v : ℝ) :
    ‖c5PoleMixed Y t v‖ = ‖gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t‖ *
      Real.exp (-(1 / 2 : ℝ) * v) := by
  rw [c5PoleMixed, norm_mul, norm_cexp_real_mul, leftChiPoint_re]

theorem integrable_c5PoleMixed {Y : ℝ} (hY : 1 ≤ Y) :
    Integrable (fun p : ℝ × ℝ => c5PoleMixed Y p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hG := (gammaContourFactor_vertical_integrable hY le_rfl
    (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2)).norm
  have hv := integrableOn_exp_negative_scale (a := (1 / 2 : ℝ)) (by norm_num)
  have hm : Continuous (fun p : ℝ × ℝ => c5PoleMixed Y p.1 p.2) := by
    have hg := (gammaContourFactor_continuous Y (-(1 / 2 : ℝ)) 1 le_rfl).comp
      continuous_fst
    have he : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (leftChiPoint p.1 * (p.2 : ℂ))) := by
      unfold leftChiPoint
      fun_prop
    exact hg.mul he
  apply (hG.prod_mul hv).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => (norm_c5PoleMixed Y p.1 p.2).le)

theorem c5PoleMixed_inner_laplace (Y t : ℝ) :
    (∫ v : ℝ in Ioi 0, c5PoleMixed Y t v) =
      -(gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t / leftChiPoint t) := by
  have hz : 0 < (-leftChiPoint t).re := by
    rw [Complex.neg_re, leftChiPoint_re]
    norm_num
  have h := complex_rate_laplace_identity (s := (1 : ℂ)) (by norm_num) hz
  have hclean : (∫ v : ℝ in Ioi 0, Complex.exp (leftChiPoint t * (v : ℂ))) =
      -(1 / leftChiPoint t) := by
    simpa only [laplaceTransform, laplaceIntegrand, neg_neg, sub_self,
      Complex.cpow_zero, mul_one, Complex.Gamma_one, Complex.cpow_neg,
      Complex.cpow_one, inv_neg, one_div] using h
  rw [c5PoleMixed, integral_mul_left, hclean]
  ring

theorem c5Pole_integrable {Y : ℝ} (hY : 1 ≤ Y) :
    Integrable (fun t : ℝ => gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t /
      leftChiPoint t) := by
  have h := (integrable_c5PoleMixed hY).integral_prod_left
  have hn : Integrable (fun t : ℝ => -(gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t /
      leftChiPoint t)) := h.congr (Eventually.of_forall (fun t => c5PoleMixed_inner_laplace Y t))
  simpa only [neg_neg] using hn.neg

theorem c5Pole_global_mellin {Y : ℝ} (hY : 1 ≤ Y) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ,
      gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t / leftChiPoint t) =
      -(∫ v : ℝ in Ioi 0, thermalTest Y (Real.exp (-v))) := by
  have hs := integral_integral_swap (integrable_c5PoleMixed hY)
  have ht : (fun t : ℝ => ∫ v : ℝ in Ioi 0, c5PoleMixed Y t v) =
      (fun t : ℝ => -(gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t / leftChiPoint t)) :=
    funext (c5PoleMixed_inner_laplace Y)
  have hv : ∀ v : ℝ, (1 / (2 * Real.pi)) •
      (∫ t : ℝ, c5PoleMixed Y t v) = thermalTest Y (Real.exp (-v)) := by
    intro v
    have heq : (fun t : ℝ => c5PoleMixed Y t v) = c5MellinMode Y (-v) := by
      funext t
      unfold c5PoleMixed c5MellinMode
      rw [Complex.ofReal_neg, neg_neg, mul_comm (v : ℂ) (leftChiPoint t)]
    rw [heq]
    exact c5MellinMode_inversion hY (-v)
  have h := congrArg (fun z : ℂ => (1 / (2 * Real.pi)) • z) hs
  rw [ht, integral_neg, smul_neg, ← integral_smul] at h
  have heq : (∫ v : ℝ in Ioi 0,
      (1 / (2 * Real.pi)) • (∫ t : ℝ, c5PoleMixed Y t v)) =
      ∫ v : ℝ in Ioi 0, thermalTest Y (Real.exp (-v)) :=
    integral_congr_ae (Eventually.of_forall hv)
  rw [heq] at h
  exact neg_eq_iff_eq_neg.mp h

theorem c5Chi_weighted_pointwise (Y t : ℝ) :
    gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
      (deriv contourChi (leftChiPoint t) / contourChi (leftChiPoint t)) =
      ((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
        gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t +
      gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t / leftChiPoint t +
      ∫ v : ℝ in Ioi 0, psiTrueMixedIntegrand Y t v := by
  have hA : -1 < (leftChiPoint t).re := by rw [leftChiPoint_re]; norm_num
  have hB : (leftChiPoint t).re < 0 := by rw [leftChiPoint_re]; norm_num
  rw [contourChi_logDeriv_eq_scaled_integral hA hB]
  rw [psiTrueMixedIntegrand, integral_mul_left]
  ring

theorem c5Chi_weighted_integrable {Y : ℝ} (hY : 1 ≤ Y) :
    Integrable (fun t : ℝ => gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
      (deriv contourChi (leftChiPoint t) / contourChi (leftChiPoint t))) := by
  have hG := (gammaContourFactor_vertical_integrable hY le_rfl
    (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2)).const_mul
      ((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ))
  have hp := c5Pole_integrable hY
  have hm := (integrable_psiTrueMixedIntegrand (lt_of_lt_of_le zero_lt_one hY)).integral_prod_left
  exact ((hG.add hp).add hm).congr
    (Eventually.of_forall (fun t => (c5Chi_weighted_pointwise Y t).symm))

/-- Exact pre-Arch C5. The next source proves the log(2) correction and
    the value of the two thermal integrals, rather than assuming them. -/
theorem c5Chi_preArch_identity {Y : ℝ} (hY : 1 ≤ Y) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ,
      gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
        (deriv contourChi (leftChiPoint t) / contourChi (leftChiPoint t))) =
      ((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) * thermalTest Y 1 -
      (∫ v : ℝ in Ioi 0, thermalTest Y (Real.exp (-v))) +
      (∫ v : ℝ in Ioi 0, c5MellinImageKernel Y v) := by
  have hG := gammaContourFactor_vertical_integrable hY le_rfl
    (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2)
  have hC := hG.const_mul ((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ))
  have hP := c5Pole_integrable hY
  have hM := (integrable_psiTrueMixedIntegrand (lt_of_lt_of_le zero_lt_one hY)).integral_prod_left
  simp_rw [c5Chi_weighted_pointwise]
  rw [integral_add (hC.add hP) hM, integral_add hC hP,
    integral_mul_left, smul_add, smul_add,
    c5Pole_global_mellin hY, c5Mixed_global_mellin hY]
  have h1 := c5MellinMode_inversion hY 0
  simp only [c5MellinMode, Complex.ofReal_zero, neg_zero, zero_mul,
    Complex.exp_zero, mul_one, Real.exp_zero] at h1
  have hconst : (1 / (2 * Real.pi)) •
      (((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
        (∫ t : ℝ, gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t)) =
      ((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) * thermalTest Y 1 := by
    calc
      _ = ((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) *
          ((1 / (2 * Real.pi)) •
            (∫ t : ℝ, gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t)) := by
        simp only [Complex.real_smul]
        ring
      _ = _ := by rw [h1]
  rw [hconst]
  ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.c5MellinMode
#print axioms GoldbachContinuous22.c5MellinImageKernel
#print axioms GoldbachContinuous22.c5MellinMode_continuous
#print axioms GoldbachContinuous22.norm_c5MellinMode
#print axioms GoldbachContinuous22.integrable_c5MellinMode
#print axioms GoldbachContinuous22.c5MellinMode_inversion
#print axioms GoldbachContinuous22.c5Mixed_pointwise
#print axioms GoldbachContinuous22.c5Mixed_inner_mellin
#print axioms GoldbachContinuous22.integrable_c5MellinImageKernel
#print axioms GoldbachContinuous22.c5Mixed_global_mellin
#print axioms GoldbachContinuous22.c5PoleMixed
#print axioms GoldbachContinuous22.norm_c5PoleMixed
#print axioms GoldbachContinuous22.integrable_c5PoleMixed
#print axioms GoldbachContinuous22.c5PoleMixed_inner_laplace
#print axioms GoldbachContinuous22.c5Pole_integrable
#print axioms GoldbachContinuous22.c5Pole_global_mellin
#print axioms GoldbachContinuous22.c5Chi_weighted_pointwise
#print axioms GoldbachContinuous22.c5Chi_weighted_integrable
#print axioms GoldbachContinuous22.c5Chi_preArch_identity
