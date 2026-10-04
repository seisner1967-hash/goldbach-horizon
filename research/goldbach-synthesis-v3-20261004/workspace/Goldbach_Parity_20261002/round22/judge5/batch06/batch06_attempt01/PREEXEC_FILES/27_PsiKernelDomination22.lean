import PsiKernelEnvelope22
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-! SOURCE ONLY. The positive-v bounds below are consequences of the genuine
paired exponential numerator, its value at zero and its derivative. No kernel
bound, integrability exchange or contour factor bound is taken as a premise. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def psiSlopeCoeff (t : ℝ) : ℂ := -(3 / 2 : ℂ) + (t : ℂ) * Complex.I

def psiKernelNumerator (t v : ℝ) : ℂ :=
  Complex.exp (psiSlopeCoeff t * (v : ℂ)) +
    Complex.exp (psiSlopeCoeff (-t) * (v : ℂ)) -
      2 * Complex.exp (-2 * (v : ℂ))

theorem psiSlopeCoeff_re (t : ℝ) : (psiSlopeCoeff t).re = -(3 / 2 : ℝ) := by
  have hthreeRe : (3 : ℂ).re = (3 : ℝ) := rfl
  simp only [psiSlopeCoeff, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
    hthreeRe, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem norm_psiSlopeCoeff_le (t : ℝ) : ‖psiSlopeCoeff t‖ ≤ 3 / 2 + |t| := by
  have h := norm_add_le (-(3 / 2 : ℂ)) ((t : ℂ) * Complex.I)
  simpa only [psiSlopeCoeff, norm_neg, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_ofNat] using h

theorem norm_cexp_real_mul (c : ℂ) (v : ℝ) :
    ‖Complex.exp (c * (v : ℂ))‖ = Real.exp (c.re * v) := by
  rw [Complex.norm_eq_abs, Complex.abs_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem hasDerivAt_cexp_real_mul (c : ℂ) (v : ℝ) :
    HasDerivAt (fun w : ℝ => Complex.exp (c * (w : ℂ)))
      (Complex.exp (c * (v : ℂ)) * c) v := by
  have h : HasDerivAt (fun w : ℝ => c * (w : ℂ)) c v := by
    simpa only [Complex.ofReal_one, mul_one] using
      (hasDerivAt_id v).ofReal_comp.const_mul c
  exact h.cexp

theorem norm_cexp_derivative_le_coeff {c : ℂ} {v : ℝ}
    (hc : c.re ≤ 0) (hv : 0 ≤ v) :
    ‖Complex.exp (c * (v : ℂ)) * c‖ ≤ ‖c‖ := by
  rw [norm_mul, norm_cexp_real_mul]
  have he : Real.exp (c.re * v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc hv)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg c)

theorem psiKernelNumerator_zero (t : ℝ) : psiKernelNumerator t 0 = 0 := by
  simp only [psiKernelNumerator, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

theorem hasDerivAt_psiKernelNumerator (t v : ℝ) :
    HasDerivAt (psiKernelNumerator t)
      (Complex.exp (psiSlopeCoeff t * (v : ℂ)) * psiSlopeCoeff t +
        Complex.exp (psiSlopeCoeff (-t) * (v : ℂ)) * psiSlopeCoeff (-t) -
          2 * (Complex.exp (-2 * (v : ℂ)) * (-2))) v := by
  exact ((hasDerivAt_cexp_real_mul (psiSlopeCoeff t) v).add
    (hasDerivAt_cexp_real_mul (psiSlopeCoeff (-t)) v)).sub
      ((hasDerivAt_cexp_real_mul (-2) v).const_mul 2)

theorem norm_deriv_psiKernelNumerator_le (t : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ‖deriv (psiKernelNumerator t) v‖ ≤ 7 + 2 * |t| := by
  let A := Complex.exp (psiSlopeCoeff t * (v : ℂ)) * psiSlopeCoeff t
  let B := Complex.exp (psiSlopeCoeff (-t) * (v : ℂ)) * psiSlopeCoeff (-t)
  let C := Complex.exp (-2 * (v : ℂ)) * (-2)
  have ha : ‖A‖ ≤ 3 / 2 + |t| :=
    (norm_cexp_derivative_le_coeff (c := psiSlopeCoeff t)
      (by rw [psiSlopeCoeff_re]; norm_num) hv).trans
      (norm_psiSlopeCoeff_le t)
  have hb : ‖B‖ ≤ 3 / 2 + |t| := by
    simpa only [abs_neg] using
      (norm_cexp_derivative_le_coeff (c := psiSlopeCoeff (-t))
        (by rw [psiSlopeCoeff_re]; norm_num) hv).trans
        (norm_psiSlopeCoeff_le (-t))
  have hc : ‖C‖ ≤ 2 := by
    simpa only [C, norm_neg, Complex.norm_ofNat] using
      norm_cexp_derivative_le_coeff (c := (-2 : ℂ)) (by norm_num) hv
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [(hasDerivAt_psiKernelNumerator t v).deriv]
  change ‖A + B - 2 * C‖ ≤ 7 + 2 * |t|
  calc
    ‖A + B - 2 * C‖ ≤ ‖A + B‖ + ‖2 * C‖ := norm_sub_le _ _
    _ ≤ (‖A‖ + ‖B‖) + 2 * ‖C‖ := by
      rw [norm_mul, htwo]
      exact add_le_add_right (norm_add_le A B) _
    _ ≤ 7 + 2 * |t| := by linarith

theorem norm_psiKernelNumerator_le_linear (t : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ‖psiKernelNumerator t v‖ ≤ (7 + 2 * |t|) * v := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hasDerivAt_psiKernelNumerator t u).differentiableAt)
    (fun u hu => norm_deriv_psiKernelNumerator_le t hu)
    (convex_Ici (0 : ℝ)) (show (0 : ℝ) ∈ Ici 0 from le_rfl) hv
  simpa only [psiKernelNumerator_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg hv] using h

theorem norm_psiKernelNumerator_le_exponential (t : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ‖psiKernelNumerator t v‖ ≤ 4 * Real.exp (-(3 / 2 : ℝ) * v) := by
  have ha : ‖Complex.exp (psiSlopeCoeff t * (v : ℂ))‖ =
      Real.exp (-(3 / 2 : ℝ) * v) := by rw [norm_cexp_real_mul, psiSlopeCoeff_re]
  have hb : ‖Complex.exp (psiSlopeCoeff (-t) * (v : ℂ))‖ =
      Real.exp (-(3 / 2 : ℝ) * v) := by rw [norm_cexp_real_mul, psiSlopeCoeff_re]
  have hc : ‖Complex.exp (-2 * (v : ℂ))‖ ≤
      Real.exp (-(3 / 2 : ℝ) * v) := by
    have htwoRe : (2 : ℂ).re = (2 : ℝ) := rfl
    rw [norm_cexp_real_mul]
    simp only [Complex.neg_re, htwoRe]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  unfold psiKernelNumerator
  calc
    _ ≤ ‖Complex.exp (psiSlopeCoeff t * (v : ℂ)) +
        Complex.exp (psiSlopeCoeff (-t) * (v : ℂ))‖ +
          ‖2 * Complex.exp (-2 * (v : ℂ))‖ := norm_sub_le _ _
    _ ≤ (‖Complex.exp (psiSlopeCoeff t * (v : ℂ))‖ +
        ‖Complex.exp (psiSlopeCoeff (-t) * (v : ℂ))‖) +
          2 * ‖Complex.exp (-2 * (v : ℂ))‖ := by
      rw [norm_mul, htwo]
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ 4 * Real.exp (-(3 / 2 : ℝ) * v) := by rw [ha, hb]; linarith

theorem psiDenominator_ge_fraction {v : ℝ} (hv : 0 < v) :
    2 * v / (1 + 2 * v) ≤ 1 - Real.exp (-2 * v) := by
  have hd : 0 < 1 + 2 * v := by linarith
  have hexp : 1 + 2 * v ≤ Real.exp (2 * v) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 * v)
  have hi : Real.exp (-2 * v) ≤ 1 / (1 + 2 * v) := by
    rw [show -2 * v = -(2 * v) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hd hexp
  have heq : 2 * v / (1 + 2 * v) = 1 - 1 / (1 + 2 * v) := by
    field_simp [hd.ne'] <;> ring
  rw [heq]
  linarith

theorem psiDenominator_ge_near {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    v / 2 ≤ 1 - Real.exp (-2 * v) := by
  apply le_trans _ (psiDenominator_ge_fraction hv)
  apply (le_div_iff₀ (by linarith : 0 < 1 + 2 * v)).mpr
  nlinarith

theorem psiDenominator_ge_tail {v : ℝ} (hv : 1 ≤ v) :
    1 / 2 ≤ 1 - Real.exp (-2 * v) := by
  apply le_trans _ (psiDenominator_ge_fraction (by linarith : 0 < v))
  apply (le_div_iff₀ (by linarith : 0 < 1 + 2 * v)).mpr
  nlinarith

theorem psiDenominator_pos {v : ℝ} (hv : 0 < v) :
    0 < 1 - Real.exp (-2 * v) := by
  have h : Real.exp (-2 * v) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem norm_complex_psiDenominator {v : ℝ} (hv : 0 < v) :
    ‖1 - Complex.exp (-2 * (v : ℂ))‖ = 1 - Real.exp (-2 * v) := by
  have he : -2 * (v : ℂ) = ((-2 * v : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp]
  have hd : 1 - (Real.exp (-2 * v) : ℂ) = ((1 - Real.exp (-2 * v) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (psiDenominator_pos hv)]

theorem contourPsiScaledKernel_left_eq_numerator (t v : ℝ) :
    contourPsiScaledKernel (leftChiPoint t) v =
      psiKernelNumerator t v / (1 - Complex.exp (-2 * (v : ℂ))) := by
  rw [contourPsiScaledKernel_left_line]
  have hneg : psiSlopeCoeff (-t) = -(3 / 2 : ℂ) - (t : ℂ) * Complex.I := by
    unfold psiSlopeCoeff
    rw [Complex.ofReal_neg]
    ring
  rw [psiKernelNumerator, hneg]
  rfl

theorem norm_contourPsiScaledKernel_left_le_near (t : ℝ) {v : ℝ}
    (hv : 0 < v) (hv1 : v ≤ 1) :
    ‖contourPsiScaledKernel (leftChiPoint t) v‖ ≤ 14 + 4 * |t| := by
  rw [contourPsiScaledKernel_left_eq_numerator, norm_div,
    norm_complex_psiDenominator hv]
  apply (div_le_iff₀ (psiDenominator_pos hv)).mpr
  have hn := norm_psiKernelNumerator_le_linear t hv.le
  have hd := psiDenominator_ge_near hv hv1
  have hC : 0 ≤ 14 + 4 * |t| := by positivity
  have hm := mul_le_mul_of_nonneg_left hd hC
  nlinarith

theorem norm_contourPsiScaledKernel_left_le_tail (t : ℝ) {v : ℝ}
    (hv : 1 ≤ v) :
    ‖contourPsiScaledKernel (leftChiPoint t) v‖ ≤
      8 * Real.exp (-(3 / 2 : ℝ) * v) := by
  have hv0 : 0 < v := by linarith
  rw [contourPsiScaledKernel_left_eq_numerator, norm_div,
    norm_complex_psiDenominator hv0]
  apply (div_le_iff₀ (psiDenominator_pos hv0)).mpr
  have hn := norm_psiKernelNumerator_le_exponential t hv0.le
  have hd := psiDenominator_ge_tail hv
  have hm := mul_le_mul_of_nonneg_left hd
    (by positivity : 0 ≤ 8 * Real.exp (-(3 / 2 : ℝ) * v))
  nlinarith

theorem norm_contourPsiScaledKernel_left_le_envelope (t : ℝ) {v : ℝ}
    (hv : 0 < v) :
    ‖contourPsiScaledKernel (leftChiPoint t) v‖ ≤ psiKernelEnvelope t v := by
  by_cases hv1 : v ≤ 1
  · exact (norm_contourPsiScaledKernel_left_le_near t hv hv1).trans
      (psiKernelEnvelope_ge_near hv1)
  · exact (norm_contourPsiScaledKernel_left_le_tail t (lt_of_not_ge hv1).le).trans
      (psiKernelEnvelope_ge_tail t v)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.psiSlopeCoeff
#print axioms GoldbachContinuous22.psiKernelNumerator
#print axioms GoldbachContinuous22.psiSlopeCoeff_re
#print axioms GoldbachContinuous22.norm_psiSlopeCoeff_le
#print axioms GoldbachContinuous22.norm_cexp_real_mul
#print axioms GoldbachContinuous22.hasDerivAt_cexp_real_mul
#print axioms GoldbachContinuous22.norm_cexp_derivative_le_coeff
#print axioms GoldbachContinuous22.psiKernelNumerator_zero
#print axioms GoldbachContinuous22.hasDerivAt_psiKernelNumerator
#print axioms GoldbachContinuous22.norm_deriv_psiKernelNumerator_le
#print axioms GoldbachContinuous22.norm_psiKernelNumerator_le_linear
#print axioms GoldbachContinuous22.norm_psiKernelNumerator_le_exponential
#print axioms GoldbachContinuous22.psiDenominator_ge_fraction
#print axioms GoldbachContinuous22.psiDenominator_ge_near
#print axioms GoldbachContinuous22.psiDenominator_ge_tail
#print axioms GoldbachContinuous22.psiDenominator_pos
#print axioms GoldbachContinuous22.norm_complex_psiDenominator
#print axioms GoldbachContinuous22.contourPsiScaledKernel_left_eq_numerator
#print axioms GoldbachContinuous22.norm_contourPsiScaledKernel_left_le_near
#print axioms GoldbachContinuous22.norm_contourPsiScaledKernel_left_le_tail
#print axioms GoldbachContinuous22.norm_contourPsiScaledKernel_left_le_envelope
