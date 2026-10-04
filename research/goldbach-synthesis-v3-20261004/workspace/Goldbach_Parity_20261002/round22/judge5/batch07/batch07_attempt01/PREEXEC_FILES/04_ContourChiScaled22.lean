import ContourChiPsi22
import Mathlib.MeasureTheory.Function.Jacobian

/-! SOURCE ONLY. The Jacobian 2 of u=2v is paid explicitly and the genuine
paired P1 integrability is transported. This does not exchange a contour
integral with the v integral and does not claim C5. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def contourPsiScaledKernel (s : ℂ) (v : ℝ) : ℂ :=
  (Complex.exp (-(1 - s) * (v : ℂ)) + Complex.exp (-(2 + s) * (v : ℂ)) -
    2 * Complex.exp (-2 * (v : ℂ))) / (1 - Complex.exp (-2 * (v : ℂ)))

def leftChiPoint (t : ℝ) : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem scaleTwo_image_Ioi :
    (fun v : ℝ => 2 * v) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mul_pos (by norm_num : (0 : ℝ) < 2) hv
  · intro hu
    refine ⟨u / 2, div_pos hu (by norm_num), ?_⟩
    ring

theorem scaleTwo_injOn_Ioi : InjOn (fun v : ℝ => 2 * v) (Ioi (0 : ℝ)) := by
  intro v hv w hw h
  linarith

theorem contourPsiPair_scaleTwo (s : ℂ) (v : ℝ) :
    |(2 : ℝ)| • contourPsiPairIntegrand s (2 * v) = contourPsiScaledKernel s v := by
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
  unfold contourPsiPairIntegrand contourPsiScaledKernel
  have hA : -((1 - s) / 2) * ((2 * v : ℝ) : ℂ) = -(1 - s) * (v : ℂ) := by
    push_cast <;> ring
  have hB : -(1 + s / 2) * ((2 * v : ℝ) : ℂ) = -(2 + s) * (v : ℂ) := by
    push_cast <;> ring
  have hE : -((2 * v : ℝ) : ℂ) = -2 * (v : ℂ) := by
    push_cast <;> ring
  rw [hA, hB, hE]
  by_cases hd : 1 - Complex.exp (-2 * (v : ℂ)) = 0
  · simp only [hd, mul_zero, div_zero]
  · field_simp [hd] <;> ring

theorem integrableOn_contourPsiScaledKernel {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    IntegrableOn (contourPsiScaledKernel s) (Ioi (0 : ℝ)) := by
  have hp : IntegrableOn (contourPsiPairIntegrand s)
      ((fun v : ℝ => 2 * v) '' Ioi (0 : ℝ)) := by
    rw [scaleTwo_image_Ioi]
    exact integrableOn_contourPsiPair hs0 hs1
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun v hv => (by
      simpa only [mul_one] using (hasDerivAt_id v).const_mul (2 : ℝ) :
        HasDerivAt (fun w : ℝ => 2 * w) 2 v).hasDerivWithinAt)
    scaleTwo_injOn_Ioi (contourPsiPairIntegrand s)).mp hp
  simpa only [contourPsiPair_scaleTwo] using h

theorem contourPsiPair_integral_eq_scaled (s : ℂ) :
    (∫ u : ℝ in Ioi 0, contourPsiPairIntegrand s u) =
      ∫ v : ℝ in Ioi 0, contourPsiScaledKernel s v := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun v hv => (by
      simpa only [mul_one] using (hasDerivAt_id v).const_mul (2 : ℝ) :
        HasDerivAt (fun w : ℝ => 2 * w) 2 v).hasDerivWithinAt)
    scaleTwo_injOn_Ioi (contourPsiPairIntegrand s)
  simpa only [scaleTwo_image_Ioi, contourPsiPair_scaleTwo] using h

theorem contourChi_logDeriv_eq_scaled_integral {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    deriv contourChi s / contourChi s =
      (Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ) + 1 / s +
        ∫ v : ℝ in Ioi 0, contourPsiScaledKernel s v := by
  rw [contourChi_logDeriv_eq_pair_integral hs0 hs1,
    contourPsiPair_integral_eq_scaled]

theorem leftChiPoint_re (t : ℝ) : (leftChiPoint t).re = -(1 / 2 : ℝ) := by
  simp only [leftChiPoint, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
    Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem contourPsiScaledKernel_left_line (t v : ℝ) :
    contourPsiScaledKernel (leftChiPoint t) v =
      (Complex.exp ((-(3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ)) +
        Complex.exp ((-(3 / 2 : ℂ) - (t : ℂ) * Complex.I) * (v : ℂ)) -
          2 * Complex.exp (-2 * (v : ℂ))) /
          (1 - Complex.exp (-2 * (v : ℂ))) := by
  unfold contourPsiScaledKernel leftChiPoint
  rw [show -(1 - (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      -(3 / 2 : ℂ) + (t : ℂ) * Complex.I by ring,
    show -(2 + (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      -(3 / 2 : ℂ) - (t : ℂ) * Complex.I by ring]

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourPsiScaledKernel
#print axioms GoldbachContinuous22.leftChiPoint
#print axioms GoldbachContinuous22.scaleTwo_image_Ioi
#print axioms GoldbachContinuous22.scaleTwo_injOn_Ioi
#print axioms GoldbachContinuous22.contourPsiPair_scaleTwo
#print axioms GoldbachContinuous22.integrableOn_contourPsiScaledKernel
#print axioms GoldbachContinuous22.contourPsiPair_integral_eq_scaled
#print axioms GoldbachContinuous22.contourChi_logDeriv_eq_scaled_integral
#print axioms GoldbachContinuous22.leftChiPoint_re
#print axioms GoldbachContinuous22.contourPsiScaledKernel_left_line
