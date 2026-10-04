import GammaPsiBetaLimit22
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! SOURCE ONLY. The exp(-u) image, signed derivative, absolute Jacobian,
and transported integrability are proved before the digamma identity P1. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def psiExpIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  (Complex.exp (-(u : ℂ)) - Complex.exp (-z * (u : ℂ))) /
    (1 - Complex.exp (-(u : ℂ)))

theorem expNeg_image_Ioi :
    (fun u : ℝ => Real.exp (-u)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)⟩
  · intro ht
    refine ⟨-Real.log t, ?_, ?_⟩
    · exact neg_pos.mpr ((Real.log_neg_iff ht.1).mpr ht.2)
    · simpa only [neg_neg] using Real.exp_log ht.1

theorem hasDerivAt_expNeg (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-u)) u := by
  simpa only [mul_neg, mul_one] using (hasDerivAt_id u).neg.exp

theorem expNeg_injOn_Ioi : InjOn (fun u : ℝ => Real.exp (-u)) (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  have h := Real.exp_injective huv
  linarith

theorem ofReal_exp_cpow (u : ℝ) (w : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ w = Complex.exp ((u : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

theorem expNeg_mul_cpow (z : ℂ) (u : ℝ) :
    (Real.exp (-u) : ℂ) * (Real.exp (-u) : ℂ) ^ (z - 1) =
      Complex.exp (-z * (u : ℂ)) := by
  rw [ofReal_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem psiBeta_exp_jacobian (z : ℂ) (u : ℝ) :
    |(-Real.exp (-u))| • psiBetaIntegrand z (Real.exp (-u)) = psiExpIntegrand z u := by
  rw [abs_neg, abs_of_pos (Real.exp_pos (-u)), Complex.real_smul]
  unfold psiBetaIntegrand psiExpIntegrand
  rw [← mul_div_assoc, mul_sub, mul_one, expNeg_mul_cpow,
    Complex.ofReal_exp, Complex.ofReal_neg]

theorem psiBeta_integral_eq_exp_integral (z : ℂ) :
    (∫ t : ℝ in 0..1, psiBetaIntegrand z t) =
      ∫ u : ℝ in Ioi 0, psiExpIntegrand z u := by
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo, ← expNeg_image_Ioi]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u hu => (hasDerivAt_expNeg u).hasDerivWithinAt)
    expNeg_injOn_Ioi (psiBetaIntegrand z)
  simpa only [psiBeta_exp_jacobian] using h

theorem integrableOn_psiExpIntegrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (psiExpIntegrand z) (Ioi 0) := by
  have hbeta : IntegrableOn (psiBetaIntegrand z)
      ((fun u : ℝ => Real.exp (-u)) '' Ioi (0 : ℝ)) := by
    rw [expNeg_image_Ioi]
    exact integrableOn_Ioc_iff_integrableOn_Ioo.mp (integrableOn_psiBetaIntegrand hz)
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u hu => (hasDerivAt_expNeg u).hasDerivWithinAt)
    expNeg_injOn_Ioi (psiBetaIntegrand z)).mp hbeta
  simpa only [psiBeta_exp_jacobian] using h

theorem gammaPsi_eq_exp_integral {z : ℂ} (hz : 0 < z.re) :
    gammaPsi z = -(Real.eulerMascheroniConstant : ℂ) +
      ∫ u : ℝ in Ioi 0, psiExpIntegrand z u := by
  rw [gammaPsi_eq_beta_integral hz, psiBeta_integral_eq_exp_integral]

end GoldbachContinuous22

#print axioms GoldbachContinuous22.psiExpIntegrand
#print axioms GoldbachContinuous22.expNeg_image_Ioi
#print axioms GoldbachContinuous22.hasDerivAt_expNeg
#print axioms GoldbachContinuous22.expNeg_injOn_Ioi
#print axioms GoldbachContinuous22.ofReal_exp_cpow
#print axioms GoldbachContinuous22.expNeg_mul_cpow
#print axioms GoldbachContinuous22.psiBeta_exp_jacobian
#print axioms GoldbachContinuous22.psiBeta_integral_eq_exp_integral
#print axioms GoldbachContinuous22.integrableOn_psiExpIntegrand
#print axioms GoldbachContinuous22.gammaPsi_eq_exp_integral
