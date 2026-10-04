import GammaPsiReflection22
import GammaPsiIntegral22
import ZetaReflection22
import Mathlib.MeasureTheory.Integral.Bochner

/-! SOURCE ONLY revision09, distinct from all frozen author/Judge batches. Every identity below
uses ROLE4's actual contourChi. The sine form is an equality of functions,
and the paired integral inherits actual P1 integrability; no Fubini conclusion
or freely supplied majorant is an input. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

theorem contourChi_eq_sine (s : ℂ) :
    contourChi s = 2 * (2 * Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
      Complex.sin ((Real.pi : ℂ) * (s / 2)) := by
  unfold contourChi
  rw [show -(1 - s) = s - 1 by ring,
    show (Real.pi : ℂ) * (1 - s) / 2 =
      (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * (s / 2) by ring,
    Complex.cos_pi_div_two_sub]

theorem deriv_contourChi_sine {s : ℂ} (hs1 : s.re < 0) :
    deriv contourChi s =
      2 * (2 * Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.sin ((Real.pi : ℂ) * (s / 2)) * Complex.log (2 * Real.pi) -
      2 * (2 * Real.pi : ℂ) ^ (s - 1) * deriv Complex.Gamma (1 - s) *
        Complex.sin ((Real.pi : ℂ) * (s / 2)) +
      2 * (2 * Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
        Complex.cos ((Real.pi : ℂ) * (s / 2)) * ((Real.pi : ℂ) / 2) := by
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hgpos : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hp := ((hasDerivAt_id s).sub_const (1 : ℂ)).const_cpow
    (c := (2 * Real.pi : ℂ)) (Or.inl hbase)
  have hg := (gammaDifferentiableAt_of_re_pos hgpos).hasDerivAt.comp s
    ((hasDerivAt_id s).const_sub (1 : ℂ))
  have hlin := ((hasDerivAt_id s).div_const (2 : ℂ)).const_mul (Real.pi : ℂ)
  have ht := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * (s / 2))).comp s hlin
  have hd := (((hp.const_mul (2 : ℂ)).mul hg).mul ht).congr_of_eventuallyEq
    (Eventually.of_forall contourChi_eq_sine)
  have h := hd.deriv
  simp only [Function.comp_apply, id_eq, mul_one, one_mul, zero_add] at h
  linear_combination h

theorem contourChi_logDeriv_direct {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    deriv contourChi s / contourChi s =
      Complex.log (2 * Real.pi) - gammaPsi (1 - s) +
        ((Real.pi : ℂ) / 2) * Complex.cos ((Real.pi : ℂ) * (s / 2)) /
          Complex.sin ((Real.pi : ℂ) * (s / 2)) := by
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hp : (2 * Real.pi : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hbase]
    exact Complex.exp_ne_zero _
  have hg : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)
  have ht := sin_half_pi_ne_zero_on_left_strip hs0 hs1
  -- Normalize the field expression before substituting opaque functions.
  have hquotient (a g dg z c L k : ℂ) (ha : a ≠ 0) (hg0 : g ≠ 0)
      (hz : z ≠ 0) :
      (2 * a * g * z * L - 2 * a * dg * z + 2 * a * g * c * k) /
          (2 * a * g * z) = L - dg / g + k * c / z := by
    field_simp [ha, hg0, hz] <;> ring
  rw [deriv_contourChi_sine hs1, contourChi_eq_sine]
  unfold gammaPsi
  exact hquotient ((2 * Real.pi : ℂ) ^ (s - 1)) (Complex.Gamma (1 - s))
    (deriv Complex.Gamma (1 - s)) (Complex.sin ((Real.pi : ℂ) * (s / 2)))
    (Complex.cos ((Real.pi : ℂ) * (s / 2))) (Complex.log (2 * Real.pi))
    ((Real.pi : ℂ) / 2) hp hg ht

theorem complex_log_two_pi :
    Complex.log (2 * Real.pi : ℂ) = (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
  have hcast : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast <;> ring
  rw [hcast, ← Complex.ofReal_log (mul_pos (by norm_num : (0 : ℝ) < 2)
      Real.pi_pos).le,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero, Complex.ofReal_add]

theorem contourChi_logDeriv_symmetric {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    deriv contourChi s / contourChi s =
      (Real.log Real.pi : ℂ) + 1 / s - gammaPsi ((1 - s) / 2) / 2 -
        gammaPsi (1 + s / 2) / 2 := by
  have hA : 0 < ((1 - s) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hd := gammaPsi_duplication hA
  rw [show (1 - s) / 2 + 1 / 2 = 1 - s / 2 by ring,
    show 2 * ((1 - s) / 2) = 1 - s by ring] at hd
  have hr := gammaPsi_shift_reflection hs0 hs1
  rw [contourChi_logDeriv_direct hs0 hs1, complex_log_two_pi]
  linear_combination (1 / 2 : ℂ) * hd + hr

def contourPsiPairIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  (Complex.exp (-((1 - s) / 2) * (u : ℂ)) +
    Complex.exp (-(1 + s / 2) * (u : ℂ)) - 2 * Complex.exp (-(u : ℂ))) /
    (2 * (1 - Complex.exp (-(u : ℂ))))

theorem contourPsiPair_eq_negPsi (s : ℂ) (u : ℝ) :
    contourPsiPairIntegrand s u =
      -(psiExpIntegrand ((1 - s) / 2) u + psiExpIntegrand (1 + s / 2) u) / 2 := by
  unfold contourPsiPairIntegrand psiExpIntegrand
  by_cases hd : 1 - Complex.exp (-(u : ℂ)) = 0
  · simp only [hd, mul_zero, div_zero, add_zero, neg_zero, zero_div]
  · field_simp [hd] <;> ring

theorem integrableOn_contourPsiPair {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    IntegrableOn (contourPsiPairIntegrand s) (Ioi (0 : ℝ)) := by
  have hA : 0 < ((1 - s) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hB := (Gamma_shift_arguments_re_pos hs0 hs1).2
  have h := (((integrableOn_psiExpIntegrand hA).add
    (integrableOn_psiExpIntegrand hB)).neg).div_const (2 : ℂ)
  apply h.congr
  exact Eventually.of_forall (fun u => (contourPsiPair_eq_negPsi s u).symm)

theorem contourPsiPair_integral {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    (∫ u : ℝ in Ioi 0, contourPsiPairIntegrand s u) =
      -((∫ u : ℝ in Ioi 0, psiExpIntegrand ((1 - s) / 2) u) +
        (∫ u : ℝ in Ioi 0, psiExpIntegrand (1 + s / 2) u)) / 2 := by
  have hA : 0 < ((1 - s) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hB := (Gamma_shift_arguments_re_pos hs0 hs1).2
  simp_rw [contourPsiPair_eq_negPsi]
  rw [integral_div, integral_neg,
    integral_add (integrableOn_psiExpIntegrand hA) (integrableOn_psiExpIntegrand hB)]

theorem contourChi_logDeriv_eq_pair_integral {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    deriv contourChi s / contourChi s =
      (Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ) + 1 / s +
        ∫ u : ℝ in Ioi 0, contourPsiPairIntegrand s u := by
  have hA : 0 < ((1 - s) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith
  have hB := (Gamma_shift_arguments_re_pos hs0 hs1).2
  rw [contourChi_logDeriv_symmetric hs0 hs1,
    gammaPsi_eq_exp_integral hA, gammaPsi_eq_exp_integral hB,
    contourPsiPair_integral hs0 hs1]
  ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourChi_eq_sine
#print axioms GoldbachContinuous22.deriv_contourChi_sine
#print axioms GoldbachContinuous22.contourChi_logDeriv_direct
#print axioms GoldbachContinuous22.complex_log_two_pi
#print axioms GoldbachContinuous22.contourChi_logDeriv_symmetric
#print axioms GoldbachContinuous22.contourPsiPairIntegrand
#print axioms GoldbachContinuous22.contourPsiPair_eq_negPsi
#print axioms GoldbachContinuous22.integrableOn_contourPsiPair
#print axioms GoldbachContinuous22.contourPsiPair_integral
#print axioms GoldbachContinuous22.contourChi_logDeriv_eq_pair_integral
