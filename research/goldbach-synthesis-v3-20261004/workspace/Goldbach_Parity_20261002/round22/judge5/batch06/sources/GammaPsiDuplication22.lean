import GammaPsiCore22
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! SOURCE ONLY. This is differentiation of the actual Legendre Gamma
identity on its positive-real domain, with every denominator nonzero. -/

noncomputable section
open Set Filter
open scoped Topology

namespace GoldbachContinuous22

theorem deriv_Gamma_duplication {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
      Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2) =
    (2 * deriv Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) -
      2 * Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * Complex.log 2) *
      (Real.sqrt Real.pi : ℂ) := by
  have hzhalf : 0 < (z + 1 / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hz2 : 0 < (2 * z).re := by
    have htwoRe : (2 : ℂ).re = (2 : ℝ) := rfl
    have htwoIm : (2 : ℂ).im = 0 := rfl
    simp only [Complex.mul_re, htwoRe, htwoIm, zero_mul, sub_zero]
    exact mul_pos (by norm_num) hz
  have hleft := (gammaDifferentiableAt_of_re_pos hz).hasDerivAt.mul
    ((gammaDifferentiableAt_of_re_pos hzhalf).hasDerivAt.comp z
      ((hasDerivAt_id z).add_const (1 / 2 : ℂ)))
  have hGamma := (gammaDifferentiableAt_of_re_pos hz2).hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (2 : ℂ))
  have hpower := ((hasDerivAt_const z (1 : ℂ)).sub
    ((hasDerivAt_id z).const_mul (2 : ℂ))).const_cpow
      (c := (2 : ℂ)) (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hright := (hGamma.mul hpower).mul_const (Real.sqrt Real.pi : ℂ)
  have heq : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =ᶠ[𝓝 z]
      (fun w => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) *
        (Real.sqrt Real.pi : ℂ)) :=
    Eventually.of_forall Complex.Gamma_mul_Gamma_add_half
  have h := hleft.unique (hright.congr_of_eventuallyEq heq)
  simp only [Function.comp_apply, id_eq, mul_one, zero_sub] at h
  linear_combination h

theorem gammaPsi_duplication {z : ℂ} (hz : 0 < z.re) :
    gammaPsi z + gammaPsi (z + 1 / 2) =
      2 * gammaPsi (2 * z) - 2 * (Real.log 2 : ℂ) := by
  have hzhalf : 0 < (z + 1 / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hz2 : 0 < (2 * z).re := by
    have htwoRe : (2 : ℂ).re = (2 : ℝ) := rfl
    have htwoIm : (2 : ℂ).im = 0 := rfl
    simp only [Complex.mul_re, htwoRe, htwoIm, zero_mul, sub_zero]
    exact mul_pos (by norm_num) hz
  have hΓ0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hΓhalf := Complex.Gamma_ne_zero_of_re_pos hzhalf
  have hΓ2 := Complex.Gamma_ne_zero_of_re_pos hz2
  have hp : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact Complex.exp_ne_zero _
  have hsq : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    gammaPsi z + gammaPsi (z + 1 / 2) =
        (deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
          Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2)) /
          (Complex.Gamma z * Complex.Gamma (z + 1 / 2)) := by
      unfold gammaPsi
      rw [div_add_div _ _ hΓ0 hΓhalf]
    _ = ((2 * deriv Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) -
          2 * Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * Complex.log 2) *
          (Real.sqrt Real.pi : ℂ)) /
          (Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) *
            (Real.sqrt Real.pi : ℂ)) := by
      rw [deriv_Gamma_duplication hz, Complex.Gamma_mul_Gamma_add_half]
    _ = 2 * gammaPsi (2 * z) - 2 * (Real.log 2 : ℂ) := by
      rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
      unfold gammaPsi
      field_simp [hΓ2, hp, hsq] <;> ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.deriv_Gamma_duplication
#print axioms GoldbachContinuous22.gammaPsi_duplication
