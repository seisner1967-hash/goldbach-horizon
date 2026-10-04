import GammaPsiDuplication22
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! SOURCE ONLY, outside the frozen psi54 batch. Differentiation is performed
only at positive-real Gamma arguments, even though s/2 itself is negative. -/

noncomputable section
open Set Filter
open scoped Topology

namespace GoldbachContinuous22

theorem Gamma_shift_arguments_re_pos {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    0 < (1 - s / 2).re ∧ 0 < (1 + s / 2).re := by
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
  constructor <;> linarith

theorem sin_half_pi_ne_zero_on_left_strip {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
  have hs2 : s / 2 ≠ (0 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.zero_re] at hre
    linarith
  have hpos := Gamma_shift_arguments_re_pos hs0 hs1
  have hΓC := Complex.Gamma_ne_zero_of_re_pos hpos.1
  have hΓB := Complex.Gamma_ne_zero_of_re_pos hpos.2
  have hΓv : Complex.Gamma (s / 2) ≠ 0 := by
    intro h
    apply hΓB
    rw [show 1 + s / 2 = s / 2 + 1 by ring, Complex.Gamma_add_one _ hs2, h, mul_zero]
  intro hsin
  have h := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  rw [hsin, div_zero] at h
  exact mul_ne_zero hΓv hΓC h

theorem Gamma_shift_reflection {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    Complex.Gamma (1 - s / 2) * Complex.Gamma (1 + s / 2) =
      (Real.pi : ℂ) * (s / 2) / Complex.sin ((Real.pi : ℂ) * (s / 2)) := by
  have hs2 : s / 2 ≠ (0 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.zero_re] at hre
    linarith
  rw [show 1 + s / 2 = s / 2 + 1 by ring, Complex.Gamma_add_one _ hs2]
  calc
    Complex.Gamma (1 - s / 2) * ((s / 2) * Complex.Gamma (s / 2)) =
      (s / 2) * (Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2)) := by ring
    _ = (s / 2) * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (s / 2))) := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
    _ = _ := by ring

theorem deriv_Gamma_shift_reflection {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    (-deriv Complex.Gamma (1 - s / 2) * Complex.Gamma (1 + s / 2) +
      Complex.Gamma (1 - s / 2) * deriv Complex.Gamma (1 + s / 2)) / 2 =
      (((Real.pi : ℂ) / 2) * Complex.sin ((Real.pi : ℂ) * (s / 2)) -
        ((Real.pi : ℂ) * (s / 2)) * Complex.cos ((Real.pi : ℂ) * (s / 2)) *
          ((Real.pi : ℂ) / 2)) /
        Complex.sin ((Real.pi : ℂ) * (s / 2)) ^ 2 := by
  have hpos := Gamma_shift_arguments_re_pos hs0 hs1
  have hc := (gammaDifferentiableAt_of_re_pos hpos.1).hasDerivAt.comp s
    (((hasDerivAt_id s).div_const (2 : ℂ)).const_sub 1)
  have hb := (gammaDifferentiableAt_of_re_pos hpos.2).hasDerivAt.comp s
    ((hasDerivAt_const s (1 : ℂ)).add ((hasDerivAt_id s).div_const 2))
  have hleft := hc.mul hb
  have hlin := ((hasDerivAt_id s).div_const (2 : ℂ)).const_mul (Real.pi : ℂ)
  have hsin := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * (s / 2))).comp s hlin
  have hright := hlin.div hsin (sin_half_pi_ne_zero_on_left_strip hs0 hs1)
  have heq : (fun w : ℂ => Complex.Gamma (1 - w / 2) * Complex.Gamma (1 + w / 2))
      =ᶠ[𝓝 s] (fun w => (Real.pi : ℂ) * (w / 2) /
        Complex.sin ((Real.pi : ℂ) * (w / 2))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs0,
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs1] with w hw0 hw1
    exact Gamma_shift_reflection hw0 hw1
  have h := hleft.unique (hright.congr_of_eventuallyEq heq)
  simp only [mul_one, zero_add] at h
  linear_combination h

theorem gammaPsi_shift_reflection {s : ℂ} (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    -gammaPsi (1 - s / 2) / 2 + gammaPsi (1 + s / 2) / 2 =
      1 / s - ((Real.pi : ℂ) / 2) *
        Complex.cos ((Real.pi : ℂ) * (s / 2)) / Complex.sin ((Real.pi : ℂ) * (s / 2)) := by
  have hpos := Gamma_shift_arguments_re_pos hs0 hs1
  have hΓC := Complex.Gamma_ne_zero_of_re_pos hpos.1
  have hΓB := Complex.Gamma_ne_zero_of_re_pos hpos.2
  have hsin := sin_half_pi_ne_zero_on_left_strip hs0 hs1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs1; linarith
  calc
    -gammaPsi (1 - s / 2) / 2 + gammaPsi (1 + s / 2) / 2 =
        ((-deriv Complex.Gamma (1 - s / 2) * Complex.Gamma (1 + s / 2) +
          Complex.Gamma (1 - s / 2) * deriv Complex.Gamma (1 + s / 2)) / 2) /
          (Complex.Gamma (1 - s / 2) * Complex.Gamma (1 + s / 2)) := by
      unfold gammaPsi
      field_simp [hΓC, hΓB] <;> ring
    _ = _ := by
      rw [deriv_Gamma_shift_reflection hs0 hs1, Gamma_shift_reflection hs0 hs1]
      field_simp [hs, hπ, hsin] <;> ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.Gamma_shift_arguments_re_pos
#print axioms GoldbachContinuous22.sin_half_pi_ne_zero_on_left_strip
#print axioms GoldbachContinuous22.Gamma_shift_reflection
#print axioms GoldbachContinuous22.deriv_Gamma_shift_reflection
#print axioms GoldbachContinuous22.gammaPsi_shift_reflection
