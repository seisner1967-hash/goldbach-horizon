import ZetaEulerDirect22
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/- SOURCE_ONLY. Genuine zeta reflection on the left open strip, with the
   domains and both nonvanishing statements derived. The quotient derivative
   uses the actual functional equation in a neighbourhood, not an assumed
   trace relation. The digamma integral and arithmetic prime-power series
   are still separate missing obligations. -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace GoldbachContinuous22

def contourChi (s : ℂ) : ℂ :=
  2 * (2 * Real.pi : ℂ) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
    Complex.cos (Real.pi * (1 - s) / 2)

theorem contourZeta_reflection {s : ℂ} (hs : s.re < 0) :
    riemannZeta s = contourChi s * riemannZeta (1 - s) := by
  have hneg : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hr
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hone : 1 - s ≠ 1 := by
    intro hn
    have hr := congrArg Complex.re hn
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  have h := riemannZeta_one_sub hneg hone
  simpa only [sub_sub_cancel, contourChi] using h

theorem contour_cos_ne_zero_in_left_strip {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    Complex.cos (Real.pi * (1 - s) / 2) ≠ 0 := by
  rw [Complex.cos_ne_zero_iff]
  intro k hk
  have hr := congrArg Complex.re hk
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.one_re, Complex.add_re,
    Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.one_im, mul_zero, zero_mul, sub_zero,
    add_zero] at hr
  norm_num at hr
  have hkpos : 0 < (k : ℝ) := by nlinarith [Real.pi_pos]
  have hklt : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt' : k < (1 : ℤ) := by exact_mod_cast hklt
  omega

theorem contourChi_ne_zero_in_left_strip {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) : contourChi s ≠ 0 := by
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hg : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)
  have hpow : (2 * Real.pi : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hbase]
    exact Complex.exp_ne_zero _
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    hpow) hg) (contour_cos_ne_zero_in_left_strip hs0 hs1)

theorem contourZeta_ne_zero_in_left_strip {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) : riemannZeta s ≠ 0 := by
  rw [contourZeta_reflection hs1]
  exact mul_ne_zero (contourChi_ne_zero_in_left_strip hs0 hs1)
    (contourZeta_ne_zero_on_right (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith))

theorem contourChi_differentiableAt {s : ℂ} (hs : s.re < 0) :
    DifferentiableAt ℂ contourChi s := by
  have hg : DifferentiableAt ℂ Complex.Gamma (1 - s) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp only [Complex.sub_re, Complex.one_re, Complex.neg_re,
        Complex.natCast_re] at hr
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  have hbase : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have harg : DifferentiableAt ℂ (fun w : ℂ => 1 - w) s :=
    hid.const_sub (1 : ℂ)
  have hf : DifferentiableAt ℂ
      (fun w : ℂ => (2 * Real.pi : ℂ) ^ (-(1 - w))) s :=
    harg.neg.const_cpow (c := (2 * Real.pi : ℂ)) (Or.inl hbase)
  have hgamma : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) s :=
    hg.comp s harg
  have hcos : DifferentiableAt ℂ (fun w : ℂ => Complex.cos (Real.pi * (1 - w) / 2)) s := by
    fun_prop
  unfold contourChi
  exact ((hf.const_mul 2).mul hgamma).mul hcos

/-- The exact reflected logarithmic derivative for the genuine zeta. -/
theorem contourZeta_logDeriv_reflection {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv contourChi s / contourChi s -
        deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
  have hch := contourChi_differentiableAt hs1
  have hw : 1 - s ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  have hz := differentiableAt_riemannZeta hw
  have hdcomp := hz.hasDerivAt.comp s ((hasDerivAt_id s).const_sub (1 : ℂ))
  have hdprod := hch.hasDerivAt.mul hdcomp
  have heq : (fun w : ℂ => contourChi w * riemannZeta (1 - w)) =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs1]
      with w hw
    exact (contourZeta_reflection hw).symm
  have hder : deriv riemannZeta s =
      deriv contourChi s * riemannZeta (1 - s) -
        contourChi s * deriv riemannZeta (1 - s) := by
    have hd := (hdprod.congr_of_eventuallyEq heq.symm).deriv
    simpa only [Function.comp_apply, mul_neg_one, mul_neg, mul_one,
      ← sub_eq_add_neg] using hd
  rw [hder, contourZeta_reflection hs1]
  have hχ0 := contourChi_ne_zero_in_left_strip hs0 hs1
  have hζ0 := contourZeta_ne_zero_on_right (s := 1 - s) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  field_simp [hχ0, hζ0]

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourChi
#print axioms GoldbachContinuous22.contourZeta_reflection
#print axioms GoldbachContinuous22.contour_cos_ne_zero_in_left_strip
#print axioms GoldbachContinuous22.contourChi_ne_zero_in_left_strip
#print axioms GoldbachContinuous22.contourZeta_ne_zero_in_left_strip
#print axioms GoldbachContinuous22.contourChi_differentiableAt
#print axioms GoldbachContinuous22.contourZeta_logDeriv_reflection
