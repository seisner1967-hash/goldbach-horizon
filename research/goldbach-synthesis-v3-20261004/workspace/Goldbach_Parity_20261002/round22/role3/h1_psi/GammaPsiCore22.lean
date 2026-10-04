import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecificLimits.Basic

/-! SOURCE ONLY. These objects use the actual complex Gamma function.
The Beta quotient is constructed before its limit; no digamma integral or
dominated-convergence conclusion is assumed. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def gammaPsi (z : ℂ) : ℂ := deriv Complex.Gamma z / Complex.Gamma z

def betaGammaRatio (z w : ℂ) : ℂ :=
  Complex.Gamma z * Complex.Gamma (w + 1) / Complex.Gamma (z + w)

def betaStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def betaDifferenceIntegrand (z : ℂ) (w t : ℝ) : ℂ :=
  ((t : ℂ) ^ (z - 1) - 1) * (1 - (t : ℂ)) ^ ((w : ℂ) - 1)

theorem gammaDifferentiableAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  refine Complex.differentiableAt_Gamma z ?_
  intro n hn
  have hre := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem deriv_Gamma_add_one_right {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.Gamma (z + 1) =
      Complex.Gamma z + z * deriv Complex.Gamma z := by
  have hz1 : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have heq : (fun w : ℂ => Complex.Gamma (w + 1)) =ᶠ[𝓝 z]
      (fun w => w * Complex.Gamma w) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually
      (Ioi_mem_nhds hz)] with w hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw
    exact Complex.Gamma_add_one w hw0
  have hleft := (gammaDifferentiableAt_of_re_pos hz1).hasDerivAt.comp z
    ((hasDerivAt_id z).add_const 1)
  have hright := ((hasDerivAt_id z).mul
    (gammaDifferentiableAt_of_re_pos hz).hasDerivAt).congr_of_eventuallyEq heq
  simpa only [mul_one, one_mul] using hleft.unique hright

theorem gammaPsi_add_one {z : ℂ} (hz : 0 < z.re) :
    gammaPsi (z + 1) = gammaPsi z + 1 / z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hg0 := Complex.Gamma_ne_zero_of_re_pos hz
  unfold gammaPsi
  rw [deriv_Gamma_add_one_right hz, Complex.Gamma_add_one z hz0]
  field_simp [hz0, hg0] <;> ring

theorem gammaPsi_one : gammaPsi 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  simp [gammaPsi, Complex.hasDerivAt_Gamma_one.deriv, Complex.Gamma_one]

theorem betaGammaRatio_zero {z : ℂ} (hz : 0 < z.re) :
    betaGammaRatio z 0 = 1 := by
  simp [betaGammaRatio, Complex.Gamma_one, Complex.Gamma_ne_zero_of_re_pos hz]

theorem hasDerivAt_betaGammaRatio_zero {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (betaGammaRatio z)
      (-(Real.eulerMascheroniConstant : ℂ) - gammaPsi z) 0 := by
  have hnGamma : HasDerivAt (fun w : ℂ => Complex.Gamma (w + 1))
      (-(Real.eulerMascheroniConstant : ℂ)) 0 := by
    have hOne : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ))
        ((0 : ℂ) + 1) := by
      simpa only [zero_add] using Complex.hasDerivAt_Gamma_one
    simpa only [zero_add, mul_one] using
      hOne.comp 0 ((hasDerivAt_id (0 : ℂ)).add_const 1)
  have hdGamma : HasDerivAt (fun w : ℂ => Complex.Gamma (z + w))
      (deriv Complex.Gamma z) 0 := by
    have hAt : HasDerivAt Complex.Gamma (deriv Complex.Gamma z) (z + (0 : ℂ)) := by
      simpa only [add_zero] using (gammaDifferentiableAt_of_re_pos hz).hasDerivAt
    simpa only [add_zero, zero_add, mul_one] using hAt.comp 0
        ((hasDerivAt_const (0 : ℂ) z).add (hasDerivAt_id (0 : ℂ)))
  have hquot : HasDerivAt (betaGammaRatio z)
      ((Complex.Gamma z * -(Real.eulerMascheroniConstant : ℂ) * Complex.Gamma z -
        Complex.Gamma z * deriv Complex.Gamma z) / Complex.Gamma z ^ 2) 0 := by
    simpa only [betaGammaRatio, zero_add, add_zero, Complex.Gamma_one, mul_one] using
      (hnGamma.const_mul (Complex.Gamma z)).div hdGamma
        (by simpa only [add_zero] using Complex.Gamma_ne_zero_of_re_pos hz)
  apply hquot.congr_deriv
  unfold gammaPsi
  field_simp [Complex.Gamma_ne_zero_of_re_pos hz] <;> ring

theorem hasDerivAt_betaGammaRatio_real_zero {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℝ => betaGammaRatio z w)
      (-(Real.eulerMascheroniConstant : ℂ) - gammaPsi z) 0 := by
  exact (hasDerivAt_betaGammaRatio_zero hz).comp_ofReal

theorem betaStep_pos (n : ℕ) : 0 < betaStep n := by
  unfold betaStep
  positivity

theorem betaStep_le_one (n : ℕ) : betaStep n ≤ 1 := by
  unfold betaStep
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem betaStep_tendsto_zero : Tendsto betaStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem betaStep_tendsto_zero_right : Tendsto betaStep atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨betaStep_tendsto_zero, Eventually.of_forall betaStep_pos⟩

theorem betaGammaRatio_eq_mul_betaIntegral {z : ℂ} (hz : 0 < z.re)
    {w : ℝ} (hw : 0 < w) :
    betaGammaRatio z w = (w : ℂ) * Complex.betaIntegral z w := by
  have hwC : 0 < (w : ℂ).re := hw
  have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hsum : 0 < (z + (w : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  unfold betaGammaRatio
  rw [Complex.Gamma_add_one (w : ℂ) hw0]
  have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral hz hwC
  rw [show Complex.Gamma z * ((w : ℂ) * Complex.Gamma w) =
    (w : ℂ) * (Complex.Gamma z * Complex.Gamma w) by ring, hb]
  field_simp [Complex.Gamma_ne_zero_of_re_pos hsum] <;> ring

theorem betaDifference_eq_ratio {z : ℂ} (hz : 0 < z.re)
    {w : ℝ} (hw : 0 < w) :
    Complex.betaIntegral z w - Complex.betaIntegral 1 w =
      (betaGammaRatio z w - 1) / (w : ℂ) := by
  rw [Complex.betaIntegral_symm (w : ℂ) 1,
    Complex.betaIntegral_eval_one_right (show 0 < (w : ℂ).re from hw),
    betaGammaRatio_eq_mul_betaIntegral hz hw]
  field_simp [Complex.ofReal_ne_zero.mpr hw.ne'] <;> ring

theorem betaDifference_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.betaIntegral z (betaStep n) -
      Complex.betaIntegral 1 (betaStep n)) atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - gammaPsi z)) := by
  have h := (hasDerivAt_betaGammaRatio_real_zero hz).tendsto_slope_zero_right.comp
    betaStep_tendsto_zero_right
  apply h.congr'
  filter_upwards with n
  rw [betaDifference_eq_ratio hz (betaStep_pos n), zero_add, betaGammaRatio_zero hz]
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem betaDifference_eq_integral {z : ℂ} (hz : 0 < z.re)
    {w : ℝ} (hw : 0 < w) :
    Complex.betaIntegral z w - Complex.betaIntegral 1 w =
      ∫ t : ℝ in 0..1, betaDifferenceIntegrand z w t := by
  have hi := Complex.betaIntegral_convergent hz (show 0 < (w : ℂ).re from hw)
  have h1 := Complex.betaIntegral_convergent
    (show 0 < (1 : ℂ).re by norm_num) (show 0 < (w : ℂ).re from hw)
  unfold Complex.betaIntegral
  rw [← intervalIntegral.integral_sub hi h1]
  congr 1
  funext t
  simp only [betaDifferenceIntegrand, sub_self, Complex.cpow_zero, one_mul, sub_mul]

end GoldbachContinuous22

#print axioms GoldbachContinuous22.gammaPsi
#print axioms GoldbachContinuous22.betaGammaRatio
#print axioms GoldbachContinuous22.betaStep
#print axioms GoldbachContinuous22.betaDifferenceIntegrand
#print axioms GoldbachContinuous22.gammaDifferentiableAt_of_re_pos
#print axioms GoldbachContinuous22.deriv_Gamma_add_one_right
#print axioms GoldbachContinuous22.gammaPsi_add_one
#print axioms GoldbachContinuous22.gammaPsi_one
#print axioms GoldbachContinuous22.betaGammaRatio_zero
#print axioms GoldbachContinuous22.hasDerivAt_betaGammaRatio_zero
#print axioms GoldbachContinuous22.hasDerivAt_betaGammaRatio_real_zero
#print axioms GoldbachContinuous22.betaStep_pos
#print axioms GoldbachContinuous22.betaStep_le_one
#print axioms GoldbachContinuous22.betaStep_tendsto_zero
#print axioms GoldbachContinuous22.betaStep_tendsto_zero_right
#print axioms GoldbachContinuous22.betaGammaRatio_eq_mul_betaIntegral
#print axioms GoldbachContinuous22.betaDifference_eq_ratio
#print axioms GoldbachContinuous22.betaDifference_tendsto
#print axioms GoldbachContinuous22.betaDifference_eq_integral
