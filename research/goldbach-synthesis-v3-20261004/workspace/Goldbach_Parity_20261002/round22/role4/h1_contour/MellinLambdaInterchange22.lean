import ZetaEulerLambda22
import MellinThermalInversion22
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/- SOURCE_ONLY. Actual Lambda coefficients and actual G=Y^s Gamma(s+1).
   The vertical coefficient norm is constant; its proved summable norm times
   the proved integrable Gamma norm is the dominateur. The arithmetic side of
   C4 is obtained by genuine Mellin inversion, not a free Fubini premise.
   The chi/psi side, contour residues, and the global H1 identity remain open. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def thermalPrimeIntegrand (Y c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  contourLambdaTerm n (gammaContourPoint c 1 t) * gammaContourFactor Y c 1 t

theorem contourLambdaTerm_norm_on_vertical (n : ℕ) (c t : ℝ) :
    ‖contourLambdaTerm n (gammaContourPoint c 1 t)‖ =
      ‖contourLambdaTerm n (c : ℂ)‖ := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [contourLambdaTerm, contourLambdaWeight, not_isPrimePow_zero]
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hp (s : ℂ) : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [← Complex.ofReal_natCast, Complex.norm_eq_abs,
        Complex.abs_cpow_eq_rpow_re_of_pos hnR, Complex.neg_re]
    simp only [contourLambdaTerm, norm_mul, hp, gammaContourPoint,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem thermalPrimeIntegrand_continuous (Y c : ℝ) (n : ℕ)
    (hc : -(1 / 2) ≤ c) : Continuous (thermalPrimeIntegrand Y c n) := by
  classical
  by_cases hn : n = 0
  · subst n
    simpa only [thermalPrimeIntegrand, contourLambdaTerm, contourLambdaWeight,
      if_neg not_isPrimePow_zero, Complex.ofReal_zero, zero_mul] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hp : Continuous (fun t : ℝ => -gammaContourPoint c 1 t) := by
      unfold gammaContourPoint
      fun_prop
    exact (continuous_const.mul (hp.const_cpow (Or.inl hnC))).mul
      (gammaContourFactor_continuous Y c 1 hc)

theorem norm_thermalPrimeIntegrand (Y c : ℝ) (n : ℕ) (t : ℝ) :
    ‖thermalPrimeIntegrand Y c n t‖ =
      ‖contourLambdaTerm n (c : ℂ)‖ * ‖gammaContourFactor Y c 1 t‖ := by
  rw [thermalPrimeIntegrand, norm_mul, contourLambdaTerm_norm_on_vertical]

theorem thermalPrimeIntegrand_integrable {Y c : ℝ} (hY : 1 ≤ Y)
    (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2) (n : ℕ) :
    Integrable (thermalPrimeIntegrand Y c n) := by
  have hbound := (gammaContourFactor_vertical_integrable hY hc0 hc1).norm.const_mul
    ‖contourLambdaTerm n (c : ℂ)‖
  apply hbound.mono' (thermalPrimeIntegrand_continuous Y c n hc0).aestronglyMeasurable
  filter_upwards with t
  exact (norm_thermalPrimeIntegrand Y c n t).le

theorem thermalPrimeIntegrand_integral_norm_summable {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖thermalPrimeIntegrand Y c n t‖) := by
  have hcoeff := contourLambdaTerm_norm_summable
    (s := (c : ℂ)) (by simpa only [Complex.ofReal_re] using hc)
  have h := hcoeff.mul_right (∫ t : ℝ, ‖gammaContourFactor Y c 1 t‖)
  refine h.congr fun n => ?_
  simp_rw [norm_thermalPrimeIntegrand]
  rw [integral_mul_left]

theorem thermalPrimeIntegrand_norm_summable_at {c : ℝ} (hc : 1 < c)
    (Y t : ℝ) : Summable (fun n : ℕ => ‖thermalPrimeIntegrand Y c n t‖) := by
  simpa only [norm_thermalPrimeIntegrand] using
    (contourLambdaTerm_norm_summable (s := (c : ℂ))
      (by simpa only [Complex.ofReal_re] using hc)).mul_right
        ‖gammaContourFactor Y c 1 t‖

theorem thermalPrimeIntegrand_tsum_integrable {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => ∑' n : ℕ, thermalPrimeIntegrand Y c n t) := by
  have hc0 : -(1 / 2) ≤ c := by linarith
  have hmeas : StronglyMeasurable
      (fun t : ℝ => ∑' n : ℕ, thermalPrimeIntegrand Y c n t) := by
    apply stronglyMeasurable_of_tendsto (u := (atTop : Filter ℕ))
      (f := fun k t => ∑ n ∈ Finset.range k, thermalPrimeIntegrand Y c n t)
    · intro k
      exact (continuous_finset_sum (Finset.range k)
        (fun n _ => thermalPrimeIntegrand_continuous Y c n hc0)).stronglyMeasurable
    · apply tendsto_pi_nhds.mpr
      intro t
      exact (thermalPrimeIntegrand_norm_summable_at hc Y t).of_norm.hasSum.tendsto_sum_nat
  have hG := gammaContourFactor_vertical_integrable hY hc0 hc1
  have hbound := hG.norm.const_mul (∑' n : ℕ, ‖contourLambdaTerm n (c : ℂ)‖)
  apply hbound.mono' hmeas.aestronglyMeasurable
  filter_upwards with t
  calc
    _ ≤ ∑' n : ℕ, ‖thermalPrimeIntegrand Y c n t‖ :=
      norm_tsum_le_tsum_norm (thermalPrimeIntegrand_norm_summable_at hc Y t)
    _ = _ := by simp_rw [norm_thermalPrimeIntegrand]; rw [tsum_mul_right]

theorem thermalPrimeIntegrand_single_inversion {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) (n : ℕ) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ, thermalPrimeIntegrand Y c n t) =
      (contourLambdaWeight n : ℂ) * thermalTest Y (n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [thermalPrimeIntegrand, contourLambdaTerm, contourLambdaWeight,
      not_isPrimePow_zero, thermalTest, thermalUnitTest]
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
    have hc0 : -(1 / 2) ≤ c := by linarith
    have heq : thermalPrimeIntegrand Y c n =
        (fun t : ℝ => (contourLambdaWeight n : ℂ) *
          ((n : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
            ((Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
              Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I + 1)))) := by
      ext t
      simp only [thermalPrimeIntegrand, contourLambdaTerm, gammaContourFactor,
        weightedGammaTerm_eq_cpow hY0, gammaContourPoint, one_mul]
      ring
    rw [heq, integral_mul_left, ← mul_smul_comm]
    congr 1
    exact thermalTest_gamma_inversion hY hc0 hc1 hnR

/-- Paid arithmetic integral/sum exchange with the actual thermal test. -/
theorem thermalPrimeIntegrand_full_inversion {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, ∑' n : ℕ, thermalPrimeIntegrand Y c n t) =
      ∑' n : ℕ, (contourLambdaWeight n : ℂ) * thermalTest Y (n : ℝ) := by
  have hc0 : -(1 / 2) ≤ c := by linarith
  have hexchange := integral_tsum_of_summable_integral_norm
    (thermalPrimeIntegrand_integrable hY hc0 hc1)
    (thermalPrimeIntegrand_integral_norm_summable hY hc hc1)
  rw [← hexchange, ← tsum_const_smul'']
  exact tsum_congr (thermalPrimeIntegrand_single_inversion hY hc hc1)

theorem thermalZeta_arithmetic_integrand_eq {c : ℝ} (hc : 1 < c) (Y t : ℝ) :
    gammaContourFactor Y c 1 t *
      (-(deriv riemannZeta (gammaContourPoint c 1 t) /
        riemannZeta (gammaContourPoint c 1 t))) =
      ∑' n : ℕ, thermalPrimeIntegrand Y c n t := by
  have hs : 1 < (gammaContourPoint c 1 t).re := by
    simpa only [gammaContourPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hc
  rw [contourZeta_logDeriv_direct_Lambda hs, neg_neg]
  simp only [thermalPrimeIntegrand, contourLambdaTerm, tsum_mul_right]
  ring

/-- The actual G times zeta logarithmic derivative is integrable on the right
    line. Gamma integrability alone is not used as a surrogate for this claim. -/
theorem thermalZeta_arithmetic_vertical_integrable {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => gammaContourFactor Y c 1 t *
      (-(deriv riemannZeta (gammaContourPoint c 1 t) /
        riemannZeta (gammaContourPoint c 1 t)))) := by
  apply (thermalPrimeIntegrand_tsum_integrable hY hc hc1).congr
  filter_upwards with t
  exact (thermalZeta_arithmetic_integrand_eq hc Y t).symm

theorem thermalZeta_arithmetic_vertical_inversion {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, gammaContourFactor Y c 1 t *
        (-(deriv riemannZeta (gammaContourPoint c 1 t) /
          riemannZeta (gammaContourPoint c 1 t)))) =
      ∑' n : ℕ, (contourLambdaWeight n : ℂ) * thermalTest Y (n : ℝ) := by
  have heq : (fun t : ℝ => gammaContourFactor Y c 1 t *
      (-(deriv riemannZeta (gammaContourPoint c 1 t) /
        riemannZeta (gammaContourPoint c 1 t)))) =
      (fun t : ℝ => ∑' n : ℕ, thermalPrimeIntegrand Y c n t) :=
    funext (thermalZeta_arithmetic_integrand_eq hc Y)
  rw [heq]
  exact thermalPrimeIntegrand_full_inversion hY hc hc1

end GoldbachContinuous22

#print axioms GoldbachContinuous22.thermalPrimeIntegrand
#print axioms GoldbachContinuous22.contourLambdaTerm_norm_on_vertical
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_continuous
#print axioms GoldbachContinuous22.norm_thermalPrimeIntegrand
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_integrable
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_integral_norm_summable
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_norm_summable_at
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_tsum_integrable
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_single_inversion
#print axioms GoldbachContinuous22.thermalPrimeIntegrand_full_inversion
#print axioms GoldbachContinuous22.thermalZeta_arithmetic_integrand_eq
#print axioms GoldbachContinuous22.thermalZeta_arithmetic_vertical_integrable
#print axioms GoldbachContinuous22.thermalZeta_arithmetic_vertical_inversion
