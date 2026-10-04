import MellinLambdaInterchange22

/- SOURCE_ONLY. Complementary arithmetic term on the genuine left vertical
   line. The coefficients are the same direct Lambda weights, evaluated at
   1-s; inversion at x=1/n gives fY(1/n)/n, including the extra reciprocal.
   No chi integral, residue identity, or global trace is assumed or claimed. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def thermalDualPrimeIntegrand (Y d : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  contourLambdaTerm n (1 - gammaContourPoint d 1 t) * gammaContourFactor Y d 1 t

theorem contourLambdaTerm_reflected_norm (n : ℕ) (d t : ℝ) :
    ‖contourLambdaTerm n (1 - gammaContourPoint d 1 t)‖ =
      ‖contourLambdaTerm n ((1 - d : ℝ) : ℂ)‖ := by
  have heq : 1 - gammaContourPoint d 1 t = gammaContourPoint (1 - d) 1 (-t) := by
    ext <;> simp [gammaContourPoint] <;> ring
  rw [heq, contourLambdaTerm_norm_on_vertical]

theorem thermalDualPrimeIntegrand_continuous (Y d : ℝ) (n : ℕ)
    (hd : -(1 / 2) ≤ d) : Continuous (thermalDualPrimeIntegrand Y d n) := by
  classical
  by_cases hn : n = 0
  · subst n
    simpa only [thermalDualPrimeIntegrand, contourLambdaTerm, contourLambdaWeight,
      if_neg not_isPrimePow_zero, Complex.ofReal_zero, zero_mul] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hp : Continuous (fun t : ℝ => -(1 - gammaContourPoint d 1 t)) := by
      unfold gammaContourPoint
      fun_prop
    exact (continuous_const.mul (hp.const_cpow (Or.inl hnC))).mul
      (gammaContourFactor_continuous Y d 1 hd)

theorem norm_thermalDualPrimeIntegrand (Y d : ℝ) (n : ℕ) (t : ℝ) :
    ‖thermalDualPrimeIntegrand Y d n t‖ =
      ‖contourLambdaTerm n ((1 - d : ℝ) : ℂ)‖ * ‖gammaContourFactor Y d 1 t‖ := by
  rw [thermalDualPrimeIntegrand, norm_mul, contourLambdaTerm_reflected_norm]

theorem thermalDualPrimeIntegrand_integrable {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd1 : d < 0) (n : ℕ) :
    Integrable (thermalDualPrimeIntegrand Y d n) := by
  have hd2 : d ≤ 3 / 2 := by linarith
  have hbound := (gammaContourFactor_vertical_integrable hY hd0 hd2).norm.const_mul
    ‖contourLambdaTerm n ((1 - d : ℝ) : ℂ)‖
  apply hbound.mono' (thermalDualPrimeIntegrand_continuous Y d n hd0).aestronglyMeasurable
  filter_upwards with t
  exact (norm_thermalDualPrimeIntegrand Y d n t).le

theorem thermalDualPrimeIntegrand_integral_norm_summable {Y d : ℝ}
    (hd1 : d < 0) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖thermalDualPrimeIntegrand Y d n t‖) := by
  have hcoeff := contourLambdaTerm_norm_summable (s := ((1 - d : ℝ) : ℂ))
    (by simp only [Complex.ofReal_re]; linarith)
  have h := hcoeff.mul_right (∫ t : ℝ, ‖gammaContourFactor Y d 1 t‖)
  refine h.congr fun n => ?_
  simp_rw [norm_thermalDualPrimeIntegrand]
  rw [integral_mul_left]

theorem thermalDualPrimeIntegrand_norm_summable_at {d : ℝ} (hd : d < 0)
    (Y t : ℝ) : Summable (fun n : ℕ => ‖thermalDualPrimeIntegrand Y d n t‖) := by
  simpa only [norm_thermalDualPrimeIntegrand] using
    (contourLambdaTerm_norm_summable (s := ((1 - d : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith)).mul_right
        ‖gammaContourFactor Y d 1 t‖

theorem thermalDualPrimeIntegrand_tsum_integrable {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd1 : d < 0) :
    Integrable (fun t : ℝ => ∑' n : ℕ, thermalDualPrimeIntegrand Y d n t) := by
  have hd2 : d ≤ 3 / 2 := by linarith
  have hmeas : StronglyMeasurable
      (fun t : ℝ => ∑' n : ℕ, thermalDualPrimeIntegrand Y d n t) := by
    apply stronglyMeasurable_of_tendsto (u := (atTop : Filter ℕ))
      (f := fun k t => ∑ n ∈ Finset.range k, thermalDualPrimeIntegrand Y d n t)
    · intro k
      exact (continuous_finset_sum (Finset.range k)
        (fun n _ => thermalDualPrimeIntegrand_continuous Y d n hd0)).stronglyMeasurable
    · apply tendsto_pi_nhds.mpr
      intro t
      exact (thermalDualPrimeIntegrand_norm_summable_at hd1 Y t).of_norm.hasSum.tendsto_sum_nat
  have hG := gammaContourFactor_vertical_integrable hY hd0 hd2
  have hbound := hG.norm.const_mul (∑' n : ℕ, ‖contourLambdaTerm n ((1 - d : ℝ) : ℂ)‖)
  apply hbound.mono' hmeas.aestronglyMeasurable
  filter_upwards with t
  calc
    _ ≤ ∑' n : ℕ, ‖thermalDualPrimeIntegrand Y d n t‖ :=
      norm_tsum_le_tsum_norm (thermalDualPrimeIntegrand_norm_summable_at hd1 Y t)
    _ = _ := by simp_rw [norm_thermalDualPrimeIntegrand]; rw [tsum_mul_right]

/-- Branch conditions for reciprocal Mellin inversion are proved from n>0. -/
theorem contourNat_reflected_cpow {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-(1 - s)) = (n : ℂ)⁻¹ * (((n : ℝ)⁻¹ : ℂ) ^ (-s)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hnR.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, neg_neg,
    neg_sub, Complex.cpow_sub _ _ hnC, Complex.cpow_one]
  ring

theorem thermalDualPrimeIntegrand_single_inversion {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd1 : d < 0) (n : ℕ) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ, thermalDualPrimeIntegrand Y d n t) =
      (contourLambdaWeight n : ℂ) * thermalDualTest Y (n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [thermalDualPrimeIntegrand, contourLambdaTerm, contourLambdaWeight,
      not_isPrimePow_zero]
  · have hnN : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnN
    have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
    have hd2 : d ≤ 3 / 2 := by linarith
    have heq : thermalDualPrimeIntegrand Y d n =
        (fun t : ℝ => ((contourLambdaWeight n : ℂ) * (n : ℂ)⁻¹) *
          ((((n : ℝ)⁻¹ : ℂ) ^ (-((d : ℂ) + (t : ℂ) * Complex.I))) *
            ((Y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I) *
              Complex.Gamma ((d : ℂ) + (t : ℂ) * Complex.I + 1)))) := by
      ext t
      simp only [thermalDualPrimeIntegrand, contourLambdaTerm,
        contourNat_reflected_cpow hnN, gammaContourFactor,
        weightedGammaTerm_eq_cpow hY0, gammaContourPoint, one_mul]
      ring
    rw [heq, integral_mul_left, ← mul_smul_comm]
    rw [thermalTest_gamma_inversion hY hd0 hd2 (inv_pos.mpr hnR)]
    simp only [thermalDualTest, Complex.cpow_neg_one, Complex.ofReal_natCast]
    ring

theorem thermalDualPrimeIntegrand_full_inversion {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd1 : d < 0) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, ∑' n : ℕ, thermalDualPrimeIntegrand Y d n t) =
      ∑' n : ℕ, (contourLambdaWeight n : ℂ) * thermalDualTest Y (n : ℝ) := by
  have hexchange := integral_tsum_of_summable_integral_norm
    (thermalDualPrimeIntegrand_integrable hY hd0 hd1)
    (thermalDualPrimeIntegrand_integral_norm_summable hd1)
  rw [← hexchange, ← tsum_const_smul'']
  exact tsum_congr (thermalDualPrimeIntegrand_single_inversion hY hd0 hd1)

theorem thermalZeta_dual_arithmetic_integrand_eq {d : ℝ} (hd : d < 0) (Y t : ℝ) :
    gammaContourFactor Y d 1 t *
      (-(deriv riemannZeta (1 - gammaContourPoint d 1 t) /
        riemannZeta (1 - gammaContourPoint d 1 t))) =
      ∑' n : ℕ, thermalDualPrimeIntegrand Y d n t := by
  have hs : 1 < (1 - gammaContourPoint d 1 t).re := by
    simp only [gammaContourPoint, Complex.sub_re, Complex.one_re,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  rw [contourZeta_logDeriv_direct_Lambda hs, neg_neg]
  simp only [thermalDualPrimeIntegrand, contourLambdaTerm, tsum_mul_right]
  ring

theorem thermalZeta_dual_arithmetic_vertical_integrable {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd1 : d < 0) :
    Integrable (fun t : ℝ => gammaContourFactor Y d 1 t *
      (-(deriv riemannZeta (1 - gammaContourPoint d 1 t) /
        riemannZeta (1 - gammaContourPoint d 1 t)))) := by
  apply (thermalDualPrimeIntegrand_tsum_integrable hY hd0 hd1).congr
  filter_upwards with t
  exact (thermalZeta_dual_arithmetic_integrand_eq hd1 Y t).symm

theorem thermalZeta_dual_arithmetic_vertical_inversion {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd1 : d < 0) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, gammaContourFactor Y d 1 t *
        (-(deriv riemannZeta (1 - gammaContourPoint d 1 t) /
          riemannZeta (1 - gammaContourPoint d 1 t)))) =
      ∑' n : ℕ, (contourLambdaWeight n : ℂ) * thermalDualTest Y (n : ℝ) := by
  have heq : (fun t : ℝ => gammaContourFactor Y d 1 t *
      (-(deriv riemannZeta (1 - gammaContourPoint d 1 t) /
        riemannZeta (1 - gammaContourPoint d 1 t)))) =
      (fun t : ℝ => ∑' n : ℕ, thermalDualPrimeIntegrand Y d n t) :=
    funext (thermalZeta_dual_arithmetic_integrand_eq hd1 Y)
  rw [heq]
  exact thermalDualPrimeIntegrand_full_inversion hY hd0 hd1

end GoldbachContinuous22

#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand
#print axioms GoldbachContinuous22.contourLambdaTerm_reflected_norm
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_continuous
#print axioms GoldbachContinuous22.norm_thermalDualPrimeIntegrand
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_integrable
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_integral_norm_summable
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_norm_summable_at
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_tsum_integrable
#print axioms GoldbachContinuous22.contourNat_reflected_cpow
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_single_inversion
#print axioms GoldbachContinuous22.thermalDualPrimeIntegrand_full_inversion
#print axioms GoldbachContinuous22.thermalZeta_dual_arithmetic_integrand_eq
#print axioms GoldbachContinuous22.thermalZeta_dual_arithmetic_vertical_integrable
#print axioms GoldbachContinuous22.thermalZeta_dual_arithmetic_vertical_inversion
