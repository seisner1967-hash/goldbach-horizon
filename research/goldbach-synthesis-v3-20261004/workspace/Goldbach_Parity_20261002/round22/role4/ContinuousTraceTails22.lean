import QuadraticLaplaceMoments22
import RealTraceEnvelopes22

/- Actual analytic kernel tails, source preparation only. The spectral measure,
   actual zero count, Weil formula, and arithmetic sum comparison remain separate. -/

noncomputable section
open Set MeasureTheory

namespace GoldbachContinuous22

/-- Integrability and closed evaluation of the heat-tail polynomial itself. -/
theorem heat_polynomial_integrable {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    IntegrableOn (fun u : ℝ =>
      a * (T * Real.log T + (Real.log T + 1) * u + u ^ 2 / (2 * T)) *
        Real.exp (-(a * (T + u)))) (Ioi 0) := by
  have h := (quadraticLaplace_integrable ha
    (T * Real.log T) (Real.log T + 1) (1 / (2 * T))).const_mul
      (a * Real.exp (-(a * T)))
  apply h.congr_fun _ measurableSet_Ioi
  intro u _
  have hexp : Real.exp (-(a * (T + u))) =
      Real.exp (-(a * T)) * Real.exp (-(a * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  unfold quadraticLaplace
  ring

/-- A genuine integral inequality; there is no supplied target majorant. -/
theorem heat_kernel_integrable_and_bound {a T : ℝ} (ha : 0 < a) (hT : 1 ≤ T) :
    IntegrableOn (fun u : ℝ => a * ((T + u) * Real.log (T + u)) *
      Real.exp (-(a * (T + u)))) (Ioi 0) ∧
    (∫ u : ℝ in Ioi 0, a * ((T + u) * Real.log (T + u)) *
      Real.exp (-(a * (T + u)))) ≤
      Real.exp (-(a * T)) *
        (T * Real.log T + (Real.log T + 1) / a + 1 / (a ^ 2 * T)) := by
  have hT0 : 0 < T := by linarith
  let f : ℝ → ℝ := fun u => a * ((T + u) * Real.log (T + u)) *
    Real.exp (-(a * (T + u)))
  let g : ℝ → ℝ := fun u =>
    a * (T * Real.log T + (Real.log T + 1) * u + u ^ 2 / (2 * T)) *
      Real.exp (-(a * (T + u)))
  have hg : IntegrableOn g (Ioi 0) := heat_polynomial_integrable ha hT0
  have hnonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f u := by
    intro u hu
    have htu : 1 ≤ T + u := by linarith [hu]
    have hlog : 0 ≤ Real.log (T + u) := Real.log_nonneg htu
    dsimp [f]
    positivity
  have hle : ∀ u ∈ Ioi (0 : ℝ), f u ≤ g u := by
    intro u hu
    have htu : T ≤ T + u := by linarith [hu]
    have hp := tlog_taylor_upper hT0 htu
    simp only [add_sub_cancel_left] at hp
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp ha.le) (Real.exp_pos _).le
  have hcont : ContinuousOn f (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have htu : 0 < T + u := by linarith [hu]
    dsimp [f]
    fun_prop (disch := positivity)
  have hf : IntegrableOn f (Ioi 0) := by
    apply hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u hu)]
    exact hle u hu
  refine ⟨hf, ?_⟩
  calc
    (∫ u : ℝ in Ioi 0, f u) ≤ ∫ u : ℝ in Ioi 0, g u := by
      apply integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hle u hu
    _ = _ := integral_heat_polynomial ha hT0

/-- Integrability of the explicit tangent polynomial used for the prime tail. -/
theorem prime_polynomial_integrable {Y X : ℝ} (hY : 0 < Y) (hX : 0 < X) :
    IntegrableOn (fun u : ℝ =>
      ((X + u) / Y) * (Real.log X + u / X) * Real.exp (-(X + u) / Y))
      (Ioi 0) := by
  have h := (quadraticLaplace_integrable (one_div_pos.mpr hY)
    (X * Real.log X) (Real.log X + 1) (1 / X)).const_mul (Real.exp (-X / Y) / Y)
  apply h.congr_fun _ measurableSet_Ioi
  intro u _
  have hexp : Real.exp (-(X + u) / Y) =
      Real.exp (-X / Y) * Real.exp (-((1 / Y) * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  unfold quadraticLaplace
  field_simp [hY.ne', hX.ne']
  ring

/-- Actual integrated prime-density bound. Discrete arithmetic tails are not asserted here. -/
theorem prime_kernel_integrable_and_bound {Y X : ℝ} (hY : 0 < Y) (hX : 1 ≤ X) :
    IntegrableOn (fun u : ℝ => ((X + u) / Y) * Real.log (X + u) *
      Real.exp (-(X + u) / Y)) (Ioi 0) ∧
    (∫ u : ℝ in Ioi 0, ((X + u) / Y) * Real.log (X + u) *
      Real.exp (-(X + u) / Y)) ≤ primeError Y X := by
  have hX0 : 0 < X := by linarith
  let f : ℝ → ℝ := fun u => ((X + u) / Y) * Real.log (X + u) *
    Real.exp (-(X + u) / Y)
  let g : ℝ → ℝ := fun u =>
    ((X + u) / Y) * (Real.log X + u / X) * Real.exp (-(X + u) / Y)
  have hg : IntegrableOn g (Ioi 0) := prime_polynomial_integrable hY hX0
  have hnonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f u := by
    intro u hu
    have hxu : 1 ≤ X + u := by linarith [hu]
    have hlog : 0 ≤ Real.log (X + u) := Real.log_nonneg hxu
    dsimp [f]
    positivity
  have hle : ∀ u ∈ Ioi (0 : ℝ), f u ≤ g u := by
    intro u hu
    have hxu : 0 < X + u := by linarith [hu]
    simpa only [add_sub_cancel_left] using
      prime_integrand_le_tangent hY hX0 hxu
  have hcont : ContinuousOn f (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hxu : 0 < X + u := by linarith [hu]
    dsimp [f]
    fun_prop (disch := positivity)
  have hf : IntegrableOn f (Ioi 0) := by
    apply hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u hu)]
    exact hle u hu
  refine ⟨hf, ?_⟩
  calc
    (∫ u : ℝ in Ioi 0, f u) ≤ ∫ u : ℝ in Ioi 0, g u := by
      apply integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hle u hu
    _ = primeError Y X := integral_prime_polynomial hY hX0

end GoldbachContinuous22

#print axioms GoldbachContinuous22.heat_polynomial_integrable
#print axioms GoldbachContinuous22.heat_kernel_integrable_and_bound
#print axioms GoldbachContinuous22.prime_polynomial_integrable
#print axioms GoldbachContinuous22.prime_kernel_integrable_and_bound
