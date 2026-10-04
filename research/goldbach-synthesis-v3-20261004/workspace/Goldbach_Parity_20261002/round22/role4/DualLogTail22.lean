import ArchimedeanTail22

/- Source-only exact logarithmic tail. Discrete von Mangoldt comparison and
   the global trace remain separate obligations. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def dualPrimitive (x : ℝ) : ℝ := -(Real.log x + 1) / x

theorem dualPrimitive_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt dualPrimitive (Real.log x / x ^ 2) x := by
  have hd := (((Real.hasDerivAt_log hx.ne').add_const 1).div
    (hasDerivAt_id x) hx.ne').neg
  convert hd using 1
  · funext t
    unfold dualPrimitive
    ring
  · field_simp [hx.ne']
    ring

theorem dualPrimitive_tendsto : Tendsto dualPrimitive atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  convert (hlog.add hi).neg using 1
  · funext x
    unfold dualPrimitive
    ring
  · simp

/-- The actual logarithmic kernel is integrable and has a closed exact tail. -/
theorem dual_log_kernel_integrable_and_integral {Q : ℝ} (hQ : 1 ≤ Q) :
    IntegrableOn (fun x : ℝ => Real.log x / x ^ 2) (Ioi Q) ∧
      (∫ x : ℝ in Ioi Q, Real.log x / x ^ 2) = (Real.log Q + 1) / Q := by
  have hQ0 : 0 < Q := by linarith
  have hd : ∀ x ∈ Ici Q, HasDerivAt dualPrimitive (Real.log x / x ^ 2) x := by
    intro x hx
    exact dualPrimitive_hasDerivAt (hQ0.trans_le hx)
  have hnonneg : ∀ x ∈ Ioi Q, 0 ≤ Real.log x / x ^ 2 := by
    intro x hx
    have hx1 : 1 ≤ x := hQ.trans hx.le
    have hl := Real.log_nonneg hx1
    positivity
  have hf := integrableOn_Ioi_deriv_of_nonneg' hd hnonneg dualPrimitive_tendsto
  refine ⟨hf, ?_⟩
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' hd hf dualPrimitive_tendsto
  simpa only [dualPrimitive, zero_sub, neg_div, neg_neg] using heq

/-- Exact H5 integral envelope, derived rather than supplied as a premise. -/
theorem integral_dual_density {Y Q : ℝ} (hY : 0 < Y) (hQ : 1 ≤ Q) :
    IntegrableOn (fun x : ℝ => Real.log x / (Y * x ^ 2)) (Ioi Q) ∧
      (∫ x : ℝ in Ioi Q, Real.log x / (Y * x ^ 2)) = dualError Y Q := by
  obtain ⟨hf, heq⟩ := dual_log_kernel_integrable_and_integral hQ
  have hfun : (fun x : ℝ => Real.log x / (Y * x ^ 2)) =
      fun x : ℝ => (1 / Y) * (Real.log x / x ^ 2) := by
    funext x
    ring
  rw [hfun]
  refine ⟨hf.const_mul (1 / Y), ?_⟩
  rw [integral_const_mul, heq]
  unfold dualError
  ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.dualPrimitive
#print axioms GoldbachContinuous22.dualPrimitive_hasDerivAt
#print axioms GoldbachContinuous22.dualPrimitive_tendsto
#print axioms GoldbachContinuous22.dual_log_kernel_integrable_and_integral
#print axioms GoldbachContinuous22.integral_dual_density
