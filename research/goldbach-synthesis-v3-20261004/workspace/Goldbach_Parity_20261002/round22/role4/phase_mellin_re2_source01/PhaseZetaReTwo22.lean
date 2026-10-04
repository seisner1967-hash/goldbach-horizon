import PhaseGammaReTwo22
import ZetaEulerLambda22
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! SOURCE ONLY. The genuine logarithmic derivative on Re(s)=2 is bounded
through the direct prime-power Euler SOURCE chain and a quantitative integral
comparison. None of these SOURCE dependencies is promoted to a compiler PASS.
No final L bound, Mellin identity or final integrability is a premise. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def reTwoLogDeriv (t : ℝ) : ℂ :=
  -(deriv riemannZeta (reTwoS t) / riemannZeta (reTwoS t))

theorem reTwo_pseries_partial_le_two (k : ℕ) :
    (∑ i ∈ Finset.range k, (((i + 2 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))) ≤ 2 := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-3 / 2 : ℝ))
      (Icc (1 : ℝ) (1 + (k : ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-3 / 2 : ℝ) ≤ 0)).mono
      (fun x hx => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx.1)
  have hsum := hanti.sum_le_integral
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)
  calc
    _ = ∑ i ∈ Finset.range k, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-3 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      push_cast
      ring
    _ ≤ ∫ x : ℝ in (1 : ℝ)..(1 + (k : ℝ)), x ^ (-3 / 2 : ℝ) := hsum
    _ ≤ ∫ x : ℝ in Ioi (1 : ℝ), x ^ (-3 / 2 : ℝ) := by
      rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg k))]
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (by linarith : 0 ≤ x) _
      · exact Eventually.of_forall (fun x hx => hx.1)
    _ = 2 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)]
      norm_num

theorem reTwo_Lambda_norm_partial_le_four (t : ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, ‖contourLambdaTerm (i + 2) (reTwoS t)‖) ≤ 4 := by
  have hs : 1 < (reTwoS t).re := by rw [reTwoS_re]; norm_num
  calc
    _ ≤ ∑ i ∈ Finset.range k, 2 * (((i + 2 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := contourLambdaTerm_pseries_bound hs (i + 2)
      norm_num only [reTwoS_re] at h
      exact h
    _ = 2 * (∑ i ∈ Finset.range k, (((i + 2 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (reTwo_pseries_partial_le_two k) (by norm_num)
    _ = 4 := by norm_num

theorem reTwo_Lambda_norm_tsum_le_four (t : ℝ) :
    (∑' n : ℕ, ‖contourLambdaTerm n (reTwoS t)‖) ≤ 4 := by
  have hs : 1 < (reTwoS t).re := by rw [reTwoS_re]; norm_num
  have hsum := sum_add_tsum_nat_add 2 (contourLambdaTerm_norm_summable hs)
  have h0 : contourLambdaTerm 0 (reTwoS t) = 0 := by
    simp only [contourLambdaTerm, contourLambdaWeight, if_neg not_isPrimePow_zero,
      Complex.ofReal_zero, zero_mul]
  have h1 : contourLambdaTerm 1 (reTwoS t) = 0 := by
    simp only [contourLambdaTerm, contourLambdaWeight, if_neg not_isPrimePow_one,
      Complex.ofReal_zero, zero_mul]
  have heq : (∑' n : ℕ, ‖contourLambdaTerm n (reTwoS t)‖) =
      ∑' n : ℕ, ‖contourLambdaTerm (n + 2) (reTwoS t)‖ := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1,
      norm_zero, add_zero, zero_add] using hsum.symm
  rw [heq]
  exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _)
    (fun k => reTwo_Lambda_norm_partial_le_four t k)

/-- The constant four is derived from the actual Euler Lambda identity. -/
theorem norm_reTwoLogDeriv_le_four (t : ℝ) : ‖reTwoLogDeriv t‖ ≤ 4 := by
  have hs : 1 < (reTwoS t).re := by rw [reTwoS_re]; norm_num
  rw [reTwoLogDeriv, contourZeta_logDeriv_direct_Lambda hs, neg_neg]
  exact (norm_tsum_le_tsum_norm (contourLambdaTerm_norm_summable hs)).trans
    (reTwo_Lambda_norm_tsum_le_four t)

theorem reTwo_zeta_analytic :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hn : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  exact (differentiableAt_riemannZeta hn).differentiableWithinAt

theorem reTwoLogDeriv_continuous : Continuous reTwoLogDeriv := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : 1 < (reTwoS t).re := by rw [reTwoS_re]; norm_num
  have hz := (reTwo_zeta_analytic (reTwoS t) hs).differentiableAt.continuousAt
  have hd := (reTwo_zeta_analytic.deriv (reTwoS t) hs).differentiableAt.continuousAt
  exact ((hd.div hz (contourZeta_ne_zero_on_right hs)).neg).comp reTwoS_continuous.continuousAt

end GoldbachContinuous22

#print axioms GoldbachContinuous22.reTwoLogDeriv
#print axioms GoldbachContinuous22.reTwo_pseries_partial_le_two
#print axioms GoldbachContinuous22.reTwo_Lambda_norm_partial_le_four
#print axioms GoldbachContinuous22.reTwo_Lambda_norm_tsum_le_four
#print axioms GoldbachContinuous22.norm_reTwoLogDeriv_le_four
#print axioms GoldbachContinuous22.reTwo_zeta_analytic
#print axioms GoldbachContinuous22.reTwoLogDeriv_continuous
