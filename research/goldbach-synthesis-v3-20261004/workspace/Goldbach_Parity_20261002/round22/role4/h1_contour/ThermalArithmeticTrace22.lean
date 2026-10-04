import ThermalPoleDifference22

/- SOURCE_ONLY. The full arithmetic thermal object is an actual absolutely
   convergent prime-power sum. Its convergence is derived from the previously
   constructed integral-norm series and genuine single-term Mellin inversion.
   It is not an assumed spectral trace or a Goldbach coefficient. -/

noncomputable section
open Complex MeasureTheory

namespace GoldbachContinuous22

def thermalArithmeticSummand (Y : ℝ) (n : ℕ) : ℂ :=
  (contourLambdaWeight n : ℂ) *
    (thermalTest Y (n : ℝ) + thermalDualTest Y (n : ℝ))

def thermalArithmeticTrace (Y : ℝ) : ℂ :=
  ∑' n : ℕ, thermalArithmeticSummand Y n

theorem thermalDirectSummand_norm_summable {Y : ℝ} (hY : 1 ≤ Y) :
    Summable (fun n : ℕ => ‖(contourLambdaWeight n : ℂ) * thermalTest Y (n : ℝ)‖) := by
  have hs := thermalPrimeIntegrand_integral_norm_summable (c := (3 / 2 : ℝ))
    hY (by norm_num) le_rfl
  let Cpi : ℝ := 1 / (2 * Real.pi)
  apply Summable.of_norm_bounded
    (fun n : ℕ => |Cpi| * (∫ t : ℝ, ‖thermalPrimeIntegrand Y (3 / 2) n t‖))
    (hs.mul_left |Cpi|)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    ← thermalPrimeIntegrand_single_inversion (c := (3 / 2 : ℝ))
      hY (by norm_num) le_rfl n, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (abs_nonneg Cpi)

theorem thermalDualSummand_norm_summable {Y : ℝ} (hY : 1 ≤ Y) :
    Summable (fun n : ℕ => ‖(contourLambdaWeight n : ℂ) * thermalDualTest Y (n : ℝ)‖) := by
  have hs := thermalDualPrimeIntegrand_integral_norm_summable
    (Y := Y) (d := (-(1 / 2) : ℝ)) (by norm_num)
  let Cpi : ℝ := 1 / (2 * Real.pi)
  apply Summable.of_norm_bounded
    (fun n : ℕ => |Cpi| * (∫ t : ℝ, ‖thermalDualPrimeIntegrand Y (-(1 / 2)) n t‖))
    (hs.mul_left |Cpi|)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    ← thermalDualPrimeIntegrand_single_inversion (d := (-(1 / 2) : ℝ))
      hY le_rfl (by norm_num) n, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (abs_nonneg Cpi)

theorem thermalArithmeticSummand_norm_summable {Y : ℝ} (hY : 1 ≤ Y) :
    Summable (fun n : ℕ => ‖thermalArithmeticSummand Y n‖) := by
  have hd := thermalDirectSummand_norm_summable hY
  have hi := thermalDualSummand_norm_summable hY
  apply Summable.of_norm_bounded
    (fun n : ℕ => ‖(contourLambdaWeight n : ℂ) * thermalTest Y (n : ℝ)‖ +
      ‖(contourLambdaWeight n : ℂ) * thermalDualTest Y (n : ℝ)‖) (hd.add hi)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), thermalArithmeticSummand, mul_add]
  exact norm_add_le _ _

theorem thermalArithmeticSummand_summable {Y : ℝ} (hY : 1 ≤ Y) :
    Summable (thermalArithmeticSummand Y) :=
  (thermalArithmeticSummand_norm_summable hY).of_norm

theorem thermalArithmeticTrace_eq_direct_add_dual {Y : ℝ} (hY : 1 ≤ Y) :
    thermalArithmeticTrace Y =
      (∑' n : ℕ, (contourLambdaWeight n : ℂ) * thermalTest Y (n : ℝ)) +
      (∑' n : ℕ, (contourLambdaWeight n : ℂ) * thermalDualTest Y (n : ℝ)) := by
  unfold thermalArithmeticTrace
  simp only [thermalArithmeticSummand, mul_add]
  exact tsum_add (thermalDirectSummand_norm_summable hY).of_norm
    (thermalDualSummand_norm_summable hY).of_norm

end GoldbachContinuous22

#print axioms GoldbachContinuous22.thermalArithmeticSummand
#print axioms GoldbachContinuous22.thermalArithmeticTrace
#print axioms GoldbachContinuous22.thermalDirectSummand_norm_summable
#print axioms GoldbachContinuous22.thermalDualSummand_norm_summable
#print axioms GoldbachContinuous22.thermalArithmeticSummand_norm_summable
#print axioms GoldbachContinuous22.thermalArithmeticSummand_summable
#print axioms GoldbachContinuous22.thermalArithmeticTrace_eq_direct_add_dual
