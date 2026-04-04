/-
  Goldbach/Budget.lean
  Conservative budget layer for the Horizon collage.

  This file isolates the explicit numerical constants used in the narrative:
  * certified budget  = 0.78
  * safety margin     = 0.11
  * total upper bound = 0.89

  Everything is kept elementary and `norm_num`-friendly.
-/

import Goldbach.Thresholds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach

/-! ## Rational constants -/

/-- The certified U1--U6 budget, stored exactly as a rational number. -/
def certifiedBudgetQ : ℚ := 39 / 50

/-- The positivity margin used in the final ledger. -/
def safetyMarginQ : ℚ := 11 / 100

/-- The resulting total upper bound `0.89`. -/
def totalBudgetUpperQ : ℚ := certifiedBudgetQ + safetyMarginQ

/-- The remaining margin below `1`. -/
def remainingMarginQ : ℚ := 1 - totalBudgetUpperQ

/-! ## Real versions of the same constants -/

/-- Real form of the certified budget `0.78`. -/
def certifiedBudget : ℝ := certifiedBudgetQ

/-- Real form of the safety margin `0.11`. -/
def safetyMargin : ℝ := safetyMarginQ

/-- Real form of the total upper bound `0.89`. -/
def totalBudgetUpper : ℝ := totalBudgetUpperQ

/-- Real form of the remaining margin. -/
def remainingMargin : ℝ := remainingMarginQ

/-! ## Exact identities -/

theorem certifiedBudgetQ_eq : certifiedBudgetQ = 39 / 50 := by
  rfl

theorem safetyMarginQ_eq : safetyMarginQ = 11 / 100 := by
  rfl

theorem totalBudgetUpperQ_eq : totalBudgetUpperQ = 89 / 100 := by
  norm_num [totalBudgetUpperQ, certifiedBudgetQ, safetyMarginQ]

theorem remainingMarginQ_eq : remainingMarginQ = 11 / 100 := by
  norm_num [remainingMarginQ, totalBudgetUpperQ_eq]

theorem certifiedBudget_eq : certifiedBudget = (39 : ℝ) / 50 := by
  norm_num [certifiedBudget, certifiedBudgetQ]

theorem safetyMargin_eq : safetyMargin = (11 : ℝ) / 100 := by
  norm_num [safetyMargin, safetyMarginQ]

theorem totalBudgetUpper_eq : totalBudgetUpper = (89 : ℝ) / 100 := by
  norm_num [totalBudgetUpper, totalBudgetUpperQ_eq]

theorem remainingMargin_eq : remainingMargin = (11 : ℝ) / 100 := by
  norm_num [remainingMargin, remainingMarginQ_eq]

/-- The familiar decimal identity `0.78 + 0.11 = 0.89`. -/
theorem budget_decimal_identity : certifiedBudget + safetyMargin = totalBudgetUpper := by
  norm_num [certifiedBudget, safetyMargin, totalBudgetUpper,
    certifiedBudgetQ, safetyMarginQ, totalBudgetUpperQ]

/-- The final margin is exactly `1 - 0.89 = 0.11`. -/
theorem remainingMargin_from_total : remainingMargin = 1 - totalBudgetUpper := by
  norm_num [remainingMargin, remainingMarginQ, totalBudgetUpper, totalBudgetUpperQ]

/-- Equivalently, `1 - 0.78 - 0.11 = 0.11`. -/
theorem final_margin_identity : 1 - certifiedBudget - safetyMargin = remainingMargin := by
  norm_num [certifiedBudget, safetyMargin, remainingMargin,
    certifiedBudgetQ, safetyMarginQ, remainingMarginQ]

/-! ## Positivity and comparison lemmas -/

theorem certifiedBudget_nonneg : 0 ≤ certifiedBudget := by
  norm_num [certifiedBudget, certifiedBudgetQ]

theorem safetyMargin_pos : 0 < safetyMargin := by
  norm_num [safetyMargin, safetyMarginQ]

theorem safetyMargin_nonneg : 0 ≤ safetyMargin := by
  linarith [safetyMargin_pos]

theorem totalBudgetUpper_pos : 0 < totalBudgetUpper := by
  norm_num [totalBudgetUpper, totalBudgetUpperQ]

theorem certifiedBudget_lt_one : certifiedBudget < 1 := by
  norm_num [certifiedBudget, certifiedBudgetQ]

theorem safetyMargin_lt_one : safetyMargin < 1 := by
  norm_num [safetyMargin, safetyMarginQ]

theorem totalBudgetUpper_lt_one : totalBudgetUpper < 1 := by
  norm_num [totalBudgetUpper, totalBudgetUpperQ]

theorem totalBudgetUpper_le_one : totalBudgetUpper ≤ 1 := by
  linarith [totalBudgetUpper_lt_one]

theorem remainingMargin_pos : 0 < remainingMargin := by
  norm_num [remainingMargin, remainingMarginQ]

theorem remainingMargin_nonneg : 0 ≤ remainingMargin := by
  linarith [remainingMargin_pos]

/-- The final ledger leaves a strictly positive margin below `1`. -/
theorem final_budget_is_safe : certifiedBudget + safetyMargin < 1 := by
  simpa [budget_decimal_identity] using totalBudgetUpper_lt_one

/-- A convenience lemma in the exact shape often used in the notes. -/
theorem one_sub_budget_gt_zero : 0 < 1 - certifiedBudget - safetyMargin := by
  simpa [final_margin_identity] using remainingMargin_pos

/-! ## Small auxiliary lemmas linking with thresholds -/

/-- The explicit threshold is positive. -/
theorem N0_pos : 0 < N0 := by
  decide

/-- The AMS verification bound is positive. -/
theorem AMSBound_pos : 0 < AMSBound := by
  decide

/-- The explicit threshold lies below the AMS verification frontier. -/
theorem N0_lt_AMSBound : N0 < AMSBound := by
  have hne : N0 ≠ AMSBound := by
    decide
  exact lt_of_le_of_ne N0_le_AMSBound hne

/-- Real-valued version of the overlap inequality. -/
theorem N0_le_AMSBound_real : (N0 : ℝ) ≤ (AMSBound : ℝ) := by
  exact_mod_cast N0_le_AMSBound

end Goldbach
