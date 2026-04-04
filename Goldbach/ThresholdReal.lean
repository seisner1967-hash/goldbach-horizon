/-
  Goldbach/ThresholdReal.lean
  Inégalités de seuil dans ℝ pour le collage G43.
  0 sorry. exp/log bounds closed via ExpBounds (Taylor + geometric tail).
-/
import Goldbach.Thresholds
import Goldbach.ExpBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach

open Finset Real BigOperators

-- Versions réelles de N₀ et AMSBound ──────────────────────────────
noncomputable def N0_real      : ℝ := (N0 : ℝ)
noncomputable def AMSBound_real : ℝ := (AMSBound : ℝ)

-- Positivité (norm_num, 0 sorry) ───────────────────────────────────
theorem N0_real_pos : 0 < N0_real := by
  unfold N0_real; exact_mod_cast (show 0 < N0 by norm_num [N0])

theorem AMSBound_real_pos : 0 < AMSBound_real := by
  unfold AMSBound_real; exact_mod_cast (show 0 < AMSBound by norm_num [AMSBound])

-- Couverture (exact_mod_cast, 0 sorry) ─────────────────────────────
theorem N0_real_lt_AMSBound_real : N0_real < AMSBound_real := by
  unfold N0_real AMSBound_real
  exact_mod_cast N0_lt_AMSBound

-- Encadrement de log(N₀) ───────────────────────────────────────────
-- exp(42) ≈ 1.74e18 < 2.7e18 = N₀ < 4.73e18 ≈ exp(43)

/-- 42 < log(N₀): proved via exp(42) < N₀ using Taylor upper bound (n=44). -/
theorem log_N0_gt_42 : 42 < Real.log N0_real := by
  rw [Real.lt_log_iff_exp_lt N0_real_pos]
  -- Goal: Real.exp 42 < N0_real = 2700000000000000000
  unfold N0_real N0
  -- Use upper bound: exp(42) ≤ S_44(42) + tail(42, 44)
  apply lt_of_le_of_lt
    (exp_le_partial_sum_plus_tail (by norm_num : (0:ℝ) ≤ 42)
      (by norm_num : (42:ℝ) < (44:ℕ) + 1))
  -- S_44(42) + tail(42,44) < 2700000000000000000
  unfold expPartialSum expTailBound
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

/-- log(N₀) < 43: proved via N₀ < exp(43) using Taylor lower bound (n=45). -/
theorem log_N0_lt_43 : Real.log N0_real < 43 := by
  rw [Real.log_lt' N0_real_pos]
  -- Goal: N0_real = 2700000000000000000 < Real.exp 43
  unfold N0_real N0
  -- Use lower bound: S_45(43) ≤ exp(43) and 2.7e18 < S_45(43)
  apply lt_of_lt_of_le _ (expPartialSum_le_exp (by norm_num : (0:ℝ) ≤ 43) 45)
  -- 2700000000000000000 < S_45(43)
  unfold expPartialSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

-- Collage dans ℝ (0 sorry, utilise exact_mod_cast) ─────────────────
theorem N0_real_le_AMSBound_real : N0_real ≤ AMSBound_real :=
  le_of_lt N0_real_lt_AMSBound_real

-- log(AMSBound) > log(N₀) (0 sorry, monotonie) ────────────────────
theorem log_AMSBound_gt_log_N0 :
    Real.log N0_real < Real.log AMSBound_real :=
  Real.log_lt_log N0_real_pos N0_real_lt_AMSBound_real

end Goldbach
