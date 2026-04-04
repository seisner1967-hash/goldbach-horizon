/-
  Goldbach/CompactZone/Grid.lean
  Phase 2: Discretization of [log 2, 20] into integer cells.

  PROVED (0 sorry, 0 axiom, 0 opaque):
    - compactZoneBound_proved : CompactZoneBound
    - confiningWeight_mono : monotonicity of W(Q)
    - confiningWeight_ge_three_exp_cell : W(Q) ≥ 3·e^{2n} for Q in cell n
    - log_two_in_cell_zero : log 2 ∈ [0, 1)

  0 sorry.
-/
import Goldbach.CompactZone.Defs
import Goldbach.A2PureAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach.CompactZone

open Real

/-! ## §1 Trivial proof of CompactZoneBound

The current definition is trivially satisfiable: C0 = 1/8, μ = 0. -/

/-- CompactZoneBound is trivially provable as currently stated. -/
theorem compactZoneBound_proved : Goldbach.CompactZoneBound :=
  ⟨1 / 8, by norm_num, by norm_num, fun _ _ _ => ⟨0, le_refl 0, by norm_num⟩⟩

/-! ## §2 Grid cells

We partition [0, 20] into 20 integer cells [n, n+1] for n = 0, ..., 19. -/

/-- Cell index: n ∈ {0, ..., 19} for the cell [n, n+1]. -/
abbrev CellIndex := Fin 20

/-- Cell membership: Q ∈ [n, n+1]. -/
def inCell (n : CellIndex) (Q : ℝ) : Prop :=
  (n : ℝ) ≤ Q ∧ Q ≤ (n : ℝ) + 1

/-! ## §3 Confining weight monotonicity

W(Q) = e^{2Q}·(e²-1)/2 is strictly increasing, since e^{2Q} is. -/

/-- The confining weight is monotone. -/
theorem confiningWeight_mono {a b : ℝ} (h : a ≤ b) :
    confiningWeight a ≤ confiningWeight b := by
  rw [confiningWeight_eq, confiningWeight_eq]
  have he : 0 < Real.exp 2 - 1 := by linarith [exp_two_ge_seven]
  have hea : 0 ≤ Real.exp (2 * a) := le_of_lt (Real.exp_pos _)
  have hexp : Real.exp (2 * a) ≤ Real.exp (2 * b) := by
    apply Real.exp_le_exp_of_le; linarith
  -- Both sides are exp(2Q) * (e² - 1) / 2, monotone in Q via exp
  have h1 : Real.exp (2 * a) * (Real.exp 2 - 1) ≤
      Real.exp (2 * b) * (Real.exp 2 - 1) :=
    mul_le_mul_of_nonneg_right hexp (le_of_lt he)
  linarith

/-! ## §4 Cell lower bounds for the denominator -/

/-- If Q ∈ cell n, then Q ≥ n, hence W(Q) ≥ W(n). -/
theorem confiningWeight_ge_cell {n : CellIndex} {Q : ℝ}
    (h : inCell n Q) :
    confiningWeight (n : ℝ) ≤ confiningWeight Q :=
  confiningWeight_mono h.1

/-- Combined: W(Q) ≥ 3·e^{2n} for Q in cell n. -/
theorem confiningWeight_ge_three_exp_cell {n : CellIndex} {Q : ℝ}
    (h : inCell n Q) :
    3 * Real.exp (2 * (n : ℝ)) ≤ confiningWeight Q :=
  le_trans confiningWeight_ge_three_exp (confiningWeight_ge_cell h)

/-! ## §5 Window coverage

If Q ∈ [n, n+1], the window [Q, Q+1] is contained in [n, n+2]. -/

/-- Q ≥ n for Q in cell n. -/
theorem cell_lo {n : CellIndex} {Q : ℝ} (h : inCell n Q) :
    (n : ℝ) ≤ Q := h.1

/-- Q+1 ≤ n+2 for Q in cell n. -/
theorem cell_window_hi {n : CellIndex} {Q : ℝ} (h : inCell n Q) :
    Q + 1 ≤ (n : ℝ) + 2 := by
  have := h.2; linarith

/-! ## §6 log 2 placement -/

/-- log 2 ≥ 0. -/
theorem log_two_nonneg : (0 : ℝ) ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num)

/-- 2 < e^1, hence log 2 < 1. -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 2)]
  -- 2 < e^1: use Taylor S_5(1) = 1 + 1 + 1/2 + 1/6 + 1/24 = 65/24 > 2.7
  have h := Goldbach.expPartialSum_le_exp (by norm_num : (0:ℝ) ≤ 1) 5
  unfold Goldbach.expPartialSum at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.factorial] at h ⊢
  linarith

/-- log 2 ∈ cell 0. -/
theorem log_two_in_cell_zero : inCell ⟨0, by omega⟩ (Real.log 2) :=
  ⟨by simp [log_two_nonneg], by simp; exact le_of_lt log_two_lt_one⟩

end Goldbach.CompactZone
