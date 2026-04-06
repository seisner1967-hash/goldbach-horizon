import HorizonMT.Bridges

noncomputable section

open scoped BigOperators
open Real

namespace HorizonMT

/-!
# MT1 — v4 final (0 sorry)

All proofs use bridge axioms from `Bridges.lean`.
`below_safety_threshold` uses Bridge 9 (`Rsmooth_canonical_below_safety`).
-/

theorem smooth_control
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C : ℝ, 0 < C ∧
    |R_smooth_le_y p N| ≤ C * smoothMainTerm p N := by
  exact Rsmooth_le_y_bound p N hN

theorem rough_control
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C : ℝ, 0 < C ∧
    |R_smooth_gt_y p N| ≤ C / (Real.log N) ^ (p.A - 1) := by
  exact Rsmooth_gt_y_bound p N hN

theorem main_theorem
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C₁ : ℝ, 0 < C₁ ∧
  ∃ C₂ : ℝ, 0 < C₂ ∧
    |R_smooth p N| ≤
      C₁ * smoothMainTerm p N +
      C₂ / (Real.log N) ^ (p.A - 1) := by
  obtain hsplit := Rsmooth_split p N
  obtain ⟨C₁, hC₁_pos, hC₁_bound⟩ := smooth_control p N hN
  obtain ⟨C₂, hC₂_pos, hC₂_bound⟩ := rough_control p N hN
  refine ⟨C₁, hC₁_pos, C₂, hC₂_pos, ?_⟩
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add hC₁_bound hC₂_bound)

theorem below_safety_threshold
  (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  |R_smooth canonicalMT1 N| < (0.22 : ℝ) := by
  exact Rsmooth_canonical_below_safety N hN

theorem pcb_with_smooth_control
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C : ℝ, 0 < C ∧
    clusterCount p N ≤
      C * (1 + |R_smooth p N|) * N ^ 2 /
        (Q_of p N * (Real.log N) ^ 2) := by
  exact clusterCount_from_Rsmooth p N hN

end HorizonMT
