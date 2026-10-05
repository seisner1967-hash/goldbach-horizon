# Frozen C0 signatures

```lean
theorem complement_involutive (N : ℕ) : Function.Involutive (complement N)

theorem pinned_cross_sum (N : ℕ) :
    (∑ i : Fin (N + 1), C (primePoint N ℚ (complement N i)) * X i) =
    (∑ i : Fin (N + 1), C (primePoint N ℚ i) * X (complement N i))

theorem pinned_telescoping (N : ℕ) :
    (∑ i : Fin (N + 1),
      (X (complement N i) + C (primePoint N ℚ (complement N i))) * pinnedFamily N i) =
    g N ℚ - C (goldbachCount N : ℚ)

theorem pinned_control_certificate (N : ℕ) (hG : (goldbachCount N : ℚ) ≠ 0) :
    Certificate (pinnedFamily N) (pinnedMultiplier N) (fun _ => 0)
      (C ((goldbachCount N : ℚ)⁻¹))

theorem pinned_family_pins (N : ℕ) (x : Fin (N + 1) → ℚ)
    (hF : ∀ i, eval x (pinnedFamily N i) = 0) : x = primePoint N ℚ

theorem pinned_certificate_iff_goldbach (N : ℕ) :
    (∃ A U B, Certificate (pinnedFamily N) A U B) ↔ 0 < goldbachCount N

theorem pinned_multiplier_degree_le_one (N : ℕ) (i : Fin (N + 1)) :
    (pinnedMultiplier N i).totalDegree ≤ 1

theorem pinned_B_degree_zero (N : ℕ) :
    (C ((goldbachCount N : ℚ)⁻¹) : R N ℚ).totalDegree = 0

theorem pinned_summand_degree_le_two (N : ℕ) (i : Fin (N + 1)) :
    (pinnedMultiplier N i * pinnedFamily N i).totalDegree ≤ 2

theorem g_degree_le_two (N : ℕ) : (g N ℚ).totalDegree ≤ 2

theorem pinned_g_summand_degree_le_two (N : ℕ) :
    (C ((goldbachCount N : ℚ)⁻¹) * g N ℚ).totalDegree ≤ 2
```
