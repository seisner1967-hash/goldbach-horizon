import AlgebraicGoldbach.Soundness
import Mathlib.Algebra.MvPolynomial.Degrees

namespace AlgebraicGoldbach

noncomputable section
open MvPolynomial
open scoped BigOperators

def pinnedFamily (N : ℕ) (i : Fin (N + 1)) : R N ℚ :=
  X i - C (primePoint N ℚ i)

def pinnedMultiplier (N : ℕ) (i : Fin (N + 1)) : R N ℚ :=
  -(X (complement N i) + C (primePoint N ℚ (complement N i))) *
    C ((goldbachCount N : ℚ)⁻¹)

theorem complement_involutive (N : ℕ) : Function.Involutive (complement N) := by
  intro i
  apply Fin.ext
  simp only [complement]
  have hi := i.isLt
  omega

theorem pinned_cross_sum (N : ℕ) :
    (∑ i : Fin (N + 1), C (primePoint N ℚ (complement N i)) * X i) =
    (∑ i : Fin (N + 1), C (primePoint N ℚ i) * X (complement N i)) := by
  apply Finset.sum_bij (fun i _ => complement N i)
  · intro i _
    exact Finset.mem_univ _
  · intro i _ j _ hij
    exact (complement_involutive N).injective hij
  · intro j _
    exact ⟨complement N j, Finset.mem_univ _, complement_involutive N j⟩
  · intro i _
    rw [complement_involutive N i]

theorem pinned_telescoping (N : ℕ) :
    (∑ i : Fin (N + 1),
      (X (complement N i) + C (primePoint N ℚ (complement N i))) * pinnedFamily N i) =
    g N ℚ - C (goldbachCount N : ℚ) := by
  have ht (i : Fin (N + 1)) :
      (X (complement N i) + C (primePoint N ℚ (complement N i))) * pinnedFamily N i =
      X i * X (complement N i) + C (primePoint N ℚ (complement N i)) * X i -
      C (primePoint N ℚ i) * X (complement N i) -
      C (primePoint N ℚ i * primePoint N ℚ (complement N i)) := by
    simp only [pinnedFamily, map_mul]
    ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    pinned_cross_sum]
  have hc : (∑ i : Fin (N + 1), C (primePoint N ℚ i * primePoint N ℚ (complement N i))) =
      (C (goldbachCount N : ℚ) : R N ℚ) := by
    simp [goldbachCount, primePoint, primeIndicator, complement,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, map_sum]
  rw [hc]
  simp only [g]
  ring

theorem pinned_control_certificate (N : ℕ) (hG : (goldbachCount N : ℚ) ≠ 0) :
    Certificate (pinnedFamily N) (pinnedMultiplier N) (fun _ => 0)
      (C ((goldbachCount N : ℚ)⁻¹)) := by
  unfold Certificate
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  have ht := pinned_telescoping N
  have hs : (∑ i : Fin (N + 1), pinnedMultiplier N i * pinnedFamily N i) =
      -C ((goldbachCount N : ℚ)⁻¹) *
      (∑ i : Fin (N + 1),
        (X (complement N i) + C (primePoint N ℚ (complement N i))) * pinnedFamily N i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pinnedMultiplier]
    ring
  rw [hs, ht]
  have hi : C ((goldbachCount N : ℚ)⁻¹) * C (goldbachCount N : ℚ) = (1 : R N ℚ) := by
    rw [← map_mul, inv_mul_cancel₀ hG, map_one]
  calc
    1 = C ((goldbachCount N : ℚ)⁻¹) * C (goldbachCount N : ℚ) := hi.symm
    _ = _ := by ring

theorem pinned_family_pins (N : ℕ) (x : Fin (N + 1) → ℚ)
    (hF : ∀ i, eval x (pinnedFamily N i) = 0) : x = primePoint N ℚ := by
  funext i
  have hi := hF i
  simpa [pinnedFamily, sub_eq_zero] using hi

theorem pinned_certificate_iff_goldbach (N : ℕ) :
    (∃ A U B, Certificate (pinnedFamily N) A U B) ↔ 0 < goldbachCount N := by
  constructor
  · rintro ⟨A, U, B, hc⟩
    exact certificate_goldbachCount_positive (pinnedFamily N) A U B hc (by simp [pinnedFamily])
  · intro hG
    have hn : (goldbachCount N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hG)
    exact ⟨pinnedMultiplier N, (fun _ => 0), C ((goldbachCount N : ℚ)⁻¹),
      pinned_control_certificate N hn⟩

theorem pinned_multiplier_degree_le_one (N : ℕ) (i : Fin (N + 1)) :
    (pinnedMultiplier N i).totalDegree ≤ 1 := by
  unfold pinnedMultiplier
  have hm := totalDegree_mul
    (-(X (complement N i) + C (primePoint N ℚ (complement N i))) : R N ℚ)
    (C ((goldbachCount N : ℚ)⁻¹))
  rw [totalDegree_neg, totalDegree_C, add_zero] at hm
  have ha := totalDegree_add (X (complement N i) : R N ℚ)
    (C (primePoint N ℚ (complement N i)))
  rw [totalDegree_X, totalDegree_C] at ha
  exact hm.trans (by simpa using ha)

theorem pinned_B_degree_zero (N : ℕ) :
    (C ((goldbachCount N : ℚ)⁻¹) : R N ℚ).totalDegree = 0 := totalDegree_C _

theorem pinned_summand_degree_le_two (N : ℕ) (i : Fin (N + 1)) :
    (pinnedMultiplier N i * pinnedFamily N i).totalDegree ≤ 2 := by
  have ha := pinned_multiplier_degree_le_one N i
  have hf : (pinnedFamily N i).totalDegree ≤ 1 := by
    unfold pinnedFamily
    have hs := totalDegree_sub (X i : R N ℚ) (C (primePoint N ℚ i))
    simpa using hs
  have hm := totalDegree_mul (pinnedMultiplier N i) (pinnedFamily N i)
  omega

theorem g_degree_le_two (N : ℕ) : (g N ℚ).totalDegree ≤ 2 := by
  unfold g
  apply totalDegree_finsetSum_le
  intro i _
  simpa using totalDegree_mul (X i : R N ℚ) (X (complement N i))

theorem pinned_g_summand_degree_le_two (N : ℕ) :
    (C ((goldbachCount N : ℚ)⁻¹) * g N ℚ).totalDegree ≤ 2 := by
  have hm := totalDegree_mul (C ((goldbachCount N : ℚ)⁻¹)) (g N ℚ)
  rw [totalDegree_C, zero_add] at hm
  exact hm.trans (g_degree_le_two N)

end
end AlgebraicGoldbach
