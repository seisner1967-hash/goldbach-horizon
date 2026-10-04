import Mathlib.Tactic

/-!
# Finite algebra of the arithmetic Goldbach bridge

The coefficient `mu` is an arbitrary real-valued function. Consequently the
weighted Cauchy inequality can later be specialized to the actual Moebius
function, without assuming its distribution. The row kernel `h` can retain
the actual centered progression indicator and moving cofactor endpoint.

These theorems prove finite algebra only. They assert no estimate for the
signed off-diagonal, no prime distribution hypothesis, and no Goldbach proof.
-/

namespace GoldbachResearch.ArithmeticBridge

open scoped BigOperators

variable {I J : Type*}

/-- Cauchy with reciprocal positive weights and arbitrary signed coefficients. -/
theorem weighted_signed_cauchy (s : Finset I) (w mu eps : I → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, mu i * eps i) ^ 2 ≤
      (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, w i * (mu i) ^ 2 * (eps i) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
  · intro i hi
    exact le_of_lt (one_div_pos.mpr (hw i hi))
  · intro i hi
    exact mul_nonneg (mul_nonneg (le_of_lt (hw i hi)) (sq_nonneg _)) (sq_nonneg _)
  · intro i hi
    have hwi : w i ≠ 0 := ne_of_gt (hw i hi)
    field_simp [hwi]
    ring

/-- The exact diagonal/off-diagonal split of a finite square. -/
theorem square_sum_split [DecidableEq J] (t : Finset J) (f : J → ℝ) :
    (∑ n ∈ t, f n) ^ 2 = (∑ n ∈ t, (f n) ^ 2) +
      ∑ n ∈ t, ∑ r ∈ t.erase n, f n * f r := by
  calc
    (∑ n ∈ t, f n) ^ 2 = ∑ n ∈ t, f n * (∑ r ∈ t, f r) := by
      rw [pow_two, Finset.sum_mul]
    _ = ∑ n ∈ t, ((f n) ^ 2 + ∑ r ∈ t.erase n, f n * f r) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hsplit : (∑ r ∈ t.erase n, f r) + f n = ∑ r ∈ t, f r :=
        Finset.sum_erase_add _ _ hn
      rw [← Finset.mul_sum, ← hsplit]
      ring
    _ = _ := Finset.sum_add_distrib

noncomputable def rowSum (t : Finset J) (a : J → ℝ) (h : I → J → ℝ) (k : I) : ℝ :=
  ∑ n ∈ t, a n * h k n

noncomputable def variance (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ) : ℝ :=
  ∑ k ∈ s, w k * (mu k) ^ 2 * (rowSum t a h k) ^ 2

noncomputable def diagonal (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ) : ℝ :=
  ∑ k ∈ s, ∑ n ∈ t, w k * (mu k) ^ 2 * (a n * h k n) ^ 2

noncomputable def offDiagonal [DecidableEq J] (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ) : ℝ :=
  ∑ k ∈ s, ∑ n ∈ t, ∑ r ∈ t.erase n,
    w k * (mu k) ^ 2 * ((a n * h k n) * (a r * h k r))

noncomputable def gramKernel (s : Finset I) (w mu : I → ℝ)
    (h : I → J → ℝ) (n r : J) : ℝ :=
  ∑ k ∈ s, w k * (mu k) ^ 2 * (h k n * h k r)

/-- No mixed term is dropped when the actual row variance is expanded. -/
theorem variance_eq_diagonal_add_offDiagonal [DecidableEq J] (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ) :
    variance s t w mu a h = diagonal s t w mu a h + offDiagonal s t w mu a h := by
  unfold variance rowSum diagonal offDiagonal
  simp_rw [square_sum_split, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]

/-- The row variance is precisely the quadratic form of its centered Gram kernel. -/
theorem variance_eq_gramKernel (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ) :
    variance s t w mu a h =
      ∑ n ∈ t, ∑ r ∈ t, a n * a r * gramKernel s w mu h n r := by
  have hexpand : variance s t w mu a h =
      ∑ k ∈ s, ∑ n ∈ t, ∑ r ∈ t,
        w k * (mu k) ^ 2 * ((a n * h k n) * (a r * h k r)) := by
    unfold variance rowSum
    simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  rw [hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  unfold gramKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The centered row Gram is nonnegative for nonnegative row weights. -/
theorem variance_nonneg (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) : 0 ≤ variance s t w mu a h := by
  unfold variance
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (mul_nonneg (hw k hk) (sq_nonneg _)) (sq_nonneg _)

theorem diagonal_nonneg (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) : 0 ≤ diagonal s t w mu a h := by
  unfold diagonal
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (mul_nonneg (hw k hk) (sq_nonneg _)) (sq_nonneg _)

/-- Specialization of weighted Cauchy to the actual finite row sums. -/
theorem signed_rows_sq_le_variance (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ)
    (hw : ∀ k ∈ s, 0 < w k) :
    (∑ k ∈ s, mu k * rowSum t a h k) ^ 2 ≤
      (∑ k ∈ s, 1 / w k) * variance s t w mu a h := by
  exact weighted_signed_cauchy s w mu (rowSum t a h) hw

/-- Finite one-sided off-diagonal bounds transfer without requiring a sign assumption. -/
theorem signed_rows_sq_le_diagonal_off_budget [DecidableEq J]
    (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ)
    (hw : ∀ k ∈ s, 0 < w k) (d o : ℝ)
    (hd : diagonal s t w mu a h ≤ d) (ho : offDiagonal s t w mu a h ≤ o) :
    (∑ k ∈ s, mu k * rowSum t a h k) ^ 2 ≤
      (∑ k ∈ s, 1 / w k) * (d + o) := by
  have hmass : 0 ≤ ∑ k ∈ s, 1 / w k := by
    apply Finset.sum_nonneg
    intro k hk
    exact le_of_lt (one_div_pos.mpr (hw k hk))
  have hvar : variance s t w mu a h ≤ d + o := by
    rw [variance_eq_diagonal_add_offDiagonal]
    exact add_le_add hd ho
  exact le_trans (signed_rows_sq_le_variance s t w mu a h hw)
    (mul_le_mul_of_nonneg_left hvar hmass)

theorem gramKernel_symmetric (s : Finset I) (w mu : I → ℝ)
    (h : I → J → ℝ) (n r : J) :
    gramKernel s w mu h n r = gramKernel s w mu h r n := by
  unfold gramKernel
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Every finite quadratic form of the Gram kernel is nonnegative. -/
theorem gramKernel_positive_semidefinite (s : Finset I) (t : Finset J)
    (w mu : I → ℝ) (a : J → ℝ) (h : I → J → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    0 ≤ ∑ n ∈ t, ∑ r ∈ t, a n * a r * gramKernel s w mu h n r := by
  rw [← variance_eq_gramKernel]
  exact variance_nonneg s t w mu a h hw

end GoldbachResearch.ArithmeticBridge

#print axioms GoldbachResearch.ArithmeticBridge.weighted_signed_cauchy
#print axioms GoldbachResearch.ArithmeticBridge.square_sum_split
#print axioms GoldbachResearch.ArithmeticBridge.variance_eq_diagonal_add_offDiagonal
#print axioms GoldbachResearch.ArithmeticBridge.variance_eq_gramKernel
#print axioms GoldbachResearch.ArithmeticBridge.variance_nonneg
#print axioms GoldbachResearch.ArithmeticBridge.diagonal_nonneg
#print axioms GoldbachResearch.ArithmeticBridge.signed_rows_sq_le_variance
#print axioms GoldbachResearch.ArithmeticBridge.signed_rows_sq_le_diagonal_off_budget
#print axioms GoldbachResearch.ArithmeticBridge.gramKernel_symmetric
#print axioms GoldbachResearch.ArithmeticBridge.gramKernel_positive_semidefinite
