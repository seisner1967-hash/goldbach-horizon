import EpsteinKernel22
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Epstein22

def shiftKernel (y : ℝ) (m n : ℤ) (x : ℝ) : ℝ :=
  weight y * kernel (|(m : ℝ)| * y) ((m : ℝ) * x + n)

def shiftWindow (Q : ℕ) : Finset ℤ := Finset.Icc (-(Q : ℤ)) Q

def finiteShiftIntegral (y : ℝ) (m : ℤ) (Q : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∑ n ∈ shiftWindow Q, shiftKernel y m n x

def endpointSum (a : ℝ) (Q q : ℕ) : ℝ :=
  (∑ u ∈ Finset.Icc ((Q : ℤ) + 1) ((Q : ℤ) + q), boundary a u) -
    ∑ u ∈ Finset.Icc (-(Q : ℤ)) (-(Q : ℤ) + q - 1), boundary a u

theorem abs_cast_pos {m : ℤ} (hm : m ≠ 0) : 0 < |(m : ℝ)| := by
  exact abs_pos.mpr (by exact_mod_cast hm)

theorem shiftKernel_eq_rpow {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0)
    (n : ℤ) (x : ℝ) :
    shiftKernel y m n x = y ^ (3 / 2 : ℝ) /
      (((m : ℝ) * x + n) ^ 2 + ((m : ℝ) * y) ^ 2) ^ (3 / 2 : ℝ) := by
  unfold shiftKernel
  rw [weight_eq_rpow hy, kernel_eq_rpow (mul_pos (abs_cast_pos hm) hy)]
  have hr : radicand (|(m : ℝ)| * y) ((m : ℝ) * x + n) =
      ((m : ℝ) * x + n) ^ 2 + ((m : ℝ) * y) ^ 2 := by
    simp [radicand, mul_pow, sq_abs]
  rw [hr, show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
    Real.rpow_neg (by positivity)]
  rfl

theorem continuous_shiftKernel {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0)
    (n : ℤ) : Continuous (shiftKernel y m n) := by
  exact ((continuous_kernel (mul_pos (abs_cast_pos hm) hy)).comp
    ((continuous_const.mul continuous_id).add continuous_const)).const_mul _

theorem intervalIntegrable_shiftKernel {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0)
    (n : ℤ) (A B : ℝ) : IntervalIntegrable (shiftKernel y m n) volume A B :=
  (continuous_shiftKernel hy hm n).intervalIntegrable _ _

theorem affineCellIntegral {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, shiftKernel y m n x) =
      weight y / ((m : ℝ) * (|(m : ℝ)| * y) ^ 2) *
        (boundary (|(m : ℝ)| * y) ((n : ℝ) + m) -
          boundary (|(m : ℝ)| * y) n) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have ha := mul_pos (abs_cast_pos hm) hy
  unfold shiftKernel
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (kernel (|(m : ℝ)| * y)) hmR (n : ℝ)]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
  rw [integral_kernel_interval ha]
  unfold primitive
  field_simp [hmR, ha.ne']
  ring

theorem shiftKernel_neg_isometry (y x : ℝ) (m n : ℤ) :
    shiftKernel y (-m) n x = shiftKernel y m (-n) x := by
  unfold shiftKernel
  simp only [Int.cast_neg, abs_neg]
  have h : (-(m : ℝ) * x + n) = -((m : ℝ) * x + (-(n : ℝ))) := by ring
  rw [h, kernel_even]

theorem finiteWindow_neg_isometry (y x : ℝ) (m : ℤ) (Q : ℕ) :
    (∑ n ∈ shiftWindow Q, shiftKernel y (-m) n x) =
      ∑ n ∈ shiftWindow Q, shiftKernel y m n x := by
  classical
  refine Finset.sum_bij (fun n _ => -n) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [shiftWindow, Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn k hk hnk
    exact neg_injective hnk
  · intro n hn
    refine ⟨-n, ?_, by simp⟩
    simp only [shiftWindow, Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn
    exact shiftKernel_neg_isometry y x m n

theorem finiteShiftIntegral_neg (y : ℝ) (m : ℤ) (Q : ℕ) :
    finiteShiftIntegral y (-m) Q = finiteShiftIntegral y m Q := by
  unfold finiteShiftIntegral
  apply intervalIntegral.integral_congr
  intro x _
  exact finiteWindow_neg_isometry y x m Q

theorem sum_int_Icc (f : ℤ → ℝ) (L U : ℤ) :
    (∑ n ∈ Finset.Icc L U, f n) =
      ∑ i ∈ Finset.range (U + 1 - L).toNat, f (L + (i : ℤ)) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  rfl

theorem range_shift_telescope (f : ℕ → ℝ) (M q : ℕ) :
    (∑ i ∈ Finset.range M, (f (i + q) - f i)) =
      ∑ i ∈ Finset.range q, (f (M + i) - f i) := by
  have h1 := Finset.sum_range_add f q M
  have h2 := Finset.sum_range_add f M q
  rw [Nat.add_comm q M] at h1
  simp_rw [Nat.add_comm q] at h1
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith

theorem sum_Icc_shift_telescope (f : ℤ → ℝ) (L U : ℤ) (q : ℕ)
    (hLU : L ≤ U + 1) :
    (∑ n ∈ Finset.Icc L U, (f (n + q) - f n)) =
      (∑ u ∈ Finset.Icc (U + 1) (U + q), f u) -
        ∑ u ∈ Finset.Icc L (L + q - 1), f u := by
  let M := (U + 1 - L).toNat
  have hM : (M : ℤ) = U + 1 - L := by dsimp [M]; omega
  have htop : (U + (q : ℤ) + 1 - (U + 1)).toNat = q := by omega
  have hbot : (L + (q : ℤ) - 1 + 1 - L).toNat = q := by omega
  calc
    (∑ n ∈ Finset.Icc L U, (f (n + q) - f n)) =
        ∑ i ∈ Finset.range M, (f (L + ((i + q : ℕ) : ℤ)) - f (L + (i : ℤ))) := by
      rw [sum_int_Icc]
      apply Finset.sum_congr rfl
      intro i _
      simp [Nat.cast_add, add_assoc]
    _ = ∑ i ∈ Finset.range q,
        (f (L + ((M + i : ℕ) : ℤ)) - f (L + (i : ℤ))) :=
      range_shift_telescope (fun i => f (L + (i : ℤ))) M q
    _ = (∑ u ∈ Finset.Icc (U + 1) (U + q), f u) -
        ∑ u ∈ Finset.Icc L (L + q - 1), f u := by
      rw [sum_int_Icc, sum_int_Icc, htop, hbot, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      simp only [Nat.cast_add]
      omega

theorem finiteShiftIntegral_pos_formula {y : ℝ} (hy : 0 < y) {q : ℕ} (hq : 0 < q)
    (Q : ℕ) :
    finiteShiftIntegral y (q : ℤ) Q =
      weight y / ((q : ℝ) * ((q : ℝ) * y) ^ 2) * endpointSum ((q : ℝ) * y) Q q := by
  have hqI : (q : ℤ) ≠ 0 := by omega
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  unfold finiteShiftIntegral
  rw [intervalIntegral.integral_finset_sum
    (fun n _ => intervalIntegrable_shiftKernel hy hqI n 0 1)]
  simp_rw [affineCellIntegral hy hqI]
  simp only [Int.cast_natCast, abs_of_pos hqR]
  rw [← Finset.mul_sum]
  congr 1
  unfold shiftWindow endpointSum
  have ht := sum_Icc_shift_telescope
    (fun u : ℤ => boundary ((q : ℝ) * y) u) (-(Q : ℤ)) (Q : ℤ) q (by omega)
  simpa [Int.cast_add, Int.cast_natCast, add_comm] using ht

theorem finiteShiftIntegral_natAbs {y : ℝ} (m : ℤ) (Q : ℕ) :
    finiteShiftIntegral y m Q = finiteShiftIntegral y (m.natAbs : ℤ) Q := by
  cases m with
  | ofNat n => rfl
  | negSucc n =>
    simpa using finiteShiftIntegral_neg y ((n + 1 : ℕ) : ℤ) Q

theorem finiteShiftIntegral_formula {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0)
    (Q : ℕ) :
    finiteShiftIntegral y m Q =
      weight y / ((m.natAbs : ℝ) * ((m.natAbs : ℝ) * y) ^ 2) *
        endpointSum ((m.natAbs : ℝ) * y) Q m.natAbs := by
  rw [finiteShiftIntegral_natAbs]
  exact finiteShiftIntegral_pos_formula hy (Int.natAbs_pos.mpr hm) Q

end Epstein22

#print axioms Epstein22.shiftKernel
#print axioms Epstein22.shiftWindow
#print axioms Epstein22.finiteShiftIntegral
#print axioms Epstein22.endpointSum
#print axioms Epstein22.abs_cast_pos
#print axioms Epstein22.shiftKernel_eq_rpow
#print axioms Epstein22.continuous_shiftKernel
#print axioms Epstein22.intervalIntegrable_shiftKernel
#print axioms Epstein22.affineCellIntegral
#print axioms Epstein22.shiftKernel_neg_isometry
#print axioms Epstein22.finiteWindow_neg_isometry
#print axioms Epstein22.finiteShiftIntegral_neg
#print axioms Epstein22.sum_int_Icc
#print axioms Epstein22.range_shift_telescope
#print axioms Epstein22.sum_Icc_shift_telescope
#print axioms Epstein22.finiteShiftIntegral_pos_formula
#print axioms Epstein22.finiteShiftIntegral_natAbs
#print axioms Epstein22.finiteShiftIntegral_formula
