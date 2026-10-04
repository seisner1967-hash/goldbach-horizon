import RationalLogQuantization22
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

/-! SOURCE ONLY. All prime powers use the actual IsPrimePow/minFac definition.
The pointwise error comes from quantizedLog_precision, not a caller-supplied
precision premise. This module concerns a finite coefficient compass only. -/

noncomputable section
open scoped BigOperators
open GoldbachLogQuantization22

namespace GoldbachQuantizedCoefficient22

def integerLambda (n : ℕ) : ℤ := by
  classical
  exact if IsPrimePow n then logPoint (Nat.minFac n) else 0

def quantizedLambda (n : ℕ) : ℝ := (integerLambda n : ℝ) / (gridScale : ℝ)

def trueCoefficient (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1),
  ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (N - n)

def integerCoefficient (N : ℕ) : ℤ := ∑ n ∈ Finset.range (N + 1),
  integerLambda n * integerLambda (N - n)

def errorEnvelope (N : ℕ) (s : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) * (64 / s + 1 / s ^ 2)

theorem integerLambda_bounds (n : ℕ) :
    0 ≤ integerLambda n ∧ integerLambda n ≤ 32 * (gridScale : ℤ) := by
  classical
  unfold integerLambda
  split_ifs
  · exact logPoint_bounds _
  · constructor <;> positivity

theorem quantizedLambda_bounds (n : ℕ) :
    0 ≤ quantizedLambda n ∧ quantizedLambda n ≤ 32 := by
  have hs : (0 : ℝ) < (gridScale : ℝ) := by exact_mod_cast gridScale_pos
  obtain ⟨hn0, hn32⟩ := integerLambda_bounds n
  have h0 : 0 ≤ (integerLambda n : ℝ) := by exact_mod_cast hn0
  have h32 : (integerLambda n : ℝ) ≤ 32 * (gridScale : ℝ) := by exact_mod_cast hn32
  unfold quantizedLambda
  exact ⟨div_nonneg h0 hs.le, (div_le_iff₀ hs).mpr h32⟩

/-- Bound the actual Lambda directly from minFac and elementary log properties. -/
theorem trueLambda_bounds {n : ℕ} (hN : n ≤ 100000000) :
    0 ≤ ArithmeticFunction.vonMangoldt n ∧ ArithmeticFunction.vonMangoldt n ≤ 32 := by
  classical
  rw [ArithmeticFunction.vonMangoldt_apply]
  by_cases hn : IsPrimePow n
  · rw [if_pos hn]
    have hp := (Nat.minFac_prime hn.ne_one).two_le
    have hm := (Nat.minFac_le (Nat.pos_of_ne_zero hn.ne_zero)).trans hN
    exact true_log_bounds hp hm
  · simp only [if_neg hn]
    norm_num

theorem quantizedLambda_precision {n : ℕ} (hN : n ≤ 100000000) :
    |ArithmeticFunction.vonMangoldt n - quantizedLambda n| ≤ 1 / (gridScale : ℝ) := by
  classical
  rw [ArithmeticFunction.vonMangoldt_apply]
  unfold quantizedLambda integerLambda
  by_cases hn : IsPrimePow n
  · rw [if_pos hn, if_pos hn]
    have hp := (Nat.minFac_prime hn.ne_one).two_le
    have hm := (Nat.minFac_le (Nat.pos_of_ne_zero hn.ne_zero)).trans hN
    exact quantizedLog_precision hp hm
  · simp only [if_neg hn, Int.cast_zero, zero_div, sub_self, abs_zero]
    positivity

theorem quantized_product_error {m n : ℕ}
    (hm : m ≤ 100000000) (hn : n ≤ 100000000) :
    |ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n -
        quantizedLambda m * quantizedLambda n| ≤ 64 / (gridScale : ℝ) := by
  obtain ⟨hxm0, hxm32⟩ := trueLambda_bounds hm
  obtain ⟨hyn0, hyn32⟩ := quantizedLambda_bounds n
  have hem := quantizedLambda_precision hm
  have hen := quantizedLambda_precision hn
  have hs : (0 : ℝ) < (gridScale : ℝ) := by exact_mod_cast gridScale_pos
  calc
    _ = |ArithmeticFunction.vonMangoldt m *
          (ArithmeticFunction.vonMangoldt n - quantizedLambda n) +
          quantizedLambda n * (ArithmeticFunction.vonMangoldt m - quantizedLambda m)| := by
      congr 1
      ring
    _ ≤ |ArithmeticFunction.vonMangoldt m *
          (ArithmeticFunction.vonMangoldt n - quantizedLambda n)| +
          |quantizedLambda n * (ArithmeticFunction.vonMangoldt m - quantizedLambda m)| := abs_add _ _
    _ = ArithmeticFunction.vonMangoldt m *
          |ArithmeticFunction.vonMangoldt n - quantizedLambda n| +
          quantizedLambda n * |ArithmeticFunction.vonMangoldt m - quantizedLambda m| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hxm0, abs_of_nonneg hyn0]
    _ ≤ 32 * (1 / (gridScale : ℝ)) + 32 * (1 / (gridScale : ℝ)) := by
      gcongr
    _ = 64 / (gridScale : ℝ) := by ring

theorem quantizedCoefficient_eq_integer (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), quantizedLambda n * quantizedLambda (N - n)) =
      (integerCoefficient N : ℝ) / (gridScale : ℝ) ^ 2 := by
  unfold integerCoefficient
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  unfold quantizedLambda
  ring

/-- The final coefficient envelope has no free Lambda bound or precision input. -/
theorem coefficient_error_bound {N : ℕ} (hN : N ≤ 100000000) :
    |trueCoefficient N - (integerCoefficient N : ℝ) / (gridScale : ℝ) ^ 2| ≤
      errorEnvelope N (gridScale : ℝ) := by
  rw [← quantizedCoefficient_eq_integer]
  unfold trueCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        |ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (N - n) -
          quantizedLambda n * quantizedLambda (N - n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), (64 / (gridScale : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
      exact quantized_product_error (hnN.trans hN) ((Nat.sub_le N n).trans hN)
    _ = ((N + 1 : ℕ) : ℝ) * (64 / (gridScale : ℝ)) := by simp
    _ ≤ errorEnvelope N (gridScale : ℝ) := by
      unfold errorEnvelope
      have hpositive : (0 : ℝ) ≤ 1 / (gridScale : ℝ) ^ 2 := by positivity
      nlinarith [Nat.cast_nonneg (N + 1)]

theorem errorEnvelope_continuousOn (N : ℕ) :
    ContinuousOn (errorEnvelope N) (Set.Ioi (0 : ℝ)) := by
  intro s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  unfold errorEnvelope
  exact (continuous_const.continuousAt.mul
    ((continuous_const.continuousAt.div continuous_id.continuousAt hs0).add
      (continuous_const.continuousAt.div
        (continuous_id.continuousAt.pow 2) (pow_ne_zero 2 hs0)))).continuousWithinAt

theorem fixed_integer_tau_guard :
    2 * (100000000 + 1 : ℕ) * (64 * gridScale + 1) * 1000000 ≤ gridScale ^ 2 := by
  norm_num [gridScale]

end GoldbachQuantizedCoefficient22

#print axioms GoldbachQuantizedCoefficient22.integerLambda
#print axioms GoldbachQuantizedCoefficient22.quantizedLambda
#print axioms GoldbachQuantizedCoefficient22.trueCoefficient
#print axioms GoldbachQuantizedCoefficient22.integerCoefficient
#print axioms GoldbachQuantizedCoefficient22.errorEnvelope
#print axioms GoldbachQuantizedCoefficient22.integerLambda_bounds
#print axioms GoldbachQuantizedCoefficient22.quantizedLambda_bounds
#print axioms GoldbachQuantizedCoefficient22.trueLambda_bounds
#print axioms GoldbachQuantizedCoefficient22.quantizedLambda_precision
#print axioms GoldbachQuantizedCoefficient22.quantized_product_error
#print axioms GoldbachQuantizedCoefficient22.quantizedCoefficient_eq_integer
#print axioms GoldbachQuantizedCoefficient22.coefficient_error_bound
#print axioms GoldbachQuantizedCoefficient22.errorEnvelope_continuousOn
#print axioms GoldbachQuantizedCoefficient22.fixed_integer_tau_guard
