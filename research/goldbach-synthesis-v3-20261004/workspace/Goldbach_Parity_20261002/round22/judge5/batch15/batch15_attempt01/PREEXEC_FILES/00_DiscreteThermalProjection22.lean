import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-! SOURCE ONLY. The grid characters below are concrete complex exponentials.
Their orthogonality is derived from the primitive root and the finite geometric
sum, not supplied as a premise. A0 excludes signed aliases on the whole finite
rectangle. The thermal trace uses the actual von Mangoldt function, including
all prime powers. This finite circle identity gives no D_N estimate or WIN.
No earlier ThermalProjectionIdentity22 source or object file is imported. -/

noncomputable section
open scoped BigOperators

namespace GoldbachDiscreteCircle22

def gridRoot (K : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (K : ℂ))

def gridCharacter (K : ℕ) (k : ℤ) (j : ℕ) : ℂ :=
  Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (K : ℂ)))

def gridAngle (K j : ℕ) : ℝ := 2 * Real.pi * (j : ℝ) / (K : ℝ)

theorem gridRoot_primitive {K : ℕ} (hK : 0 < K) : IsPrimitiveRoot (gridRoot K) K := by
  exact Complex.isPrimitiveRoot_exp K (Nat.ne_of_gt hK)

theorem gridCharacter_eq_root_pow (K : ℕ) (k : ℤ) (j : ℕ) :
    gridCharacter K k j = (gridRoot K ^ k) ^ j := by
  unfold gridCharacter gridRoot
  rw [← Complex.exp_int_mul, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem gridCharacter_eq_angle (K : ℕ) (k : ℤ) (j : ℕ) :
    gridCharacter K k j =
      Complex.exp (((k : ℂ) * Complex.I) * (gridAngle K j : ℂ)) := by
  unfold gridCharacter gridAngle
  congr 1
  push_cast <;> ring

/-- The signed character sum retains every alias, including negative ones. -/
theorem sum_gridCharacter {K : ℕ} (hK : 0 < K) (k : ℤ) :
    (∑ j ∈ Finset.range K, gridCharacter K k j) =
      if (K : ℤ) ∣ k then (K : ℂ) else 0 := by
  have hp := gridRoot_primitive hK
  simp_rw [gridCharacter_eq_root_pow]
  by_cases hd : (K : ℤ) ∣ k
  · have hx : gridRoot K ^ k = 1 := (hp.zpow_eq_one_iff_dvd k).mpr hd
    simp [hd, hx]
  · have hx : gridRoot K ^ k ≠ 1 := by
      intro hx
      exact hd ((hp.zpow_eq_one_iff_dvd k).mp hx)
    have hperiod : (gridRoot K ^ k) ^ K = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm k (K : ℤ), zpow_mul,
        hp.zpow_eq_one, one_zpow]
    have hg : (gridRoot K ^ k - 1) *
        (∑ j ∈ Finset.range K, (gridRoot K ^ k) ^ j) = 0 := by
      rw [mul_geom_sum, hperiod, sub_self]
    have hz : (∑ j ∈ Finset.range K, (gridRoot K ^ k) ^ j) = 0 :=
      (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr hx)
    simpa only [if_neg hd] using hz

/-- A multiple of K strictly between -K and K is necessarily zero. -/
theorem grid_divides_iff_zero {K : ℕ} (hK : 0 < K) {k : ℤ}
    (hlo : -(K : ℤ) < k) (hhi : k < (K : ℤ)) :
    (K : ℤ) ∣ k ↔ k = 0 := by
  constructor
  · rintro ⟨l, hl⟩
    have hKz : (0 : ℤ) < (K : ℤ) := by exact_mod_cast hK
    by_cases hl0 : l = 0
    · simpa [hl0] using hl
    · have hsign : l ≤ -1 ∨ 1 ≤ l := by omega
      rcases hsign with hneg | hpos
      · have hmul : (K : ℤ) * (l + 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hKz.le (by omega)
        nlinarith
      · have hmul : 0 ≤ (K : ℤ) * (l - 1) :=
          mul_nonneg hKz.le (by omega)
        nlinarith
  · rintro rfl
    exact dvd_zero _

theorem sum_gridCharacter_no_alias {K : ℕ} (hK : 0 < K) (k : ℤ)
    (hlo : -(K : ℤ) < k) (hhi : k < (K : ℤ)) :
    (∑ j ∈ Finset.range K, gridCharacter K k j) =
      if k = 0 then (K : ℂ) else 0 := by
  rw [sum_gridCharacter hK]
  simp only [grid_divides_iff_zero hK hlo hhi]

/-- A0 is paid for every frequency in the finite rectangle. -/
theorem rectangle_frequency_bounds {N M K m n : ℕ}
    (hA0 : max N (2 * M - N) < K) (hm : m ≤ M) (hn : n ≤ M) :
    -(K : ℤ) < (m : ℤ) + (n : ℤ) - (N : ℤ) ∧
      (m : ℤ) + (n : ℤ) - (N : ℤ) < (K : ℤ) := by
  have hNK : N < K := (le_max_left N (2 * M - N)).trans_lt hA0
  have hupper : 2 * M - N < K := (le_max_right N (2 * M - N)).trans_lt hA0
  omega

theorem sum_rectangle_character {N M K m n : ℕ}
    (hA0 : max N (2 * M - N) < K) (hm : m ≤ M) (hn : n ≤ M) :
    (∑ j ∈ Finset.range K,
      gridCharacter K ((m : ℤ) + (n : ℤ) - (N : ℤ)) j) =
      if m + n = N then (K : ℂ) else 0 := by
  have hK : 0 < K := by
    have hNK := (le_max_left N (2 * M - N)).trans_lt hA0
    omega
  obtain ⟨hlo, hhi⟩ := rectangle_frequency_bounds hA0 hm hn
  rw [sum_gridCharacter_no_alias hK _ hlo hhi]
  have hz : (m : ℤ) + (n : ℤ) - (N : ℤ) = 0 ↔ m + n = N := by omega
  simp only [hz]

def heatRatio (a : ℝ) : ℝ := Real.exp (-a)

def discreteHeatTerm (a : ℝ) (K n j : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (heatRatio a : ℂ) ^ n *
    gridCharacter K (n : ℤ) j

def discreteHeatPartial (a : ℝ) (K M j : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (M + 1), discreteHeatTerm a K n j

def trueCircleHeatPartial (a theta : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (M + 1),
    ((ArithmeticFunction.vonMangoldt n * Real.exp (-a * (n : ℝ)) : ℝ) : ℂ) *
      Complex.exp (((n : ℂ) * Complex.I) * (theta : ℂ))

def lambdaCoefficient (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal N,
    ArithmeticFunction.vonMangoldt p.1 * ArithmeticFunction.vonMangoldt p.2

def discreteThermalProjection (a : ℝ) (N M K : ℕ) : ℂ :=
  ((Real.exp (a * (N : ℝ)) / (K : ℝ) : ℝ) : ℂ) *
    ∑ j ∈ Finset.range K,
      discreteHeatPartial a K M j ^ 2 * gridCharacter K (-(N : ℤ)) j

theorem heatRatio_pow (a : ℝ) (n : ℕ) :
    heatRatio a ^ n = Real.exp (-a * (n : ℝ)) := by
  unfold heatRatio
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem discreteHeatPartial_eq_trueCircle (a : ℝ) (K M j : ℕ) :
    discreteHeatPartial a K M j = trueCircleHeatPartial a (gridAngle K j) M := by
  unfold discreteHeatPartial trueCircleHeatPartial
  apply Finset.sum_congr rfl
  intro n hn
  unfold discreteHeatTerm
  rw [gridCharacter_eq_angle]
  have hpow : (heatRatio a : ℂ) ^ n = (Real.exp (-a * (n : ℝ)) : ℂ) := by
    exact_mod_cast heatRatio_pow a n
  rw [hpow]
  push_cast <;> ring

theorem gridCharacter_pair (K N m n j : ℕ) :
    gridCharacter K (m : ℤ) j * gridCharacter K (n : ℤ) j *
      gridCharacter K (-(N : ℤ)) j =
        gridCharacter K ((m : ℤ) + (n : ℤ) - (N : ℤ)) j := by
  unfold gridCharacter
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast <;> ring

theorem discreteHeat_pair (a : ℝ) (K N m n j : ℕ) :
    discreteHeatTerm a K m j * discreteHeatTerm a K n j *
      gridCharacter K (-(N : ℤ)) j =
      ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (heatRatio a : ℂ) ^ (m + n) *
        gridCharacter K ((m : ℤ) + (n : ℤ) - (N : ℤ)) j := by
  calc
    _ = ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (heatRatio a : ℂ) ^ (m + n) *
        (gridCharacter K (m : ℤ) j * gridCharacter K (n : ℤ) j *
          gridCharacter K (-(N : ℤ)) j) := by
      unfold discreteHeatTerm
      rw [pow_add]
      push_cast <;> ring
    _ = _ := by rw [gridCharacter_pair]

theorem discrete_normalizer_cancel (a : ℝ) (N : ℕ) {K : ℕ} (hK : 0 < K) :
    ((Real.exp (a * (N : ℝ)) / (K : ℝ) : ℝ) : ℂ) *
      (heatRatio a : ℂ) ^ N * (K : ℂ) = 1 := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hpow : heatRatio a ^ N = Real.exp (-(a * (N : ℝ))) := by
    rw [heatRatio_pow]
    congr 1
    ring
  have hr : Real.exp (a * (N : ℝ)) / (K : ℝ) * heatRatio a ^ N * (K : ℝ) = 1 := by
    rw [hpow, Real.exp_neg]
    field_simp [hKr, Real.exp_ne_zero] <;> ring
  have hc := congrArg Complex.ofReal hr
  push_cast at hc ⊢
  exact hc

theorem normalized_discrete_pair (a : ℝ) {N M K m n : ℕ}
    (hA0 : max N (2 * M - N) < K) (hm : m ≤ M) (hn : n ≤ M) :
    ((Real.exp (a * (N : ℝ)) / (K : ℝ) : ℝ) : ℂ) *
      (∑ j ∈ Finset.range K,
        discreteHeatTerm a K m j * discreteHeatTerm a K n j *
          gridCharacter K (-(N : ℤ)) j) =
      if m + n = N then
        ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
      else 0 := by
  have hK : 0 < K := by
    have hNK := (le_max_left N (2 * M - N)).trans_lt hA0
    omega
  simp_rw [discreteHeat_pair]
  rw [← Finset.mul_sum, sum_rectangle_character hA0 hm hn]
  by_cases hmn : m + n = N
  · rw [if_pos hmn, if_pos hmn, hmn]
    calc
      _ = ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (((Real.exp (a * (N : ℝ)) / (K : ℝ) : ℝ) : ℂ) *
            (heatRatio a : ℂ) ^ N * (K : ℂ)) := by ring
      _ = _ := by rw [discrete_normalizer_cancel a N hK, mul_one]
  · simp only [if_neg hmn, mul_zero]

theorem discretePartial_square_expansion (a : ℝ) (N M K j : ℕ) :
    discreteHeatPartial a K M j ^ 2 * gridCharacter K (-(N : ℤ)) j =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        discreteHeatTerm a K p.1 j * discreteHeatTerm a K p.2 j *
          gridCharacter K (-(N : ℤ)) j := by
  unfold discreteHeatPartial
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  simp_rw [Finset.sum_mul]

theorem discreteProjection_eq_rectangle (a : ℝ) {N M K : ℕ}
    (hA0 : max N (2 * M - N) < K) :
    discreteThermalProjection a N M K =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        if p.1 + p.2 = N then
          ((ArithmeticFunction.vonMangoldt p.1 * ArithmeticFunction.vonMangoldt p.2 : ℝ) : ℂ)
        else 0 := by
  unfold discreteThermalProjection
  simp_rw [discretePartial_square_expansion]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_product.mp hp
  have hm : p.1 ≤ M := by have := Finset.mem_range.mp hp'.1; omega
  have hn : p.2 ≤ M := by have := Finset.mem_range.mp hp'.2; omega
  exact normalized_discrete_pair a hA0 hm hn

theorem rectangle_filter_antidiagonal {N M : ℕ} (hNM : N ≤ M) :
    (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = N) = Finset.antidiagonal N := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact ⟨⟨by omega, by omega⟩, hp⟩

/-- CIRCLE with its explicit A0 guard and the genuine prime-power weights. -/
theorem discreteThermalProjection_eq_coefficient (a : ℝ) {N M K : ℕ}
    (hNM : N ≤ M) (hA0 : max N (2 * M - N) < K) :
    discreteThermalProjection a N M K = (lambdaCoefficient N : ℂ) := by
  rw [discreteProjection_eq_rectangle a hA0, ← Finset.sum_filter,
    rectangle_filter_antidiagonal hNM]
  unfold lambdaCoefficient
  push_cast <;> rfl

theorem lambdaCoefficient_eq_sum (N : ℕ) :
    lambdaCoefficient N = ∑ n ∈ Finset.range (N + 1),
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (N - n) := by
  unfold lambdaCoefficient
  rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map] <;> rfl

/-- The same exact identity written on the concrete angles 2*pi*j/K. -/
theorem sampled_trueCircle_eq_coefficient (a : ℝ) {N M K : ℕ}
    (hNM : N ≤ M) (hA0 : max N (2 * M - N) < K) :
    ((Real.exp (a * (N : ℝ)) / (K : ℝ) : ℝ) : ℂ) *
      (∑ j ∈ Finset.range K,
        trueCircleHeatPartial a (gridAngle K j) M ^ 2 *
          Complex.exp (((-(N : ℤ) : ℂ) * Complex.I) * (gridAngle K j : ℂ))) =
      ((∑ n ∈ Finset.range (N + 1),
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (N - n) : ℝ) : ℂ) := by
  have h := discreteThermalProjection_eq_coefficient a hNM hA0
  unfold discreteThermalProjection at h
  simp_rw [discreteHeatPartial_eq_trueCircle, gridCharacter_eq_angle] at h
  rw [lambdaCoefficient_eq_sum] at h
  simpa only [Int.cast_neg] using h

end GoldbachDiscreteCircle22

#print axioms GoldbachDiscreteCircle22.gridRoot
#print axioms GoldbachDiscreteCircle22.gridCharacter
#print axioms GoldbachDiscreteCircle22.gridAngle
#print axioms GoldbachDiscreteCircle22.gridRoot_primitive
#print axioms GoldbachDiscreteCircle22.gridCharacter_eq_root_pow
#print axioms GoldbachDiscreteCircle22.gridCharacter_eq_angle
#print axioms GoldbachDiscreteCircle22.sum_gridCharacter
#print axioms GoldbachDiscreteCircle22.grid_divides_iff_zero
#print axioms GoldbachDiscreteCircle22.sum_gridCharacter_no_alias
#print axioms GoldbachDiscreteCircle22.rectangle_frequency_bounds
#print axioms GoldbachDiscreteCircle22.sum_rectangle_character
#print axioms GoldbachDiscreteCircle22.heatRatio
#print axioms GoldbachDiscreteCircle22.discreteHeatTerm
#print axioms GoldbachDiscreteCircle22.discreteHeatPartial
#print axioms GoldbachDiscreteCircle22.trueCircleHeatPartial
#print axioms GoldbachDiscreteCircle22.lambdaCoefficient
#print axioms GoldbachDiscreteCircle22.discreteThermalProjection
#print axioms GoldbachDiscreteCircle22.heatRatio_pow
#print axioms GoldbachDiscreteCircle22.discreteHeatPartial_eq_trueCircle
#print axioms GoldbachDiscreteCircle22.gridCharacter_pair
#print axioms GoldbachDiscreteCircle22.discreteHeat_pair
#print axioms GoldbachDiscreteCircle22.discrete_normalizer_cancel
#print axioms GoldbachDiscreteCircle22.normalized_discrete_pair
#print axioms GoldbachDiscreteCircle22.discretePartial_square_expansion
#print axioms GoldbachDiscreteCircle22.discreteProjection_eq_rectangle
#print axioms GoldbachDiscreteCircle22.rectangle_filter_antidiagonal
#print axioms GoldbachDiscreteCircle22.discreteThermalProjection_eq_coefficient
#print axioms GoldbachDiscreteCircle22.lambdaCoefficient_eq_sum
#print axioms GoldbachDiscreteCircle22.sampled_trueCircle_eq_coefficient
