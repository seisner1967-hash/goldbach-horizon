import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.ZMod.Basic
import QuantizedLambdaEnvelope22
import Mathlib.Tactic

/-! SOURCE ONLY: no compiler invocation or verified elaboration claimed.
The finite geometric sum proves character orthogonality. The primitive-root
and characteristic guards are explicit algebraic domain hypotheses; no final
projection equality, orthogonality, arithmetic bound, or precision is assumed.
The concrete integerLambda is the independently compiled A32 constructor,
including every true prime power. This source does not prove any radix-2
butterfly, machine/GMP refinement, CRT reconstruction, five concrete root
certificates, Goldbach, D_N bound, or parity cancellation. -/

noncomputable section
open scoped BigOperators

namespace GoldbachFiniteFieldProjection22

variable {F : Type*} [Field F]

def fieldCharacter (ω : F) (k : ℤ) (j : ℕ) : F := (ω ^ k) ^ j

/-- Every signed alias is retained before the finite-size guard is used. -/
theorem sum_fieldCharacter {ω : F} {K : ℕ} (hω : IsPrimitiveRoot ω K)
    (hK : 0 < K) (k : ℤ) :
    (∑ j ∈ Finset.range K, fieldCharacter ω k j) =
      if (K : ℤ) ∣ k then (K : F) else 0 := by
  unfold fieldCharacter
  by_cases hd : (K : ℤ) ∣ k
  · have hx : ω ^ k = 1 := (hω.zpow_eq_one_iff_dvd k).mpr hd
    simp [hd, hx]
  · have hx : ω ^ k ≠ 1 := by
      intro hx
      exact hd ((hω.zpow_eq_one_iff_dvd k).mp hx)
    have hperiod : (ω ^ k) ^ K = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm k (K : ℤ), zpow_mul,
        hω.zpow_eq_one, one_zpow]
    have hg : (ω ^ k - 1) * (∑ j ∈ Finset.range K, (ω ^ k) ^ j) = 0 := by
      rw [mul_geom_sum, hperiod, sub_self]
    have hz : (∑ j ∈ Finset.range K, (ω ^ k) ^ j) = 0 :=
      (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr hx)
    simpa only [if_neg hd] using hz

theorem signed_divides_iff_zero {K : ℕ} (hK : 0 < K) {k : ℤ}
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

theorem sum_fieldCharacter_no_alias {ω : F} {K : ℕ}
    (hω : IsPrimitiveRoot ω K) (hK : 0 < K) (k : ℤ)
    (hlo : -(K : ℤ) < k) (hhi : k < (K : ℤ)) :
    (∑ j ∈ Finset.range K, fieldCharacter ω k j) =
      if k = 0 then (K : F) else 0 := by
  rw [sum_fieldCharacter hω hK]
  simp only [signed_divides_iff_zero hK hlo hhi]

theorem rectangle_frequency_bounds {N M K m n : ℕ}
    (hA0 : max N (2 * M - N) < K) (hm : m ≤ M) (hn : n ≤ M) :
    -(K : ℤ) < (m : ℤ) + (n : ℤ) - (N : ℤ) ∧
      (m : ℤ) + (n : ℤ) - (N : ℤ) < (K : ℤ) := by
  have hNK : N < K := (le_max_left N (2 * M - N)).trans_lt hA0
  have hupper : 2 * M - N < K := (le_max_right N (2 * M - N)).trans_lt hA0
  omega

theorem sum_rectangle_character {ω : F} {N M K m n : ℕ}
    (hω : IsPrimitiveRoot ω K) (hA0 : max N (2 * M - N) < K)
    (hm : m ≤ M) (hn : n ≤ M) :
    (∑ j ∈ Finset.range K,
      fieldCharacter ω ((m : ℤ) + (n : ℤ) - (N : ℤ)) j) =
      if m + n = N then (K : F) else 0 := by
  have hK : 0 < K := by
    have hNK := (le_max_left N (2 * M - N)).trans_lt hA0
    omega
  obtain ⟨hlo, hhi⟩ := rectangle_frequency_bounds hA0 hm hn
  rw [sum_fieldCharacter_no_alias hω hK _ hlo hhi]
  have hz : (m : ℤ) + (n : ℤ) - (N : ℤ) = 0 ↔ m + n = N := by omega
  simp only [hz]

theorem fieldCharacter_pair {ω : F} (hω0 : ω ≠ 0) (N m n j : ℕ) :
    fieldCharacter ω (m : ℤ) j * fieldCharacter ω (n : ℤ) j *
      fieldCharacter ω (-(N : ℤ)) j =
        fieldCharacter ω ((m : ℤ) + (n : ℤ) - (N : ℤ)) j := by
  unfold fieldCharacter
  calc
    _ = (ω ^ (m : ℤ) * ω ^ (n : ℤ) * ω ^ (-(N : ℤ))) ^ j := by
      rw [mul_pow, mul_pow]
    _ = _ := by
      rw [sub_eq_add_neg, zpow_add₀ hω0, zpow_add₀ hω0]

def fieldTerm (ω : F) (x : ℕ → F) (n j : ℕ) : F :=
  x n * fieldCharacter ω (n : ℤ) j

def fieldPolynomial (ω : F) (x : ℕ → F) (M j : ℕ) : F :=
  ∑ n ∈ Finset.range (M + 1), fieldTerm ω x n j

def fieldProjection (ω : F) (x : ℕ → F) (N M K : ℕ) : F :=
  (K : F)⁻¹ * ∑ j ∈ Finset.range K,
    fieldPolynomial ω x M j ^ 2 * fieldCharacter ω (-(N : ℤ)) j

theorem fieldTerm_pair {ω : F} (hω0 : ω ≠ 0) (x : ℕ → F)
    (N m n j : ℕ) :
    fieldTerm ω x m j * fieldTerm ω x n j *
      fieldCharacter ω (-(N : ℤ)) j =
      x m * x n * fieldCharacter ω ((m : ℤ) + (n : ℤ) - (N : ℤ)) j := by
  calc
    _ = x m * x n * (fieldCharacter ω (m : ℤ) j *
        fieldCharacter ω (n : ℤ) j * fieldCharacter ω (-(N : ℤ)) j) := by
      unfold fieldTerm
      ring
    _ = _ := by rw [fieldCharacter_pair hω0]

theorem normalized_field_pair {ω : F} {N M K m n : ℕ}
    (hω : IsPrimitiveRoot ω K) (hA0 : max N (2 * M - N) < K)
    (hK0 : (K : F) ≠ 0) (hm : m ≤ M) (hn : n ≤ M) (x : ℕ → F) :
    (K : F)⁻¹ * (∑ j ∈ Finset.range K,
      fieldTerm ω x m j * fieldTerm ω x n j *
        fieldCharacter ω (-(N : ℤ)) j) =
      if m + n = N then x m * x n else 0 := by
  have hK : 0 < K := by
    have hNK := (le_max_left N (2 * M - N)).trans_lt hA0
    omega
  have hω0 : ω ≠ 0 := hω.ne_zero (Nat.ne_of_gt hK)
  simp_rw [fieldTerm_pair hω0]
  rw [← Finset.mul_sum, sum_rectangle_character hω hA0 hm hn]
  by_cases hmn : m + n = N
  · rw [if_pos hmn, if_pos hmn]
    calc
      _ = (x m * x n) * ((K : F)⁻¹ * (K : F)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hK0, mul_one]
  · simp only [if_neg hmn, mul_zero]

theorem fieldPolynomial_square_expansion (ω : F) (x : ℕ → F)
    (N M j : ℕ) :
    fieldPolynomial ω x M j ^ 2 * fieldCharacter ω (-(N : ℤ)) j =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        fieldTerm ω x p.1 j * fieldTerm ω x p.2 j *
          fieldCharacter ω (-(N : ℤ)) j := by
  unfold fieldPolynomial
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  simp_rw [Finset.sum_mul]

theorem fieldProjection_eq_rectangle {ω : F} {N M K : ℕ}
    (hω : IsPrimitiveRoot ω K) (hA0 : max N (2 * M - N) < K)
    (hK0 : (K : F) ≠ 0) (x : ℕ → F) :
    fieldProjection ω x N M K =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        if p.1 + p.2 = N then x p.1 * x p.2 else 0 := by
  unfold fieldProjection
  simp_rw [fieldPolynomial_square_expansion]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_product.mp hp
  have hm : p.1 ≤ M := by have := Finset.mem_range.mp hp'.1; omega
  have hn : p.2 ≤ M := by have := Finset.mem_range.mp hp'.2; omega
  exact normalized_field_pair hω hA0 hK0 hm hn x

theorem rectangle_filter_antidiagonal {N M : ℕ} (hNM : N ≤ M) :
    (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = N) = Finset.antidiagonal N := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_antidiagonal]
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact ⟨⟨by omega, by omega⟩, hp⟩

theorem fieldProjection_eq_antidiagonal {ω : F} {N M K : ℕ}
    (hω : IsPrimitiveRoot ω K) (hNM : N ≤ M)
    (hA0 : max N (2 * M - N) < K) (hK0 : (K : F) ≠ 0) (x : ℕ → F) :
    fieldProjection ω x N M K = ∑ p ∈ Finset.antidiagonal N, x p.1 * x p.2 := by
  rw [fieldProjection_eq_rectangle hω hA0 hK0 x,
    ← Finset.sum_filter, rectangle_filter_antidiagonal hNM]

theorem fieldProjection_eq_sum {ω : F} {N M K : ℕ}
    (hω : IsPrimitiveRoot ω K) (hNM : N ≤ M)
    (hA0 : max N (2 * M - N) < K) (hK0 : (K : F) ≠ 0) (x : ℕ → F) :
    fieldProjection ω x N M K =
      ∑ n ∈ Finset.range (N + 1), x n * x (N - n) := by
  rw [fieldProjection_eq_antidiagonal hω hNM hA0 hK0 x,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_map] <;> rfl

theorem fieldCharacter_nat (ω : F) (n j : ℕ) :
    fieldCharacter ω (n : ℤ) j = ω ^ (n * j) := by
  unfold fieldCharacter
  rw [zpow_natCast, ← pow_mul]

theorem fieldPolynomial_eq_standardDFT (ω : F) (x : ℕ → F) (M j : ℕ) :
    fieldPolynomial ω x M j =
      ∑ n ∈ Finset.range (M + 1), x n * ω ^ (n * j) := by
  unfold fieldPolynomial fieldTerm
  simp_rw [fieldCharacter_nat]

/-- The exact DFT expression; no butterfly or code evaluation is presumed. -/
theorem standardDFT_projection_eq_sum {ω : F} {N M K : ℕ}
    (hω : IsPrimitiveRoot ω K) (hNM : N ≤ M)
    (hA0 : max N (2 * M - N) < K) (hK0 : (K : F) ≠ 0) (x : ℕ → F) :
    (K : F)⁻¹ * (∑ j ∈ Finset.range K,
      (∑ n ∈ Finset.range (M + 1), x n * ω ^ (n * j)) ^ 2 *
        ω ^ (-((N : ℤ) * (j : ℤ)))) =
      ∑ n ∈ Finset.range (N + 1), x n * x (N - n) := by
  have hchar : ∀ j : ℕ,
      fieldCharacter ω (-(N : ℤ)) j = ω ^ (-((N : ℤ) * (j : ℤ))) := by
    intro j
    unfold fieldCharacter
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have h := fieldProjection_eq_sum hω hNM hA0 hK0 x
  unfold fieldProjection at h
  simp_rw [fieldPolynomial_eq_standardDFT, hchar] at h
  exact h

theorem zmod_size_ne_zero {p K : ℕ} (hK : 0 < K) (hKp : K < p) :
    (K : ZMod p) ≠ 0 := by
  intro hz
  have hd : p ∣ K := (ZMod.natCast_zmod_eq_zero_iff_dvd K p).mp hz
  have hpK : p ≤ K := Nat.le_of_dvd hK hd
  exact (not_le_of_gt hKp) hpK

theorem zmod_integer_projection {p N K : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω K) (hNK : N < K) (hKp : K < p) (x : ℕ → ℤ) :
    fieldProjection ω (fun n => (x n : ZMod p)) N N K =
      ((∑ n ∈ Finset.range (N + 1), x n * x (N - n) : ℤ) : ZMod p) := by
  have hK : 0 < K := by omega
  have hA0 : max N (2 * N - N) < K := by omega
  have hK0 : (K : ZMod p) ≠ 0 := zmod_size_ne_zero hK hKp
  have h := fieldProjection_eq_sum hω (le_refl N) hA0 hK0
    (fun n => (x n : ZMod p))
  simpa only [Int.cast_sum, Int.cast_mul] using h

/-- Canonical A32 weights, with the actual IsPrimePow/minFac branch preserved. -/
theorem zmod_canonical_A32_projection {p N K : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω K) (hNK : N < K) (hKp : K < p) :
    fieldProjection ω
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod p)) N N K =
      (GoldbachQuantizedCoefficient22.integerCoefficient N : ZMod p) := by
  simpa only [GoldbachQuantizedCoefficient22.integerCoefficient] using
    zmod_integer_projection hω hNK hKp GoldbachQuantizedCoefficient22.integerLambda

/-- Fixed bank size only; each concrete prime/root certificate remains explicit. -/
theorem fixed_A32_projection {p : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω (2 ^ 27)) (hKp : 2 ^ 27 < p) :
    fieldProjection ω
      (fun n => (GoldbachQuantizedCoefficient22.integerLambda n : ZMod p))
        100000000 100000000 (2 ^ 27) =
      (GoldbachQuantizedCoefficient22.integerCoefficient 100000000 : ZMod p) := by
  exact zmod_canonical_A32_projection hω (by norm_num) hKp

end GoldbachFiniteFieldProjection22

#print axioms GoldbachFiniteFieldProjection22.fieldCharacter
#print axioms GoldbachFiniteFieldProjection22.sum_fieldCharacter
#print axioms GoldbachFiniteFieldProjection22.signed_divides_iff_zero
#print axioms GoldbachFiniteFieldProjection22.sum_fieldCharacter_no_alias
#print axioms GoldbachFiniteFieldProjection22.rectangle_frequency_bounds
#print axioms GoldbachFiniteFieldProjection22.sum_rectangle_character
#print axioms GoldbachFiniteFieldProjection22.fieldCharacter_pair
#print axioms GoldbachFiniteFieldProjection22.fieldTerm
#print axioms GoldbachFiniteFieldProjection22.fieldPolynomial
#print axioms GoldbachFiniteFieldProjection22.fieldProjection
#print axioms GoldbachFiniteFieldProjection22.fieldTerm_pair
#print axioms GoldbachFiniteFieldProjection22.normalized_field_pair
#print axioms GoldbachFiniteFieldProjection22.fieldPolynomial_square_expansion
#print axioms GoldbachFiniteFieldProjection22.fieldProjection_eq_rectangle
#print axioms GoldbachFiniteFieldProjection22.rectangle_filter_antidiagonal
#print axioms GoldbachFiniteFieldProjection22.fieldProjection_eq_antidiagonal
#print axioms GoldbachFiniteFieldProjection22.fieldProjection_eq_sum
#print axioms GoldbachFiniteFieldProjection22.fieldCharacter_nat
#print axioms GoldbachFiniteFieldProjection22.fieldPolynomial_eq_standardDFT
#print axioms GoldbachFiniteFieldProjection22.standardDFT_projection_eq_sum
#print axioms GoldbachFiniteFieldProjection22.zmod_size_ne_zero
#print axioms GoldbachFiniteFieldProjection22.zmod_integer_projection
#print axioms GoldbachFiniteFieldProjection22.zmod_canonical_A32_projection
#print axioms GoldbachFiniteFieldProjection22.fixed_A32_projection
