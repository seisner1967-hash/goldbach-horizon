import Mathlib.Tactic

/-!
Exact two-parameter affine obstruction. The universal identity is required
over the entire field, not just on an integer box. This module proves cross-
branch determinant vanishing, not the complete higher-dimensional rank-one
lemma. The mixed-product example records the level displaced by linearization.
No estimate of the Goldbach residue or of a Mobius correlation is assumed.
-/

namespace GoldbachResearch.AffineHHObstruction

variable {K : Type*} [Field K]

def affine (a b c X Y : K) : K := a * X + b * Y + c

theorem common_zero_of_nonzero_determinant {a b c d e f : K}
    (hdet : a * e - b * d ≠ 0) :
    affine a b c ((b * f - c * e) / (a * e - b * d))
        ((c * d - a * f) / (a * e - b * d)) = 0 ∧
      affine d e f ((b * f - c * e) / (a * e - b * d))
        ((c * d - a * f) / (a * e - b * d)) = 0 := by
  constructor
  all_goals unfold affine
  all_goals field_simp [hdet]
  all_goals ring

theorem cross_branch_determinant_zero {a b c d e f N : K}
    (R S : K → K → K) (hN : N ≠ 0)
    (hidentity : ∀ X Y : K,
      affine a b c X Y * R X Y + affine d e f X Y * S X Y = N) :
    a * e - b * d = 0 := by
  by_contra hdet
  let X := (b * f - c * e) / (a * e - b * d)
  let Y := (c * d - a * f) / (a * e - b * d)
  have hz := common_zero_of_nonzero_determinant (c := c) (f := f) hdet
  have hh := hidentity X Y
  change affine a b c _ _ * R _ _ + affine d e f _ _ * S _ _ = N at hh
  rw [hz.1, hz.2, zero_mul, zero_mul, zero_add] at hh
  exact hN hh.symm

theorem rational_affine_obstruction (a b c d e f N : ℚ)
    (R S : ℚ → ℚ → ℚ) (hN : N ≠ 0)
    (hidentity : ∀ X Y : ℚ,
      (a * X + b * Y + c) * R X Y + (d * X + e * Y + f) * S X Y = N) :
    a * e - b * d = 0 :=
  cross_branch_determinant_zero R S hN hidentity

theorem real_affine_obstruction (a b c d e f N : ℝ)
    (R S : ℝ → ℝ → ℝ) (hN : N ≠ 0)
    (hidentity : ∀ X Y : ℝ,
      (a * X + b * Y + c) * R X Y + (d * X + e * Y + f) * S X Y = N) :
    a * e - b * d = 0 :=
  cross_branch_determinant_zero R S hN hidentity

theorem independent_cross_forms_cannot_have_constant_nonzero_sum
    {a b c d e f N : K} (hdet : a * e - b * d ≠ 0) (hN : N ≠ 0) :
    ¬ ∃ R S : K → K → K, ∀ X Y : K,
      affine a b c X Y * R X Y + affine d e f X Y * S X Y = N := by
  rintro ⟨R, S, hid⟩
  exact hdet (cross_branch_determinant_zero R S hN hid)

theorem zero_factor_allows_two_same_branch_directions :
    ∃ a b c d e f : ℚ,
      a * e - b * d ≠ 0 ∧
      (∀ X Y : ℚ, affine a b c X Y * affine d e f X Y * 0 + 1 = 1) ∧
      ¬ (∃ X Y : ℚ, affine a b c X Y * affine d e f X Y * 0 ≠ 0) := by
  refine ⟨1, 0, 0, 0, 1, 0, ?_, ?_, ?_⟩
  · norm_num
  · intro X Y
    simp
  · simp

def hhLevel (b u v k s t N : K) : K := b * u * v + k * s * t - N

theorem exact_mixed_product_difference (b u v k s t N h j : K) :
    hhLevel b (u + h) (v + j) k s t N -
      hhLevel b (u + h) v k s t N - hhLevel b u (v + j) k s t N +
      hhLevel b u v k s t N = b * h * j := by
  unfold hhLevel
  ring

theorem concrete_positive_tuple :
    hhLevel (13 : ℚ) 3 7 1 7951 12577 100000000 = 0 ∧
    (0 : ℚ) < 13 * 3 * 7 ∧ (0 : ℚ) < 1 * 7951 * 12577 := by
  norm_num [hhLevel]

theorem concrete_mixed_level_displacement :
    hhLevel (13 : ℚ) 11 17 1 7951 12577 100000000 -
      hhLevel (13 : ℚ) 11 7 1 7951 12577 100000000 -
        hhLevel (13 : ℚ) 3 17 1 7951 12577 100000000 +
          hhLevel (13 : ℚ) 3 7 1 7951 12577 100000000 = 1040 := by
  norm_num [hhLevel]

#print axioms common_zero_of_nonzero_determinant
#print axioms cross_branch_determinant_zero
#print axioms rational_affine_obstruction
#print axioms real_affine_obstruction
#print axioms independent_cross_forms_cannot_have_constant_nonzero_sum
#print axioms zero_factor_allows_two_same_branch_directions
#print axioms exact_mixed_product_difference
#print axioms concrete_positive_tuple
#print axioms concrete_mixed_level_displacement

end GoldbachResearch.AffineHHObstruction
