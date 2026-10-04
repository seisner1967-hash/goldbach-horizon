import GoldbachMoebiusShortLong
import Mathlib.Tactic

/-!
The finite quartic truncated Mobius identity, with its exact remainder.
All products and powers of arithmetic functions are Dirichlet convolution.
The weighted insertion retains an arbitrary coefficient on the full argument n.
This file proves no analytic estimate for the terminal Goldbach residue.
-/

namespace GoldbachResearch.QuarticMobius

open scoped BigOperators
open ArithmeticFunction Finset
open GoldbachResearch.MoebiusShortLong

def shortCubic (alpha : ℕ) : ArithmeticFunction ℤ :=
  shortMoebius alpha ^ 3 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 2

def shortQuartic (alpha : ℕ) : ArithmeticFunction ℤ :=
  shortMoebius alpha ^ 4 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 3

def longQuartic (alpha : ℕ) : ArithmeticFunction ℤ :=
  longMoebius alpha ^ 4 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 3

theorem algebraic_quartic_identity (M : ArithmeticFunction ℤ) :
    ArithmeticFunction.moebius =
      4 * M - 6 * (M ^ 2 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) +
      4 * (M ^ 3 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 2) -
      M ^ 4 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 3 +
      (ArithmeticFunction.moebius - M) ^ 4 *
        (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 3 := by
  have hinv := ArithmeticFunction.moebius_mul_coe_zeta
  linear_combination
    ((4 * M - ArithmeticFunction.moebius) *
        (1 + ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) +
          ArithmeticFunction.moebius ^ 2 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 2) -
      6 * M ^ 2 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
        (1 + ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) +
      4 * M ^ 3 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 2) * hinv

theorem moebius_quartic (alpha : ℕ) :
    ArithmeticFunction.moebius =
      4 * shortMoebius alpha - 6 * shortDouble alpha +
        4 * shortCubic alpha - shortQuartic alpha + longQuartic alpha := by
  simpa [shortDouble, shortCubic, shortQuartic, longQuartic, longMoebius, pow_two]
    using algebraic_quartic_identity (shortMoebius alpha)

theorem long_four_support {alpha n : ℕ} (hn : n < (alpha + 1) ^ 4) :
    (longMoebius alpha ^ 4) n = 0 := by
  have hsquare : ∀ m < (alpha + 1) ^ 2, (longMoebius alpha ^ 2) m = 0 := by
    intro m hm
    rw [pow_two]
    apply convolution_vanishes_below (A := alpha + 1) (B := alpha + 1)
    · intro t ht
      exact long_apply_of_le (by omega)
    · intro t ht
      exact long_apply_of_le (by omega)
    · simpa [pow_two] using hm
  have heq : (4 : ℕ) = 2 + 2 := by norm_num
  rw [heq, pow_add]
  apply convolution_vanishes_below hsquare hsquare
  simpa [← pow_add] using hn

theorem long_quartic_support {alpha n : ℕ} (hn : n < (alpha + 1) ^ 4) :
    longQuartic alpha n = 0 := by
  unfold longQuartic
  exact convolution_with_arbitrary_preserves_vanishing
    (fun m hm => long_four_support hm) hn

theorem nat_coefficient_apply (k n : ℕ) (f : ArithmeticFunction ℤ) :
    ((k : ArithmeticFunction ℤ) * f) n = (k : ℤ) * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.cast_succ, add_mul, one_mul, ArithmeticFunction.add_apply, ih]

theorem moebius_quartic_apply (alpha n : ℕ) :
    ArithmeticFunction.moebius n =
      4 * shortMoebius alpha n - 6 * shortDouble alpha n +
        4 * shortCubic alpha n - shortQuartic alpha n + longQuartic alpha n := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (moebius_quartic alpha)
  change ArithmeticFunction.moebius n =
    (4 * shortMoebius alpha) n - (6 * shortDouble alpha) n +
      (4 * shortCubic alpha) n - shortQuartic alpha n + longQuartic alpha n at h
  have h4 (f : ArithmeticFunction ℤ) : (4 * f) n = 4 * f n := by
    simpa using nat_coefficient_apply 4 n f
  have h6 (f : ArithmeticFunction ℤ) : (6 * f) n = 6 * f n := by
    simpa using nat_coefficient_apply 6 n f
  simpa only [h4, h6] using h

theorem finite_quartic_identity {alpha n : ℕ} (hn : n < (alpha + 1) ^ 4) :
    ArithmeticFunction.moebius n =
      4 * shortMoebius alpha n - 6 * shortDouble alpha n +
        4 * shortCubic alpha n - shortQuartic alpha n := by
  have h := moebius_quartic_apply alpha n
  rw [long_quartic_support hn] at h
  simpa using h

theorem finite_quartic_identity_of_N {alpha N n : ℕ}
    (hn : n < N) (hN : N ≤ alpha ^ 4) :
    ArithmeticFunction.moebius n =
      4 * shortMoebius alpha n - 6 * shortDouble alpha n +
        4 * shortCubic alpha n - shortQuartic alpha n := by
  apply finite_quartic_identity
  have hpow : alpha ^ 4 ≤ (alpha + 1) ^ 4 :=
    Nat.pow_le_pow_left (by omega : alpha ≤ alpha + 1) 4
  exact lt_of_lt_of_le hn (le_trans hN hpow)

theorem long_region_quartic_identity {alpha N r : ℕ}
    (hr : alpha < r) (hrN : r < N) (hN : N ≤ alpha ^ 4) :
    ArithmeticFunction.moebius r =
      -(6 * shortDouble alpha r) + 4 * shortCubic alpha r - shortQuartic alpha r := by
  have h := finite_quartic_identity_of_N hrN hN
  rw [short_apply_of_gt hr] at h
  simpa using h

theorem weighted_boundary_identity (s : Finset ℕ) (c : ℕ → ℤ)
    {alpha N : ℕ} (hN : N ≤ alpha ^ 4)
    (hs : ∀ r ∈ s, alpha < r ∧ r < N) :
    ∑ r ∈ s, c r * ArithmeticFunction.moebius r =
      -(6 * ∑ r ∈ s, c r * shortDouble alpha r) +
        4 * ∑ r ∈ s, c r * shortCubic alpha r -
        ∑ r ∈ s, c r * shortQuartic alpha r := by
  calc
    _ = ∑ r ∈ s, c r *
        (-(6 * shortDouble alpha r) + 4 * shortCubic alpha r - shortQuartic alpha r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [long_region_quartic_identity (hs r hr).1 (hs r hr).2 hN]
    _ = _ := by
      simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp_rw [show ∀ r, c r * (6 * shortDouble alpha r) =
          6 * (c r * shortDouble alpha r) by intro r; ring,
        show ∀ r, c r * (4 * shortCubic alpha r) =
          4 * (c r * shortCubic alpha r) by intro r; ring]
      rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem weighted_boundary_identity_real {ι : Type*} (s : Finset ι)
    (r : ι → ℕ) (c : ι → ℝ) {alpha N : ℕ} (hN : N ≤ alpha ^ 4)
    (hs : ∀ t ∈ s, alpha < r t ∧ r t < N) :
    ∑ t ∈ s, c t * (ArithmeticFunction.moebius (r t) : ℝ) =
      -(6 * ∑ t ∈ s, c t * (shortDouble alpha (r t) : ℝ)) +
        4 * ∑ t ∈ s, c t * (shortCubic alpha (r t) : ℝ) -
        ∑ t ∈ s, c t * (shortQuartic alpha (r t) : ℝ) := by
  have hpoint : ∀ t ∈ s, (ArithmeticFunction.moebius (r t) : ℝ) =
      -(6 * (shortDouble alpha (r t) : ℝ)) +
        4 * (shortCubic alpha (r t) : ℝ) - (shortQuartic alpha (r t) : ℝ) := by
    intro t ht
    exact_mod_cast long_region_quartic_identity (hs t ht).1 (hs t ht).2 hN
  calc
    _ = ∑ t ∈ s, c t *
        (-(6 * (shortDouble alpha (r t) : ℝ)) +
          4 * (shortCubic alpha (r t) : ℝ) - (shortQuartic alpha (r t) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hpoint t ht]
    _ = _ := by
      simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp_rw [show ∀ t, c t * (6 * (shortDouble alpha (r t) : ℝ)) =
          6 * (c t * (shortDouble alpha (r t) : ℝ)) by intro t; ring,
        show ∀ t, c t * (4 * (shortCubic alpha (r t) : ℝ)) =
          4 * (c t * (shortCubic alpha (r t) : ℝ)) by intro t; ring]
      rw [← Finset.mul_sum, ← Finset.mul_sum]

#print axioms algebraic_quartic_identity
#print axioms moebius_quartic
#print axioms long_four_support
#print axioms long_quartic_support
#print axioms nat_coefficient_apply
#print axioms moebius_quartic_apply
#print axioms finite_quartic_identity
#print axioms finite_quartic_identity_of_N
#print axioms long_region_quartic_identity
#print axioms weighted_boundary_identity
#print axioms weighted_boundary_identity_real

end GoldbachResearch.QuarticMobius
