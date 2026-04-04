/-
  Goldbach/Basic.lean
  Conservative basic definitions for a Lean 4 / Mathlib project.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

namespace Goldbach

/-- `GoldbachAt n` means that `n` is a sum of two prime numbers. -/
def GoldbachAt (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Strong Goldbach conjecture on all even integers `n ≥ 4`. -/
def GoldbachStrong : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → GoldbachAt n

/-- Verified Goldbach range up to `K`. -/
def VerifiedUpTo (K : ℕ) : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ K → Even n → GoldbachAt n

/-- Goldbach holds for all even integers strictly above `N0`. -/
def HoldsAbove (N0 : ℕ) : Prop :=
  ∀ n : ℕ, N0 < n → Even n → GoldbachAt n

/-- A tiny sanity check: `28 = 5 + 23`. -/
example : GoldbachAt 28 := by
  refine ⟨5, 23, ?_, ?_, ?_⟩
  · decide
  · decide
  · norm_num

end Goldbach
