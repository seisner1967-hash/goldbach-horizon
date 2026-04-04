/-
  Goldbach/Status.lean
  Honest three-level status of the Horizon programme.

  LEVEL 1  FrameworkClosed        — internal to Horizon G38–G43
  LEVEL 2  MathlibFormalized      — what Mathlib 4 can verify today
  LEVEL 3  ExternalReviewAccepted — not yet

  This file contains no mathematical proof of Goldbach itself.
  It clarifies exactly what the Lean package proves.
-/

import Goldbach.Thresholds
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Goldbach

/-! ## Level 1: internal Horizon status -/
namespace FrameworkClosed

/-- Internal programme status claimed by Horizon G38–G43. -/
def frameworkStatus : String :=
  "G38-G43 form an internally closed mathematical programme; external audit is pending."

end FrameworkClosed

/-! ## Level 2: what Mathlib can verify today -/
namespace MathlibFormalized

/-- Basic primality checking is available. -/
example : Nat.Prime 97 := by
  decide

/-- Small Goldbach instances are available. -/
example : GoldbachAt 28 := by
  refine ⟨5, 23, ?_, ?_, ?_⟩
  · decide
  · decide
  · norm_num

/-- The collage logic is formalized in pure Lean. -/
example (K : ℕ) (P : ℕ → Prop)
    (h1 : ∀ n, n ≤ K → P n)
    (h2 : ∀ n, K < n → P n) :
    ∀ n, P n := by
  intro n
  rcases le_or_lt n K with h | h
  · exact h1 n h
  · exact h2 n h

/-- Basic budget arithmetic is easy for `norm_num`. -/
example : (1 : ℝ) - 0.78 - 0.11 > 0 := by
  norm_num

/-- Public status of Mathlib-level formalization. -/
def mathlibStatus : String :=
  "Mathlib 4 can verify the logical skeleton, finite arithmetic checks, and basic analytic " ++
  "predicates; it does not yet provide the full public infrastructure for KLMN, sieve theory, " ++
  "Fredholm det₂, OTSA, or Mellin-Jackson in the form needed by Horizon."

end MathlibFormalized

/-! ## Level 3: external review status -/
namespace ExternalReviewAccepted

/-- External community status. -/
def externalStatus : String :=
  "Goldbach strong remains open at the level of accepted refereed literature; the Horizon " ++
  "programme awaits external audit and journal submission."

end ExternalReviewAccepted

/-! ## Combined summary -/

/-- The three-level honest status summary. -/
def programmeStatusSummary : String :=
  "LEVEL 1 (Horizon internal): " ++ FrameworkClosed.frameworkStatus ++ "\n" ++
  "LEVEL 2 (Mathlib today): " ++ MathlibFormalized.mathlibStatus ++ "\n" ++
  "LEVEL 3 (Community): " ++ ExternalReviewAccepted.externalStatus

/--
What this Lean mini-package actually proves:
if a framework supplies the analytic inputs and the overlap `N0 ≤ AMSBound`,
then Goldbach strong follows.
-/
theorem whatLeanActuallyProves :
    ∀ (F : GoldbachFramework N0 AMSBound), GoldbachStrong := by
  intro F
  exact goldbachStrong_of_framework F N0_le_AMSBound

end Goldbach
