import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# TS282 - ASCII bridge for the regularized completed zeta API

The locked Mathlib declarations use the Unicode subscript-zero character.
This file contains the only unavoidable uses of that character and gives the
API stable ASCII names for the rest of TS282.
-/

noncomputable section

namespace TS282
namespace Goldbach

/-- ASCII alias for Mathlib's entire regularized completed zeta function. -/
noncomputable def completedRiemannZetaZero (s : Complex) : Complex :=
  completedRiemannZeta₀ s

theorem differentiable_completedRiemannZetaZero :
    Differentiable Complex completedRiemannZetaZero := by
  exact differentiable_completedZeta₀

theorem completedRiemannZetaZero_one_sub (s : Complex) :
    completedRiemannZetaZero (1 - s) = completedRiemannZetaZero s := by
  exact completedRiemannZeta₀_one_sub s

theorem completedRiemannZeta_eq_zero_regularization (s : Complex) :
    completedRiemannZeta s =
      completedRiemannZetaZero s - 1 / s - 1 / (1 - s) := by
  exact completedRiemannZeta_eq s

end Goldbach
end TS282
