import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TS17
namespace MellinJackson

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- The exponential map sends the real line onto the positive half-line. -/
theorem exp_image_univ : Real.exp '' (univ : Set Real) = Ioi 0 := by
  rw [Set.image_univ, Real.range_exp]

/-- The exponential map is injective on the real line. -/
theorem exp_injOn_univ : (univ : Set Real).InjOn Real.exp :=
  Real.exp_injective.injOn

/-- Derivative data for the exponential map on the real line. -/
theorem exp_hasDerivWithinAt_univ :
    ∀ u ∈ (univ : Set Real),
      HasDerivWithinAt Real.exp (Real.exp u) univ u := by
  intro u hu
  exact (Real.hasDerivAt_exp u).hasDerivWithinAt

/--
Bochner change of variables for `x = exp u`.

This is the measure-theoretic core behind the Mellin/Fourier logarithmic
pullback: integration over `(0, infinity)` can be pulled back to integration
over the full real line with Jacobian factor `exp u`.
-/
theorem integral_Ioi_eq_integral_exp_smul
    (f : Real -> E) :
    (∫ x in Ioi (0 : Real), f x) =
      ∫ u : Real, (Real.exp u) • f (Real.exp u) := by
  rw [← exp_image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ exp_hasDerivWithinAt_univ exp_injOn_univ]
  simp [abs_of_pos (Real.exp_pos _)]

end MellinJackson
end TS17
