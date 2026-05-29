import Mathlib.Tactic
import TS.Goldbach.Strong.TS43.TriangleSplinePointwise

namespace TS44
namespace MellinJackson

open MeasureTheory

/-!
# TS44 - Triangle Spline Measurability and Support

This sprint proves the support and measurability inputs for the
triangle-spline weak-derivative representative.

It does not prove the Lebesgue integral, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.
-/

/-- Left exterior vanishing: for `x <= -1`, the derivative representative is zero. -/
theorem triangleSplineDeriv_eq_zero_of_le_neg_one
    {x : Real}
    (hx : x <= -1) :
    TS42.MellinJackson.triangleSplineDeriv x = 0 := by
  apply TS43.MellinJackson.triangleSplineDeriv_eq_zero_of_not_left_not_right
  case hleft =>
    intro h
    linarith
  case hright =>
    intro h
    linarith

/-- Right exterior vanishing: for `1 <= x`, the derivative representative is zero. -/
theorem triangleSplineDeriv_eq_zero_of_one_le
    {x : Real}
    (hx : 1 <= x) :
    TS42.MellinJackson.triangleSplineDeriv x = 0 := by
  apply TS43.MellinJackson.triangleSplineDeriv_eq_zero_of_not_left_not_right
  case hleft =>
    intro h
    linarith
  case hright =>
    intro h
    linarith

/--
Pointwise support containment in the closed interval `[-1, 1]`.

This is the support fact needed before turning to Lebesgue integration.
-/
theorem triangleSplineDeriv_zero_outside_Icc
    {x : Real}
    (hx : Not (Set.Icc (-1 : Real) 1 x)) :
    TS42.MellinJackson.triangleSplineDeriv x = 0 := by
  by_cases hleft : x <= -1
  case pos =>
    exact triangleSplineDeriv_eq_zero_of_le_neg_one hleft
  case neg =>
    by_cases hright : 1 <= x
    case pos =>
      exact triangleSplineDeriv_eq_zero_of_one_le hright
    case neg =>
      have hx_mem : Set.Icc (-1 : Real) 1 x := by
        constructor
        case left =>
          exact le_of_lt (lt_of_not_ge hleft)
        case right =>
          exact le_of_lt (lt_of_not_ge hright)
      exact False.elim (hx hx_mem)

/-- The weak-derivative representative is measurable. -/
theorem triangleSplineDeriv_measurable :
    Measurable TS42.MellinJackson.triangleSplineDeriv := by
  classical
  unfold TS42.MellinJackson.triangleSplineDeriv
  exact Measurable.ite (measurableSet_Ioi.inter measurableSet_Iio)
    measurable_const
    (Measurable.ite (measurableSet_Ioi.inter measurableSet_Iio)
      measurable_const measurable_const)

/--
Concrete support/measurability package for the triangle-spline derivative.

This is the exact input TS45 will use for the future `L2` norm estimate.
-/
structure TriangleSplineDerivativeSupportInputs where
  /-- Measurability of the weak-derivative representative. -/
  measurable_deriv :
    Measurable TS42.MellinJackson.triangleSplineDeriv

  /-- The derivative representative vanishes outside `[-1, 1]`. -/
  zero_outside :
    forall {x : Real},
      Not (Set.Icc (-1 : Real) 1 x) ->
        TS42.MellinJackson.triangleSplineDeriv x = 0

/-- The concrete TS44 support and measurability inputs. -/
def triangleSplineDerivativeSupportInputs :
    TriangleSplineDerivativeSupportInputs where
  measurable_deriv := triangleSplineDeriv_measurable
  zero_outside := triangleSplineDeriv_zero_outside_Icc

/-- Roadmap target for the measurability/support side of the spline derivative. -/
def TriangleSplineDerivativeSupportTarget : Prop :=
  Nonempty TriangleSplineDerivativeSupportInputs

/-- The concrete support inputs discharge the TS44 target. -/
theorem triangleSplineDerivativeSupportTarget :
    TriangleSplineDerivativeSupportTarget :=
  Nonempty.intro triangleSplineDerivativeSupportInputs

end MellinJackson
end TS44
