import Mathlib.Tactic
import TS.Goldbach.Strong.TS58.TriangleSplineBoundaryExteriorControl
import TS.Goldbach.Strong.TS57.TriangleSplineClassicalBranchDerivatives

namespace TS59
namespace MellinJackson

/-!
# TS59 - Triangle Spline Off-Corner Classical Derivative

This sprint proves that away from the three corner points `-1`, `0`, and `1`,
the classical derivative of the triangle spline exists and agrees with the
explicit representative `triangleSplineDeriv`.

It does not yet prove the almost-everywhere derivative statement, the
distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates.
-/

/-- Not being in the corner set implies `x != -1`. -/
theorem ne_neg_one_of_not_corner
    {x : Real}
    (hx : Not (TS58.MellinJackson.triangleSplineCornerSet x)) :
    Not (x = (-1 : Real)) := by
  intro h
  apply hx
  unfold TS58.MellinJackson.triangleSplineCornerSet
  rw [h]
  exact Or.inl (Or.inl rfl)

/-- Not being in the corner set implies `x != 0`. -/
theorem ne_zero_of_not_corner
    {x : Real}
    (hx : Not (TS58.MellinJackson.triangleSplineCornerSet x)) :
    Not (x = (0 : Real)) := by
  intro h
  apply hx
  unfold TS58.MellinJackson.triangleSplineCornerSet
  rw [h]
  exact Or.inl (Or.inr rfl)

/-- Not being in the corner set implies `x != 1`. -/
theorem ne_one_of_not_corner
    {x : Real}
    (hx : Not (TS58.MellinJackson.triangleSplineCornerSet x)) :
    Not (x = (1 : Real)) := by
  intro h
  apply hx
  unfold TS58.MellinJackson.triangleSplineCornerSet
  rw [h]
  exact Or.inr rfl

/--
Away from the three corner points `-1`, `0`, and `1`, the classical derivative
of the triangle spline exists and agrees with `triangleSplineDeriv`.
-/
theorem triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner
    {x : Real}
    (hx : Not (TS58.MellinJackson.triangleSplineCornerSet x)) :
    HasDerivAt
      TS42.MellinJackson.triangleSpline
      (TS42.MellinJackson.triangleSplineDeriv x)
      x := by
  have hx_ne_neg_one : Not (x = (-1 : Real)) :=
    ne_neg_one_of_not_corner hx
  have hx_ne_zero : Not (x = (0 : Real)) :=
    ne_zero_of_not_corner hx
  have hx_ne_one : Not (x = (1 : Real)) :=
    ne_one_of_not_corner hx

  by_cases hleftExterior : x < (-1 : Real)
  case pos =>
    exact
      TS58.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior
        hleftExterior
  case neg =>
    have hx_ge_neg_one : (-1 : Real) <= x := le_of_not_gt hleftExterior
    have hx_gt_neg_one : (-1 : Real) < x := by
      apply lt_of_le_of_ne hx_ge_neg_one
      intro h
      exact hx_ne_neg_one h.symm

    by_cases hleftBranch : x < 0
    case pos =>
      exact
        TS57.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_left
          hx_gt_neg_one hleftBranch
    case neg =>
      have hx_ge_zero : (0 : Real) <= x := le_of_not_gt hleftBranch
      have hx_gt_zero : (0 : Real) < x := by
        apply lt_of_le_of_ne hx_ge_zero
        intro h
        exact hx_ne_zero h.symm

      by_cases hrightBranch : x < 1
      case pos =>
        exact
          TS57.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_right
            hx_gt_zero hrightBranch
      case neg =>
        have hx_ge_one : (1 : Real) <= x := le_of_not_gt hrightBranch
        have hx_gt_one : (1 : Real) < x := by
          apply lt_of_le_of_ne hx_ge_one
          intro h
          exact hx_ne_one h.symm
        exact
          TS58.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior
            hx_gt_one

/-!
## Off-corner derivative package
-/

/-- Package of the off-corner classical derivative fact. -/
structure TriangleSplineOffCornerClassicalDerivative where
  off_corner_derivative :
    forall {x : Real},
      Not (TS58.MellinJackson.triangleSplineCornerSet x) ->
      HasDerivAt
        TS42.MellinJackson.triangleSpline
        (TS42.MellinJackson.triangleSplineDeriv x)
        x

/-- Concrete off-corner derivative package. -/
def triangleSplineOffCornerClassicalDerivative :
    TriangleSplineOffCornerClassicalDerivative where
  off_corner_derivative := by
    intro x hx
    exact triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner hx

/-- Target proposition for TS59. -/
def TriangleSplineOffCornerClassicalDerivativeTarget : Prop :=
  Nonempty TriangleSplineOffCornerClassicalDerivative

/-- The concrete off-corner package discharges the TS59 target. -/
theorem triangleSplineOffCornerClassicalDerivativeTarget :
    TriangleSplineOffCornerClassicalDerivativeTarget :=
  Nonempty.intro triangleSplineOffCornerClassicalDerivative

end MellinJackson
end TS59
