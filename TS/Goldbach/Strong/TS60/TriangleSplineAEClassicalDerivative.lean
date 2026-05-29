import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import TS.Goldbach.Strong.TS59.TriangleSplineOffCornerClassicalDerivative
import TS.Goldbach.Strong.TS58.TriangleSplineBoundaryExteriorControl

namespace TS60
namespace MellinJackson

open MeasureTheory

/-!
# TS60 - Triangle Spline A.E. Classical Derivative

This sprint lifts the off-corner pointwise derivative theorem from TS59 to an
almost-everywhere statement using the nullity of the corner set proved in TS58.

It does not prove the distributional derivative identity, Sobolev-slot
agreement, Plancherel, or Fourier-tail estimates.
-/

/--
Almost everywhere, a point is not one of the three corners `-1`, `0`, and `1`.
-/
theorem ae_not_mem_triangleSplineCornerSet :
    Filter.Eventually
      (fun x : Real => Not (TS58.MellinJackson.triangleSplineCornerSet x))
      (ae (volume : Measure Real)) := by
  exact
    (measure_zero_iff_ae_nmem.mp
      TS58.MellinJackson.volume_triangleSplineCornerSet)

/--
Almost everywhere, the classical derivative of the triangle spline exists and
agrees with the explicit representative `triangleSplineDeriv`.
-/
theorem triangleSpline_hasDerivAt_triangleSplineDeriv_ae :
    Filter.Eventually
      (fun x : Real =>
        HasDerivAt
          TS42.MellinJackson.triangleSpline
          (TS42.MellinJackson.triangleSplineDeriv x)
          x)
      (ae (volume : Measure Real)) := by
  filter_upwards [ae_not_mem_triangleSplineCornerSet] with x hx
  exact
    TS59.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner
      hx

/--
Consequently, Mathlib's global `deriv` operator agrees a.e. with the explicit
representative `triangleSplineDeriv`.
-/
theorem deriv_triangleSpline_eq_triangleSplineDeriv_ae :
    Filter.EventuallyEq
      (ae (volume : Measure Real))
      (fun x : Real => deriv TS42.MellinJackson.triangleSpline x)
      TS42.MellinJackson.triangleSplineDeriv := by
  filter_upwards [triangleSpline_hasDerivAt_triangleSplineDeriv_ae] with x hx
  exact hx.deriv

/-!
## A.E. derivative package
-/

/-- Package for the a.e. classical derivative bridge. -/
structure TriangleSplineAEClassicalDerivative where
  ae_hasDerivAt :
    Filter.Eventually
      (fun x : Real =>
        HasDerivAt
          TS42.MellinJackson.triangleSpline
          (TS42.MellinJackson.triangleSplineDeriv x)
          x)
      (ae (volume : Measure Real))

  ae_deriv_eq :
    Filter.EventuallyEq
      (ae (volume : Measure Real))
      (fun x : Real => deriv TS42.MellinJackson.triangleSpline x)
      TS42.MellinJackson.triangleSplineDeriv

/-- Concrete a.e. derivative package. -/
def triangleSplineAEClassicalDerivative :
    TriangleSplineAEClassicalDerivative where
  ae_hasDerivAt := triangleSpline_hasDerivAt_triangleSplineDeriv_ae
  ae_deriv_eq := deriv_triangleSpline_eq_triangleSplineDeriv_ae

/-- Target proposition for TS60. -/
def TriangleSplineAEClassicalDerivativeTarget : Prop :=
  Nonempty TriangleSplineAEClassicalDerivative

/-- The concrete a.e. derivative package discharges the TS60 target. -/
theorem triangleSplineAEClassicalDerivativeTarget :
    TriangleSplineAEClassicalDerivativeTarget :=
  Nonempty.intro triangleSplineAEClassicalDerivative

end MellinJackson
end TS60
