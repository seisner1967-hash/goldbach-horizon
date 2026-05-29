import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
import TS.Goldbach.Strong.TS43.TriangleSplinePointwise

namespace TS57
namespace MellinJackson

open Set

/-!
# TS57 - Triangle Spline Classical Branch Derivatives

This sprint proves the classical derivative facts for the triangle spline on
the two open affine branches.

It does not prove global a.e. differentiability, boundary/raccord control, the
distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates.
-/

/-- Classical derivative on the left open branch `(-1, 0)`. -/
theorem triangleSpline_hasDerivAt_left
    {x : Real}
    (hx1 : -1 < x)
    (hx0 : x < 0) :
    HasDerivAt TS42.MellinJackson.triangleSpline 1 x := by
  have h_eq :
      Filter.EventuallyEq (nhds x)
        TS42.MellinJackson.triangleSpline
        (fun y : Real => 1 + y) := by
    filter_upwards [Ioo_mem_nhds hx1 hx0] with y hy
    exact TS56.MellinJackson.triangleSpline_eq_one_add_of_left
      (le_of_lt hy.1) (le_of_lt hy.2)
  have h_der : HasDerivAt (fun y : Real => 1 + y) 1 x := by
    simpa using
      ((hasDerivAt_const (x := x) (c := (1 : Real))).add
        (hasDerivAt_id (x := x)))
  exact h_der.congr_of_eventuallyEq h_eq

/-- Classical derivative on the right open branch `(0, 1)`. -/
theorem triangleSpline_hasDerivAt_right
    {x : Real}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    HasDerivAt TS42.MellinJackson.triangleSpline (-1) x := by
  have h_eq :
      Filter.EventuallyEq (nhds x)
        TS42.MellinJackson.triangleSpline
        (fun y : Real => 1 - y) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
      (le_of_lt hy.1) (le_of_lt hy.2)
  have h_der : HasDerivAt (fun y : Real => 1 - y) (-1) x := by
    simpa using
      ((hasDerivAt_const (x := x) (c := (1 : Real))).sub
        (hasDerivAt_id (x := x)))
  exact h_der.congr_of_eventuallyEq h_eq

/--
On the left branch, the classical derivative agrees with the explicit
weak-derivative representative.
-/
theorem triangleSpline_hasDerivAt_triangleSplineDeriv_left
    {x : Real}
    (hx1 : -1 < x)
    (hx0 : x < 0) :
    HasDerivAt
      TS42.MellinJackson.triangleSpline
      (TS42.MellinJackson.triangleSplineDeriv x)
      x := by
  have hval :
      TS42.MellinJackson.triangleSplineDeriv x = 1 :=
    TS43.MellinJackson.triangleSplineDeriv_eq_one_of_left hx1 hx0
  simpa [hval] using triangleSpline_hasDerivAt_left hx1 hx0

/--
On the right branch, the classical derivative agrees with the explicit
weak-derivative representative.
-/
theorem triangleSpline_hasDerivAt_triangleSplineDeriv_right
    {x : Real}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    HasDerivAt
      TS42.MellinJackson.triangleSpline
      (TS42.MellinJackson.triangleSplineDeriv x)
      x := by
  have hval :
      TS42.MellinJackson.triangleSplineDeriv x = -1 :=
    TS43.MellinJackson.triangleSplineDeriv_eq_neg_one_of_right hx0 hx1
  simpa [hval] using triangleSpline_hasDerivAt_right hx0 hx1

/-!
## Branch-derivative package
-/

/-- Package of classical branch derivative facts. -/
structure TriangleSplineClassicalBranchDerivatives where
  left_derivative :
    forall {x : Real}, -1 < x -> x < 0 ->
      HasDerivAt TS42.MellinJackson.triangleSpline 1 x

  right_derivative :
    forall {x : Real}, 0 < x -> x < 1 ->
      HasDerivAt TS42.MellinJackson.triangleSpline (-1) x

  left_matches_representative :
    forall {x : Real}, -1 < x -> x < 0 ->
      HasDerivAt
        TS42.MellinJackson.triangleSpline
        (TS42.MellinJackson.triangleSplineDeriv x)
        x

  right_matches_representative :
    forall {x : Real}, 0 < x -> x < 1 ->
      HasDerivAt
        TS42.MellinJackson.triangleSpline
        (TS42.MellinJackson.triangleSplineDeriv x)
        x

/-- Concrete package of branch derivative facts. -/
def triangleSplineClassicalBranchDerivatives :
    TriangleSplineClassicalBranchDerivatives where
  left_derivative := by
    intro x hx1 hx0
    exact triangleSpline_hasDerivAt_left hx1 hx0
  right_derivative := by
    intro x hx0 hx1
    exact triangleSpline_hasDerivAt_right hx0 hx1
  left_matches_representative := by
    intro x hx1 hx0
    exact triangleSpline_hasDerivAt_triangleSplineDeriv_left hx1 hx0
  right_matches_representative := by
    intro x hx0 hx1
    exact triangleSpline_hasDerivAt_triangleSplineDeriv_right hx0 hx1

/-- Target proposition for the classical-branch derivative step. -/
def TriangleSplineClassicalBranchDerivativesTarget : Prop :=
  Nonempty TriangleSplineClassicalBranchDerivatives

/-- The concrete package discharges the TS57 target. -/
theorem triangleSplineClassicalBranchDerivativesTarget :
    TriangleSplineClassicalBranchDerivativesTarget :=
  Nonempty.intro triangleSplineClassicalBranchDerivatives

end MellinJackson
end TS57
