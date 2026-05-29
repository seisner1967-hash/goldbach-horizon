import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TS.Goldbach.Strong.TS57.TriangleSplineClassicalBranchDerivatives
import TS.Goldbach.Strong.TS44.TriangleSplineMeasurabilitySupport

namespace TS58
namespace MellinJackson

open MeasureTheory Set

/-!
# TS58 - Triangle Spline Boundary and Exterior Control

This sprint proves the exterior derivative facts for the triangle spline and
records that the three corner points `-1`, `0`, and `1` form a null set.

It does not prove global a.e. differentiability, the distributional derivative
identity, Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.
-/

/-- Classical derivative on the left exterior `(-infty, -1)`. -/
theorem triangleSpline_hasDerivAt_left_exterior
    {x : Real}
    (hx : x < -1) :
    HasDerivAt TS42.MellinJackson.triangleSpline (0 : Real) x := by
  have h_eq :
      Filter.EventuallyEq (nhds x)
        TS42.MellinJackson.triangleSpline
        (fun _ : Real => (0 : Real)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc (by
      intro hmem
      have hylt : y < -1 := hy
      linarith [hmem.1, hylt])
  have h_der : HasDerivAt (fun _ : Real => (0 : Real)) (0 : Real) x := by
    simpa using (hasDerivAt_const (x := x) (c := (0 : Real)))
  exact h_der.congr_of_eventuallyEq h_eq

/-- Classical derivative on the right exterior `(1, infty)`. -/
theorem triangleSpline_hasDerivAt_right_exterior
    {x : Real}
    (hx : 1 < x) :
    HasDerivAt TS42.MellinJackson.triangleSpline (0 : Real) x := by
  have h_eq :
      Filter.EventuallyEq (nhds x)
        TS42.MellinJackson.triangleSpline
        (fun _ : Real => (0 : Real)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc (by
      intro hmem
      have hygt : 1 < y := hy
      linarith [hmem.2, hygt])
  have h_der : HasDerivAt (fun _ : Real => (0 : Real)) (0 : Real) x := by
    simpa using (hasDerivAt_const (x := x) (c := (0 : Real)))
  exact h_der.congr_of_eventuallyEq h_eq

/--
On the left exterior, the classical derivative agrees with
`triangleSplineDeriv`.
-/
theorem triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior
    {x : Real}
    (hx : x < -1) :
    HasDerivAt
      TS42.MellinJackson.triangleSpline
      (TS42.MellinJackson.triangleSplineDeriv x)
      x := by
  have hzero :
      TS42.MellinJackson.triangleSplineDeriv x = 0 :=
    TS44.MellinJackson.triangleSplineDeriv_eq_zero_of_le_neg_one
      (le_of_lt hx)
  simpa [hzero] using triangleSpline_hasDerivAt_left_exterior hx

/--
On the right exterior, the classical derivative agrees with
`triangleSplineDeriv`.
-/
theorem triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior
    {x : Real}
    (hx : 1 < x) :
    HasDerivAt
      TS42.MellinJackson.triangleSpline
      (TS42.MellinJackson.triangleSplineDeriv x)
      x := by
  have hzero :
      TS42.MellinJackson.triangleSplineDeriv x = 0 :=
    TS44.MellinJackson.triangleSplineDeriv_eq_zero_of_one_le
      (le_of_lt hx)
  simpa [hzero] using triangleSpline_hasDerivAt_right_exterior hx

/-- The exceptional corner set of the triangle spline. -/
def triangleSplineCornerSet : Set Real :=
  Set.union
    (Set.union ({(-1 : Real)} : Set Real) ({0} : Set Real))
    ({1} : Set Real)

/-- The exceptional corner set has Lebesgue measure zero. -/
theorem volume_triangleSplineCornerSet :
    volume triangleSplineCornerSet = 0 := by
  have hfinite : triangleSplineCornerSet.Finite := by
    unfold triangleSplineCornerSet
    exact
      ((finite_singleton (-1 : Real)).union (finite_singleton (0 : Real))).union
        (finite_singleton (1 : Real))
  exact hfinite.measure_zero volume

/-!
## Boundary/exterior package
-/

/-- Package of exterior derivative and boundary-null facts. -/
structure TriangleSplineBoundaryExteriorControl where
  left_exterior :
    forall {x : Real}, x < -1 ->
      HasDerivAt TS42.MellinJackson.triangleSpline (0 : Real) x

  right_exterior :
    forall {x : Real}, 1 < x ->
      HasDerivAt TS42.MellinJackson.triangleSpline (0 : Real) x

  left_exterior_matches :
    forall {x : Real}, x < -1 ->
      HasDerivAt
        TS42.MellinJackson.triangleSpline
        (TS42.MellinJackson.triangleSplineDeriv x)
        x

  right_exterior_matches :
    forall {x : Real}, 1 < x ->
      HasDerivAt
        TS42.MellinJackson.triangleSpline
        (TS42.MellinJackson.triangleSplineDeriv x)
        x

  corner_null :
    volume triangleSplineCornerSet = 0

/-- Concrete boundary/exterior package. -/
def triangleSplineBoundaryExteriorControl :
    TriangleSplineBoundaryExteriorControl where
  left_exterior := by
    intro x hx
    exact triangleSpline_hasDerivAt_left_exterior hx
  right_exterior := by
    intro x hx
    exact triangleSpline_hasDerivAt_right_exterior hx
  left_exterior_matches := by
    intro x hx
    exact triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior hx
  right_exterior_matches := by
    intro x hx
    exact triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior hx
  corner_null := volume_triangleSplineCornerSet

/-- Target proposition for TS58. -/
def TriangleSplineBoundaryExteriorControlTarget : Prop :=
  Nonempty TriangleSplineBoundaryExteriorControl

/-- The concrete boundary/exterior package discharges the TS58 target. -/
theorem triangleSplineBoundaryExteriorControlTarget :
    TriangleSplineBoundaryExteriorControlTarget :=
  Nonempty.intro triangleSplineBoundaryExteriorControl

end MellinJackson
end TS58
