import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TS.Goldbach.Strong.TS45.TriangleSplineDerivativeSnorm

namespace TS46
namespace MellinJackson

open MeasureTheory Set

/-!
# TS46 - Triangle Spline Support Measure

This sprint proves the elementary Lebesgue-measure input for the support of
the triangle-spline weak-derivative representative.

It does not prove the `snorm` estimate, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.
-/

/-- The closed support interval `[-1, 1]` has Lebesgue measure `2`. -/
theorem triangleSpline_support_volume_eq_two :
    volume (Icc (-1 : Real) 1) = ENNReal.ofReal 2 := by
  rw [Real.volume_Icc]
  norm_num

/-- The closed support interval `[-1, 1]` has Lebesgue measure at most `2`. -/
theorem triangleSpline_support_volume_le_two :
    volume (Icc (-1 : Real) 1) <= ENNReal.ofReal 2 := by
  rw [triangleSpline_support_volume_eq_two]

/--
Support-measure input for the triangle-spline derivative.

This is the elementary Lebesgue-measure fact needed before the future `snorm`
bound.
-/
structure TriangleSplineSupportMeasureInputs where
  /-- Lebesgue measure of the support interval is bounded by `2`. -/
  support_volume_le_two :
    volume (Icc (-1 : Real) 1) <= ENNReal.ofReal 2

/-- Concrete support-measure input for the triangle-spline derivative. -/
def triangleSplineSupportMeasureInputs :
    TriangleSplineSupportMeasureInputs where
  support_volume_le_two := triangleSpline_support_volume_le_two

/-- Target proposition for the support-measure step. -/
def TriangleSplineSupportMeasureTarget : Prop :=
  Nonempty TriangleSplineSupportMeasureInputs

/-- The concrete support-measure input discharges the TS46 target. -/
theorem triangleSplineSupportMeasureTarget :
    TriangleSplineSupportMeasureTarget :=
  Nonempty.intro triangleSplineSupportMeasureInputs

end MellinJackson
end TS46
