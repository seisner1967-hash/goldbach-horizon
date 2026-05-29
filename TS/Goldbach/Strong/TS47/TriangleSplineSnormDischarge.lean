import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TS.Goldbach.Strong.TS46.TriangleSplineSupportMeasure

namespace TS47
namespace MellinJackson

open MeasureTheory Set

/-!
# TS47 - Triangle Spline Snorm Discharge Bridge

This sprint reduces the triangle-spline derivative `snorm <= 2` estimate to a
generic bounded-support `snorm` lemma.

It does not prove the generic `snorm` lemma, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.
-/

/--
Generic bounded-support `snorm` lemma needed for the triangle-spline
derivative.

The future concrete proof should show that a measurable complex function,
bounded by `1` and supported on a measurable set of volume at most `2`, has
`L2` `snorm` at most `2`.
-/
structure BoundedSupportSnormLemma where
  snorm_le_two_of_bounded_support :
    forall (f : Real -> Complex) (E : Set Real),
      Measurable f ->
      (forall {x : Real}, Not (E x) -> f x = 0) ->
      (forall x : Real, norm (f x) <= 1) ->
      volume E <= ENNReal.ofReal 2 ->
      snorm f 2 (volume : Measure Real) <= 2

/-- The complexified triangle-spline derivative representative is measurable. -/
theorem triangleSplineDeriv_complex_measurable :
    Measurable
      (fun x : Real =>
        (TS42.MellinJackson.triangleSplineDeriv x : Complex)) :=
  Complex.measurable_ofReal.comp
    TS44.MellinJackson.triangleSplineDeriv_measurable

/--
The complexified triangle-spline derivative is pointwise bounded by `1`.
-/
theorem triangleSplineDeriv_complex_norm_le_one
    (x : Real) :
    norm ((TS42.MellinJackson.triangleSplineDeriv x : Complex)) <= 1 := by
  simpa [Complex.normSq, Real.norm_eq_abs]
    using TS43.MellinJackson.abs_triangleSplineDeriv_le_one x

/--
Applying the generic bounded-support lemma to the triangle-spline derivative
discharges the TS45 snorm infrastructure.
-/
def triangleSplineDerivativeSnormInfrastructure
    (H : BoundedSupportSnormLemma) :
    TS45.MellinJackson.TriangleSplineDerivativeSnormInfrastructure where
  inputs := TS45.MellinJackson.triangleSplineDerivativeSnormInputs
  deriv_snorm_bound := by
    exact H.snorm_le_two_of_bounded_support
      (fun x : Real => (TS42.MellinJackson.triangleSplineDeriv x : Complex))
      (Icc (-1 : Real) 1)
      triangleSplineDeriv_complex_measurable
      (fun {x} hx => by
        simp [TS44.MellinJackson.triangleSplineDeriv_zero_outside_Icc hx])
      triangleSplineDeriv_complex_norm_le_one
      TS46.MellinJackson.triangleSpline_support_volume_le_two

/--
TS47 target: once the generic bounded-support `snorm` lemma is supplied, the
triangle-spline derivative snorm target is discharged.
-/
theorem triangleSplineDerivativeSnormTarget_of_boundedSupportLemma
    (H : BoundedSupportSnormLemma) :
    TS45.MellinJackson.TriangleSplineDerivativeSnormTarget :=
  Nonempty.intro (triangleSplineDerivativeSnormInfrastructure H)

end MellinJackson
end TS47
