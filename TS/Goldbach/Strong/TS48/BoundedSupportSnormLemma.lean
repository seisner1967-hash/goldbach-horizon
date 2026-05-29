import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS47.TriangleSplineSnormDischarge

namespace TS48
namespace MellinJackson

open MeasureTheory Set

/-!
# TS48 - Bounded Support Snorm Lemma

This sprint proves the generic bounded-support `snorm` estimate isolated by
TS47 and therefore discharges the triangle-spline derivative `snorm <= 2`
target from TS45.
-/

/--
Concrete target for the generic bounded-support `snorm` lemma used by TS47.
-/
def BoundedSupportSnormTarget : Prop :=
  Nonempty TS47.MellinJackson.BoundedSupportSnormLemma

/--
If the generic bounded-support `snorm` target is supplied, TS47 immediately
discharges the triangle-spline derivative `snorm <= 2` target from TS45.
-/
theorem triangleSplineDerivativeSnormTarget_of_boundedSupportSnormTarget
    (H : BoundedSupportSnormTarget) :
    TS45.MellinJackson.TriangleSplineDerivativeSnormTarget := by
  cases H with
  | intro h =>
      exact
        TS47.MellinJackson.triangleSplineDerivativeSnormTarget_of_boundedSupportLemma
          h

/--
Concrete bounded-support `snorm` lemma.

The proof compares `f` with the indicator of its support, uses Mathlib's
indicator-function `eLpNorm` estimate, and then bounds `sqrt 2` by `2` in
`ENNReal`.
-/
noncomputable def boundedSupportSnormLemma :
    TS47.MellinJackson.BoundedSupportSnormLemma where
  snorm_le_two_of_bounded_support := by
    intro f E _hf hsupport hbound hE
    have hmono :
        snorm f 2 (volume : Measure Real) <=
          snorm (E.indicator fun _ : Real => (1 : Complex)) 2
            (volume : Measure Real) := by
      apply eLpNorm_mono
      intro x
      by_cases hx : E x
      case pos =>
        simpa [Set.indicator_of_mem hx] using hbound x
      case neg =>
        simp [Set.indicator_of_not_mem hx, hsupport hx]
    refine hmono.trans ?_
    have hind :
        snorm (E.indicator fun _ : Real => (1 : Complex)) 2
            (volume : Measure Real) <=
          nnnorm (1 : Complex) * volume E ^ (1 / ((2 : ENNReal).toReal)) :=
      eLpNorm_indicator_const_le (s := E) (c := (1 : Complex)) (p := 2)
    refine hind.trans ?_
    have hpow :
        volume E ^ (1 / ((2 : ENNReal).toReal)) <=
          (ENNReal.ofReal 2) ^ (1 / ((2 : ENNReal).toReal)) := by
      gcongr
    have htwo :
        (ENNReal.ofReal 2) ^ (1 / ((2 : ENNReal).toReal)) <=
          (2 : ENNReal) := by
      norm_num
      rw [one_div, ENNReal.rpow_inv_le_iff (by norm_num : (0 : Real) < 2)]
      norm_num [ENNReal.rpow_two]
    calc
      nnnorm (1 : Complex) * volume E ^ (1 / ((2 : ENNReal).toReal))
          = volume E ^ (1 / ((2 : ENNReal).toReal)) := by norm_num
      _ <= (ENNReal.ofReal 2) ^ (1 / ((2 : ENNReal).toReal)) := hpow
      _ <= (2 : ENNReal) := htwo

/-- The bounded-support `snorm` target is now concretely discharged. -/
theorem boundedSupportSnormTarget :
    BoundedSupportSnormTarget :=
  Nonempty.intro boundedSupportSnormLemma

/-- TS45's triangle-spline derivative `snorm` target follows concretely. -/
theorem triangleSplineDerivativeSnormTarget :
    TS45.MellinJackson.TriangleSplineDerivativeSnormTarget :=
  triangleSplineDerivativeSnormTarget_of_boundedSupportSnormTarget
    boundedSupportSnormTarget

end MellinJackson
end TS48
