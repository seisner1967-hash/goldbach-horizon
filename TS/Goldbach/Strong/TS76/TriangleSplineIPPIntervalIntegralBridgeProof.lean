import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS75.TriangleSplineIPPIntervalIntegralBridge

namespace TS76
namespace MellinJackson

/-!
# TS76 - Triangle Spline IPP Interval-Integral Bridge Proof

This sprint discharges the interval-integral bridge contract isolated in TS75.

TS75 records the conversion needed between the closed-branch restricted-measure
integrals used in TS73 and the directed interval integrals used by Mathlib's
finite-interval calculus API. TS76 proves that conversion by combining the
null-endpoint restricted-measure identity `restrict_Ioc_eq_restrict_Icc` with
`intervalIntegral.integral_of_le`.

No affine integration-by-parts identity, concrete distributional derivative
identity, Sobolev-slot agreement, Plancherel, or Fourier-tail estimate is
proved here.
-/

open MeasureTheory Set

/-- The left closed branch restricted measure equals the corresponding `Ioc`
restricted measure used by interval integrals. -/
theorem leftBranchMeasure_eq_leftIocMeasure :
    TS69.MellinJackson.leftBranchMeasure
      =
    (volume : Measure Real).restrict (Ioc (-1 : Real) 0) := by
  have h :
      (volume : Measure Real).restrict (Ioc (-1 : Real) 0)
        =
      (volume : Measure Real).restrict (Icc (-1 : Real) 0) :=
    restrict_Ioc_eq_restrict_Icc
  simpa [
    TS69.MellinJackson.leftBranchMeasure,
    TS69.MellinJackson.leftBranchSet
  ] using h.symm

/-- Generic bridge from the left branch restricted measure to an interval
integral. -/
theorem integral_leftBranchMeasure_eq_interval
    (f : Real -> Complex) :
    integral TS69.MellinJackson.leftBranchMeasure f
      =
    TS75.MellinJackson.leftBranchIntervalIntegral f := by
  rw [
    TS75.MellinJackson.leftBranchIntervalIntegral,
    leftBranchMeasure_eq_leftIocMeasure,
    intervalIntegral.integral_of_le (by norm_num : (-1 : Real) <= 0)
  ]

/-- Generic bridge from the closed right branch restricted measure to an
interval integral. -/
theorem integral_rightClosedBranchMeasure_eq_interval
    (f : Real -> Complex) :
    integral TS71.MellinJackson.rightClosedBranchMeasure f
      =
    TS75.MellinJackson.rightClosedBranchIntervalIntegral f := by
  rw [
    TS75.MellinJackson.rightClosedBranchIntervalIntegral,
    (TS72.MellinJackson.rightBranchMeasure_eq_rightClosedBranchMeasure).symm,
    TS69.MellinJackson.rightBranchMeasure,
    TS69.MellinJackson.rightBranchSet,
    intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1)
  ]

/-- Left-branch bridge for the left IPP integrand. -/
theorem left_leftBranchMeasure_eq_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS69.MellinJackson.leftBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    TS75.MellinJackson.leftBranchIntervalIntegral
      (TS67.MellinJackson.leftIPPIntegrand phi) := by
  exact
    integral_leftBranchMeasure_eq_interval
      (TS67.MellinJackson.leftIPPIntegrand phi)

/-- Left-branch bridge for the right IPP integrand. -/
theorem right_leftBranchMeasure_eq_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS69.MellinJackson.leftBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    TS75.MellinJackson.leftBranchIntervalIntegral
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  exact
    integral_leftBranchMeasure_eq_interval
      (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Closed-right-branch bridge for the left IPP integrand. -/
theorem left_rightClosedBranchMeasure_eq_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS71.MellinJackson.rightClosedBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (TS67.MellinJackson.leftIPPIntegrand phi) := by
  exact
    integral_rightClosedBranchMeasure_eq_interval
      (TS67.MellinJackson.leftIPPIntegrand phi)

/-- Closed-right-branch bridge for the right IPP integrand. -/
theorem right_rightClosedBranchMeasure_eq_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS71.MellinJackson.rightClosedBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  exact
    integral_rightClosedBranchMeasure_eq_interval
      (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Concrete discharge of the TS75 interval-integral bridge contract. -/
def triangleSplineIPPIntervalIntegralBridge :
    TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridge where
  left_leftBranchMeasure_eq_interval := by
    intro phi
    exact left_leftBranchMeasure_eq_interval phi
  right_leftBranchMeasure_eq_interval := by
    intro phi
    exact right_leftBranchMeasure_eq_interval phi
  left_rightClosedBranchMeasure_eq_interval := by
    intro phi
    exact left_rightClosedBranchMeasure_eq_interval phi
  right_rightClosedBranchMeasure_eq_interval := by
    intro phi
    exact right_rightClosedBranchMeasure_eq_interval phi

/-- Target proposition for the concrete TS76 interval-integral bridge proof. -/
def TriangleSplineIPPIntervalIntegralBridgeProofTarget : Prop :=
  Nonempty TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridge

/-- TS76 discharges the TS75 target. -/
theorem triangleSplineIPPIntervalIntegralBridgeTarget :
    TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeTarget :=
  Nonempty.intro triangleSplineIPPIntervalIntegralBridge

/-- TS76 also provides its local proof target. -/
theorem triangleSplineIPPIntervalIntegralBridgeProofTarget :
    TriangleSplineIPPIntervalIntegralBridgeProofTarget :=
  Nonempty.intro triangleSplineIPPIntervalIntegralBridge

end MellinJackson
end TS76
