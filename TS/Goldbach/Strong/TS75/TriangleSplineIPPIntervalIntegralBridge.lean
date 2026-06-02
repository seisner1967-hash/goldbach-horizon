import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS74.TriangleSplineIPPRecombinationFromAffine

namespace TS75
namespace MellinJackson

/-!
# TS75 - Triangle Spline IPP Interval-Integral Bridge

This sprint fixes the bridge between the restricted-measure branch integrals
used in TS73 and the directed interval integrals used by Mathlib's
one-dimensional integration-by-parts API.

No restricted-measure to interval-integral conversion is proved here. No affine
integration-by-parts identity, concrete distributional derivative identity,
Sobolev-slot agreement, Plancherel, or Fourier-tail estimate is proved here.
-/

open MeasureTheory Set

/--
Directed interval integral over the left closed branch `[-1, 0]`.

This is the target shape expected by the finite-interval calculus API.
-/
noncomputable def leftBranchIntervalIntegral
    (f : Real -> Complex) :
    Complex :=
  intervalIntegral f (-1 : Real) 0 (volume : Measure Real)

/--
Directed interval integral over the right closed branch `[0, 1]`.

This is the target shape expected by the finite-interval calculus API.
-/
noncomputable def rightClosedBranchIntervalIntegral
    (f : Real -> Complex) :
    Complex :=
  intervalIntegral f (0 : Real) 1 (volume : Measure Real)

/--
Bridge contract from restricted branch measures to directed interval integrals.

The TS73 affine branch contract is stated using `volume.restrict` on closed
branches. Mathlib's finite-interval integration-by-parts lemmas are typically
stated using directed interval integrals. This structure records the exact
conversion facts needed before applying those lemmas.
-/
structure TriangleSplineIPPIntervalIntegralBridge where
  left_leftBranchMeasure_eq_interval :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS69.MellinJackson.leftBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
      =
      leftBranchIntervalIntegral
        (TS67.MellinJackson.leftIPPIntegrand phi)

  right_leftBranchMeasure_eq_interval :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS69.MellinJackson.leftBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)
      =
      leftBranchIntervalIntegral
        (TS67.MellinJackson.rightIPPIntegrand phi)

  left_rightClosedBranchMeasure_eq_interval :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS71.MellinJackson.rightClosedBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
      =
      rightClosedBranchIntervalIntegral
        (TS67.MellinJackson.leftIPPIntegrand phi)

  right_rightClosedBranchMeasure_eq_interval :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS71.MellinJackson.rightClosedBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)
      =
      rightClosedBranchIntervalIntegral
        (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Inputs available before proving the interval-integral bridge. -/
structure TriangleSplineIPPIntervalIntegralBridgeInputs where
  affine_branch_inputs :
    TS73.MellinJackson.TriangleSplineIPPAffineBranchInputs

  recombination_route :
    TS74.MellinJackson.TriangleSplineConcreteDistributionalFromAffineTarget

/-- Concrete inputs from TS73 and TS74. -/
def triangleSplineIPPIntervalIntegralBridgeInputs :
    TriangleSplineIPPIntervalIntegralBridgeInputs where
  affine_branch_inputs :=
    TS73.MellinJackson.triangleSplineIPPAffineBranchInputs
  recombination_route :=
    TS74.MellinJackson.triangleSplineConcreteDistributionalFromAffineTarget

/-- Target proposition for the interval-integral bridge. -/
def TriangleSplineIPPIntervalIntegralBridgeTarget : Prop :=
  Nonempty TriangleSplineIPPIntervalIntegralBridge

/-- Input target proposition. -/
def TriangleSplineIPPIntervalIntegralBridgeInputsTarget : Prop :=
  Nonempty TriangleSplineIPPIntervalIntegralBridgeInputs

/--
TS73 and TS74 supply the inputs for the future restricted-measure to
interval-integral bridge.
-/
theorem triangleSplineIPPIntervalIntegralBridgeInputsTarget :
    TriangleSplineIPPIntervalIntegralBridgeInputsTarget :=
  Nonempty.intro triangleSplineIPPIntervalIntegralBridgeInputs

end MellinJackson
end TS75
