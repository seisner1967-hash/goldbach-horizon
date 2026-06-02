import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.SetIntegral
import TS.Goldbach.Strong.TS71.TriangleSplineIPPRightBranchClosedBridge

namespace TS72
namespace MellinJackson

/-!
# TS72 - Triangle Spline IPP Right Branch Closed Bridge Proof

This sprint discharges the closed-right-branch bridge contract isolated in
TS71.

TS71 records that the right-branch integrals over `(0, 1]` should be
replaceable by integrals over `[0, 1]`. TS72 proves this by using Mathlib's
Lebesgue-measure fact that adding the singleton `{0}` does not change the
restricted measure or the corresponding Bochner integral.

No affine integration by parts, concrete distributional derivative identity,
Sobolev-slot agreement, Plancherel, or Fourier-tail estimate is proved here.
-/

open MeasureTheory Set

/-- The half-open and closed right branch restricted measures coincide. -/
theorem rightBranchMeasure_eq_rightClosedBranchMeasure :
    TS69.MellinJackson.rightBranchMeasure
      =
    TS71.MellinJackson.rightClosedBranchMeasure := by
  have h :
      (volume : Measure Real).restrict (Ioc (0 : Real) 1)
        =
      (volume : Measure Real).restrict (Icc (0 : Real) 1) :=
    restrict_Ioc_eq_restrict_Icc
  simpa [
    TS69.MellinJackson.rightBranchMeasure,
    TS69.MellinJackson.rightBranchSet,
    TS71.MellinJackson.rightClosedBranchMeasure,
    TS71.MellinJackson.rightClosedBranchSet
  ] using h

/-- Generic right-branch closed bridge for any Bochner integrand. -/
theorem integral_rightBranch_eq_rightClosedBranch
    (f : Real -> Complex) :
    integral TS69.MellinJackson.rightBranchMeasure f
      =
    integral TS71.MellinJackson.rightClosedBranchMeasure f := by
  rw [rightBranchMeasure_eq_rightClosedBranchMeasure]

/-- Right-branch closed bridge for the left IPP integrand. -/
theorem left_rightBranch_eq_closed
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS69.MellinJackson.rightBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    integral TS71.MellinJackson.rightClosedBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi) := by
  exact
    integral_rightBranch_eq_rightClosedBranch
      (TS67.MellinJackson.leftIPPIntegrand phi)

/-- Right-branch closed bridge for the right IPP integrand. -/
theorem right_rightBranch_eq_closed
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS69.MellinJackson.rightBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    integral TS71.MellinJackson.rightClosedBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  exact
    integral_rightBranch_eq_rightClosedBranch
      (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Concrete discharge of the TS71 right-branch closed bridge contract. -/
def triangleSplineIPPRightBranchClosedBridge :
    TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridge where
  left_rightBranch_eq_closed := by
    intro phi
    exact left_rightBranch_eq_closed phi
  right_rightBranch_eq_closed := by
    intro phi
    exact right_rightBranch_eq_closed phi

/-- Target proposition for the concrete TS72 closed-branch bridge discharge. -/
def TriangleSplineIPPRightBranchClosedBridgeProofTarget : Prop :=
  Nonempty TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridge

/-- TS72 discharges the TS71 target. -/
theorem triangleSplineIPPRightBranchClosedBridgeTarget :
    TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeTarget :=
  Nonempty.intro triangleSplineIPPRightBranchClosedBridge

/-- TS72 also provides its local proof target. -/
theorem triangleSplineIPPRightBranchClosedBridgeProofTarget :
    TriangleSplineIPPRightBranchClosedBridgeProofTarget :=
  Nonempty.intro triangleSplineIPPRightBranchClosedBridge

end MellinJackson
end TS72
