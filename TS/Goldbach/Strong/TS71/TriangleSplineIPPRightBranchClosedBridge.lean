import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS70.TriangleSplineIPPBranchSplitProof

namespace TS71
namespace MellinJackson

/-!
# TS71 - Triangle Spline IPP Right Branch Closed Bridge

This sprint records the closed-right-branch bridge needed after the TS70
branch split.

TS70 splits the restricted IPP integrals over `[-1, 0]` and `(0, 1]`. The
future affine integration-by-parts proof is more naturally stated on the
closed right interval `[0, 1]`. TS71 fixes the theorem shape saying that the
right-branch integrals over `(0, 1]` can be replaced by integrals over
`[0, 1]` for the two concrete IPP integrands.

No closed-branch bridge proof, affine integration by parts, distributional
derivative identity, Sobolev-slot agreement, Plancherel, or Fourier-tail
estimate is proved here.
-/

open MeasureTheory Set

/-- Closed right branch `[0, 1]`, needed for classical affine IPP. -/
def rightClosedBranchSet : Set Real :=
  Icc (0 : Real) 1

/-- Volume restricted to the closed right branch `[0, 1]`. -/
noncomputable def rightClosedBranchMeasure : Measure Real :=
  (volume : Measure Real).restrict rightClosedBranchSet

/--
Contract: the half-open right branch `(0, 1]` can be replaced by `[0, 1]`
for the two concrete IPP integrands.

This is justified analytically by the fact that the two sets differ only by
the singleton `{0}`. The proof is left to the next sprint.
-/
structure TriangleSplineIPPRightBranchClosedBridge where
  left_rightBranch_eq_closed :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS69.MellinJackson.rightBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
      =
      integral rightClosedBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)

  right_rightBranch_eq_closed :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS69.MellinJackson.rightBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)
      =
      integral rightClosedBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Inputs available before proving the closed-branch bridge. -/
structure TriangleSplineIPPRightBranchClosedBridgeInputs where
  branch_split :
    TS69.MellinJackson.TriangleSplineIPPBranchSplit

/-- Concrete inputs from TS70. -/
def triangleSplineIPPRightBranchClosedBridgeInputs :
    TriangleSplineIPPRightBranchClosedBridgeInputs where
  branch_split :=
    TS70.MellinJackson.triangleSplineIPPBranchSplit

/-- Target proposition for TS71. -/
def TriangleSplineIPPRightBranchClosedBridgeTarget : Prop :=
  Nonempty TriangleSplineIPPRightBranchClosedBridge

/-- Input target proposition. -/
def TriangleSplineIPPRightBranchClosedBridgeInputsTarget : Prop :=
  Nonempty TriangleSplineIPPRightBranchClosedBridgeInputs

/-- TS70 supplies the input package for the future closed-branch bridge proof. -/
theorem triangleSplineIPPRightBranchClosedBridgeInputsTarget :
    TriangleSplineIPPRightBranchClosedBridgeInputsTarget :=
  Nonempty.intro triangleSplineIPPRightBranchClosedBridgeInputs

end MellinJackson
end TS71
