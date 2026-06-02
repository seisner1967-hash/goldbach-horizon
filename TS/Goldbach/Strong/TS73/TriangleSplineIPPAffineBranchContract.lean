import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS72.TriangleSplineIPPRightBranchClosedBridgeProof

namespace TS73
namespace MellinJackson

/-!
# TS73 - Triangle Spline IPP Affine Branch Contract

This sprint records the local affine integration-by-parts contract for the
two closed triangle-spline branches.

TS70 and TS72 have reduced the future global IPP identity to branch integrals
over `[-1, 0]` and `[0, 1]`. TS73 fixes the two exact local identities that
must be proved next: the left branch contributes `phi 0`, while the right
branch contributes `- phi 0`.

No affine integration-by-parts proof, concrete distributional derivative
identity, Sobolev-slot agreement, Plancherel, or Fourier-tail estimate is
proved here.
-/

open MeasureTheory Set

/--
Local affine IPP contract on the two closed branches.

This structure records the exact theorem shape needed before recombining the
two branch identities into the concrete TS63 distributional contract.
-/
structure TriangleSplineIPPAffineBranchContract where
  /--
  Left branch `[-1, 0]`.

  Since `triangleSpline = 1 + x` and `triangleSplineDeriv = 1` on the branch,
  integration by parts gives the boundary contribution `phi 0`.
  -/
  left_affine_ipp :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS69.MellinJackson.leftBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
      =
      phi.toFun 0
        -
      integral TS69.MellinJackson.leftBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)

  /--
  Right branch `[0, 1]`.

  Since `triangleSpline = 1 - x` and `triangleSplineDeriv = -1` on the branch,
  integration by parts gives the boundary contribution `- phi 0`.
  -/
  right_affine_ipp :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral TS71.MellinJackson.rightClosedBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
      =
      - phi.toFun 0
        -
      integral TS71.MellinJackson.rightClosedBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Inputs now available for affine branch IPP. -/
structure TriangleSplineIPPAffineBranchInputs where
  branch_split :
    TS69.MellinJackson.TriangleSplineIPPBranchSplit

  right_closed_bridge :
    TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridge

/-- Concrete inputs from TS70 and TS72. -/
def triangleSplineIPPAffineBranchInputs :
    TriangleSplineIPPAffineBranchInputs where
  branch_split :=
    TS70.MellinJackson.triangleSplineIPPBranchSplit
  right_closed_bridge :=
    TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridge

/-- Target proposition for the affine branch IPP contract. -/
def TriangleSplineIPPAffineBranchContractTarget : Prop :=
  Nonempty TriangleSplineIPPAffineBranchContract

/-- Input target proposition. -/
def TriangleSplineIPPAffineBranchInputsTarget : Prop :=
  Nonempty TriangleSplineIPPAffineBranchInputs

/-- TS70 and TS72 supply the inputs for the future affine branch IPP proof. -/
theorem triangleSplineIPPAffineBranchInputsTarget :
    TriangleSplineIPPAffineBranchInputsTarget :=
  Nonempty.intro triangleSplineIPPAffineBranchInputs

end MellinJackson
end TS73
