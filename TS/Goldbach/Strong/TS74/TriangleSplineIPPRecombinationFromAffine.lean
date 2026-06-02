import Mathlib.Tactic
import TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract
import TS.Goldbach.Strong.TS73.TriangleSplineIPPAffineBranchContract

namespace TS74
namespace MellinJackson

/-!
# TS74 - Triangle Spline IPP Recombination From Affine Branches

This sprint proves that the two local affine branch IPP identities recorded in
TS73 are sufficient to discharge the concrete distributional contract of TS63.

No affine integration-by-parts proof is attempted here. TS74 is purely a
recombination step: it uses the global restriction from TS68, the branch split
from TS70, the right-closed bridge from TS72, and then cancels the two boundary
terms `phi.toFun 0` and `- phi.toFun 0`.

TS74 does not prove the local affine IPP identities themselves, Sobolev-slot
agreement, Plancherel, or Fourier-tail estimates.
-/

open MeasureTheory Set

/--
The two local affine branch IPP identities imply the concrete TS63
distributional identity.
-/
noncomputable def concreteDistributionalContract_of_affineBranchContract
    (A : TS73.MellinJackson.TriangleSplineIPPAffineBranchContract) :
    TS63.MellinJackson.TriangleSplineConcreteDistributionalContract where
  weak_derivative_identity_concrete := by
    intro phi
    calc
      integral (volume : Measure Real)
          (fun x : Real =>
            (TS42.MellinJackson.triangleSpline x : Complex) *
              phi.derivFun x)
          =
        integral (volume : Measure Real)
          (TS67.MellinJackson.leftIPPIntegrand phi) := by
          rfl
      _ =
        integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
          (TS67.MellinJackson.leftIPPIntegrand phi) := by
          exact TS68.MellinJackson.left_global_eq_restrict phi
      _ =
        integral TS69.MellinJackson.leftBranchMeasure
          (TS67.MellinJackson.leftIPPIntegrand phi)
        +
        integral TS69.MellinJackson.rightBranchMeasure
          (TS67.MellinJackson.leftIPPIntegrand phi) := by
          exact TS70.MellinJackson.left_integral_split phi
      _ =
        integral TS69.MellinJackson.leftBranchMeasure
          (TS67.MellinJackson.leftIPPIntegrand phi)
        +
        integral TS71.MellinJackson.rightClosedBranchMeasure
          (TS67.MellinJackson.leftIPPIntegrand phi) := by
          rw [TS72.MellinJackson.left_rightBranch_eq_closed phi]
      _ =
        (phi.toFun 0
          -
        integral TS69.MellinJackson.leftBranchMeasure
          (TS67.MellinJackson.rightIPPIntegrand phi))
        +
        (- phi.toFun 0
          -
        integral TS71.MellinJackson.rightClosedBranchMeasure
          (TS67.MellinJackson.rightIPPIntegrand phi)) := by
          rw [
            A.left_affine_ipp phi,
            A.right_affine_ipp phi
          ]
      _ =
        - (
          integral TS69.MellinJackson.leftBranchMeasure
            (TS67.MellinJackson.rightIPPIntegrand phi)
          +
          integral TS71.MellinJackson.rightClosedBranchMeasure
            (TS67.MellinJackson.rightIPPIntegrand phi)
        ) := by
          ring
      _ =
        - (
          integral TS69.MellinJackson.leftBranchMeasure
            (TS67.MellinJackson.rightIPPIntegrand phi)
          +
          integral TS69.MellinJackson.rightBranchMeasure
            (TS67.MellinJackson.rightIPPIntegrand phi)
        ) := by
          rw [(TS72.MellinJackson.right_rightBranch_eq_closed phi).symm]
      _ =
        - integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
          (TS67.MellinJackson.rightIPPIntegrand phi) := by
          rw [(TS70.MellinJackson.right_integral_split phi).symm]
      _ =
        - integral (volume : Measure Real)
          (TS67.MellinJackson.rightIPPIntegrand phi) := by
          rw [(TS68.MellinJackson.right_global_eq_restrict phi).symm]
      _ =
        - (integral (volume : Measure Real)
          (fun x : Real =>
            (TS42.MellinJackson.triangleSplineDeriv x : Complex) *
              phi.toFun x)) := by
          rfl

/--
Conditional target: affine branch IPP is sufficient for the concrete
distributional derivative contract.
-/
def TriangleSplineConcreteDistributionalFromAffineTarget : Prop :=
  TS73.MellinJackson.TriangleSplineIPPAffineBranchContract ->
    TS63.MellinJackson.TriangleSplineConcreteDistributionalContract

/-- TS74 proves the conditional route from TS73 to TS63. -/
theorem triangleSplineConcreteDistributionalFromAffineTarget :
    TriangleSplineConcreteDistributionalFromAffineTarget :=
  concreteDistributionalContract_of_affineBranchContract

/-- A proved affine-branch target gives the concrete TS63 target. -/
theorem concreteDistributionalTarget_of_affineBranchTarget
    (H : TS73.MellinJackson.TriangleSplineIPPAffineBranchContractTarget) :
    TS63.MellinJackson.TriangleSplineConcreteDistributionalContractTarget := by
  cases H with
  | intro A =>
      exact
        Nonempty.intro
          (concreteDistributionalContract_of_affineBranchContract A)

end MellinJackson
end TS74
