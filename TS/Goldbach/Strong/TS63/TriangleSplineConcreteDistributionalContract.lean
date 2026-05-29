import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS62.TriangleSplineTestFunctionAPIProbe
import TS.Goldbach.Strong.TS61.TriangleSplineDistributionalDerivativeLedger

namespace TS63
namespace MellinJackson

/-!
# TS63 - Triangle Spline Concrete Distributional Contract

This sprint specializes the abstract TS61 distributional derivative contract to
the concrete TS62 test-function API.

No integration-by-parts proof is attempted here. The weak derivative identity
remains an explicit local obligation, now stated against the concrete
`C1` compact-support test-function package.
-/

open MeasureTheory

/--
Concrete distributional derivative contract for the triangle spline,
specialized to the TS62 concrete `C1` compact-support test-function API.

This is the exact integration-by-parts identity still to be proved.
-/
structure TriangleSplineConcreteDistributionalContract where
  weak_derivative_identity_concrete :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      MeasureTheory.integral (volume : Measure Real)
        (fun x : Real =>
          (TS42.MellinJackson.triangleSpline x : Complex) *
            phi.derivFun x)
      =
      - (MeasureTheory.integral (volume : Measure Real)
          (fun x : Real =>
            (TS42.MellinJackson.triangleSplineDeriv x : Complex) *
              phi.toFun x))

/--
A concrete distributional contract gives the abstract TS61 distributional
contract by using the TS62 concrete test-function API.
-/
noncomputable def distributionalContract_of_concrete
    (H : TriangleSplineConcreteDistributionalContract) :
    TS61.MellinJackson.TriangleSplineDistributionalDerivativeContract where
  testAPI := TS62.MellinJackson.triangleSplineConcreteTestFunctionAPI
  weak_derivative_identity := by
    intro phi
    exact H.weak_derivative_identity_concrete phi

/-- Target proposition for the concrete distributional derivative step. -/
def TriangleSplineConcreteDistributionalContractTarget : Prop :=
  Nonempty TriangleSplineConcreteDistributionalContract

/-- A concrete distributional target gives the TS61 distributional target. -/
theorem distributionalDerivativeTarget_of_concreteTarget
    (H : TriangleSplineConcreteDistributionalContractTarget) :
    TS61.MellinJackson.TriangleSplineDistributionalDerivativeTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (distributionalContract_of_concrete h)

end MellinJackson
end TS63
