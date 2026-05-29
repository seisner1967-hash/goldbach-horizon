import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS60.TriangleSplineAEClassicalDerivative

namespace TS61
namespace MellinJackson

open MeasureTheory

/-!
# TS61 - Triangle Spline Distributional Derivative Ledger

This sprint records the distributional derivative identity needed after the
TS60 almost-everywhere classical derivative bridge.

It deliberately keeps the test-function API abstract until the exact Mathlib
interface for smooth compactly supported functions is selected. No
integration-by-parts proof is attempted here.
-/

/--
API for the test functions used in the distributional derivative identity.

The fields are intentionally minimal: a test function can be evaluated, and so
can its test-function derivative.
-/
structure TriangleSplineTestFunctionAPI where
  TestFunction : Type
  eval : TestFunction -> Real -> Complex
  derivEval : TestFunction -> Real -> Complex

/--
Distributional derivative contract for the triangle spline.

This is the weak-derivative identity
`integral triangleSpline * phi' = - integral triangleSplineDeriv * phi`,
stated against the abstract test-function API.
-/
structure TriangleSplineDistributionalDerivativeContract where
  testAPI : TriangleSplineTestFunctionAPI

  weak_derivative_identity :
    forall phi : testAPI.TestFunction,
      MeasureTheory.integral (volume : Measure Real)
        (fun x : Real =>
          (TS42.MellinJackson.triangleSpline x : Complex) *
            testAPI.derivEval phi x)
      =
      - (MeasureTheory.integral (volume : Measure Real)
          (fun x : Real =>
            (TS42.MellinJackson.triangleSplineDeriv x : Complex) *
              testAPI.eval phi x))

/--
TS61 target: the distributional derivative identity is available for a chosen
test-function API.
-/
def TriangleSplineDistributionalDerivativeTarget : Prop :=
  Nonempty TriangleSplineDistributionalDerivativeContract

/--
Inputs already available before the future distributional proof.

TS60 supplies the a.e. classical derivative bridge; TS61 records it as an input
for the later integration-by-parts sprint.
-/
structure TriangleSplineDistributionalDerivativeInputs where
  ae_classical_derivative :
    TS60.MellinJackson.TriangleSplineAEClassicalDerivative

/-- Concrete distributional-derivative inputs supplied by TS60. -/
def triangleSplineDistributionalDerivativeInputs :
    TriangleSplineDistributionalDerivativeInputs where
  ae_classical_derivative :=
    TS60.MellinJackson.triangleSplineAEClassicalDerivative

/-- Target proposition for the TS60 input package. -/
def TriangleSplineDistributionalDerivativeInputsTarget : Prop :=
  Nonempty TriangleSplineDistributionalDerivativeInputs

/-- The TS60 input package is available unconditionally. -/
theorem triangleSplineDistributionalDerivativeInputsTarget :
    TriangleSplineDistributionalDerivativeInputsTarget :=
  Nonempty.intro triangleSplineDistributionalDerivativeInputs

end MellinJackson
end TS61
