import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support
import TS.Goldbach.Strong.TS61.TriangleSplineDistributionalDerivativeLedger

namespace TS62
namespace MellinJackson

/-!
# TS62 - Triangle Spline Test Function API Probe

This sprint selects a concrete, lightweight candidate API for the test
functions used in the TS61 distributional derivative ledger.

The test functions remain plain functions `Real -> Complex`, with explicit
regularity, compact-support, and derivative-agreement fields. No
integration-by-parts proof is attempted here.
-/

/--
Concrete candidate for the test-function data used in the distributional
derivative identity.

The regularity field is intentionally kept at `ContDiff Real 1`; later sprints
can strengthen this to a smoother bundled Mathlib type after the exact API is
chosen.
-/
structure TriangleSplineConcreteTestFunction where
  toFun : Real -> Complex
  derivFun : Real -> Complex

  contDiff_toFun :
    ContDiff Real 1 toFun

  compact_support :
    HasCompactSupport toFun

  deriv_agrees :
    deriv toFun = derivFun

/--
The concrete test-function API obtained from
`TriangleSplineConcreteTestFunction`.
-/
noncomputable def triangleSplineConcreteTestFunctionAPI :
    TS61.MellinJackson.TriangleSplineTestFunctionAPI where
  TestFunction := TriangleSplineConcreteTestFunction
  eval := fun phi x => phi.toFun x
  derivEval := fun phi x => phi.derivFun x

/-- Target proposition for the concrete test-function API probe. -/
def TriangleSplineConcreteTestFunctionAPITarget : Prop :=
  Nonempty TS61.MellinJackson.TriangleSplineTestFunctionAPI

/-- The concrete candidate API discharges the TS62 target. -/
theorem triangleSplineConcreteTestFunctionAPITarget :
    TriangleSplineConcreteTestFunctionAPITarget :=
  Nonempty.intro triangleSplineConcreteTestFunctionAPI

end MellinJackson
end TS62
