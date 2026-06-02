import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract

namespace TS64
namespace MellinJackson

/-!
# TS64 - Triangle Spline IPP Integrability Inputs

This sprint records the Bochner-integrability inputs needed before proving the
concrete integration-by-parts identity from TS63.

No integration-by-parts proof is attempted here. The two product integrability
facts remain explicit local obligations.
-/

open MeasureTheory

/--
Integrability inputs for the concrete integration-by-parts identity of TS63.

The left input covers the product `triangleSpline * phi'`; the right input
covers the product `triangleSplineDeriv * phi`.
-/
structure TriangleSplineIPPIntegrabilityInputs where
  left_integrable :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      Integrable
        (fun x : Real =>
          (TS42.MellinJackson.triangleSpline x : Complex) * phi.derivFun x)
        (volume : Measure Real)

  right_integrable :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      Integrable
        (fun x : Real =>
          (TS42.MellinJackson.triangleSplineDeriv x : Complex) * phi.toFun x)
        (volume : Measure Real)

/-- Target proposition for the IPP integrability step. -/
def TriangleSplineIPPIntegrabilityTarget : Prop :=
  Nonempty TriangleSplineIPPIntegrabilityInputs

end MellinJackson
end TS64
