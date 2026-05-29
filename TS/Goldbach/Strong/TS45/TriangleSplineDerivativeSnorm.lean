import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS44.TriangleSplineMeasurabilitySupport

namespace TS45
namespace MellinJackson

open MeasureTheory

/-!
# TS45 - Triangle Spline Derivative Snorm Roadmap

This sprint isolates the `L2`/`snorm` estimate needed for the
triangle-spline weak-derivative representative.

It does not prove the Lebesgue integral, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.
-/

/--
Elementary inputs already available for the future `L2` norm estimate.

TS43 supplies the pointwise bound, and TS44 supplies measurability and support.
-/
structure TriangleSplineDerivativeSnormInputs where
  /-- Measurability and support data from TS44. -/
  support :
    TS44.MellinJackson.TriangleSplineDerivativeSupportInputs

  /-- Pointwise bound from TS43. -/
  pointwise_bound :
    forall x : Real,
      |TS42.MellinJackson.triangleSplineDeriv x| <= 1

/-- The concrete elementary inputs for the future snorm estimate. -/
def triangleSplineDerivativeSnormInputs :
    TriangleSplineDerivativeSnormInputs where
  support := TS44.MellinJackson.triangleSplineDerivativeSupportInputs
  pointwise_bound := TS43.MellinJackson.abs_triangleSplineDeriv_le_one

/--
Local analytic infrastructure for the triangle-spline derivative snorm bound.

The field `deriv_snorm_bound` is the exact Lebesgue/snorm estimate that a
future integration sprint must prove.
-/
structure TriangleSplineDerivativeSnormInfrastructure where
  /-- Concrete pointwise, measurability, and support inputs. -/
  inputs :
    TriangleSplineDerivativeSnormInputs

  /-- The future `L2`/`snorm` bound for the complexified derivative. -/
  deriv_snorm_bound :
    snorm
      (fun x : Real =>
        (TS42.MellinJackson.triangleSplineDeriv x : Complex))
      2
      (volume : Measure Real)
    <= 2

/-- Extract the snorm bound from the local infrastructure package. -/
theorem deriv_snorm_bound_of_infrastructure
    (H : TriangleSplineDerivativeSnormInfrastructure) :
    snorm
      (fun x : Real =>
        (TS42.MellinJackson.triangleSplineDeriv x : Complex))
      2
      (volume : Measure Real)
    <= 2 :=
  H.deriv_snorm_bound

/-- Roadmap target for the elementary inputs side of the snorm estimate. -/
def TriangleSplineDerivativeSnormInputsTarget : Prop :=
  Nonempty TriangleSplineDerivativeSnormInputs

/-- TS43 and TS44 discharge the elementary inputs target. -/
theorem triangleSplineDerivativeSnormInputsTarget :
    TriangleSplineDerivativeSnormInputsTarget :=
  Nonempty.intro triangleSplineDerivativeSnormInputs

/-- Roadmap target for the derivative snorm estimate itself. -/
def TriangleSplineDerivativeSnormTarget : Prop :=
  Nonempty TriangleSplineDerivativeSnormInfrastructure

end MellinJackson
end TS45
