import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS65.TriangleSplineIPPIntegrabilityDischarge
import TS.Goldbach.Strong.TS66.TriangleSplineIPPProductSupportRestriction

namespace TS67
namespace MellinJackson

/-!
# TS67 - Triangle Spline IPP Integral Restriction

This sprint records the integral-level restriction shape needed for the
concrete triangle-spline integration-by-parts route.

TS65 proves integrability of the two products, and TS66 proves that both
products vanish outside `[-1, 1]`. TS67 packages the next theorem shape:
global Bochner integrals over `volume` should equal the corresponding
integrals over `volume.restrict (Icc (-1) 1)`.

No integral-restriction proof, branch splitting, or integration-by-parts
identity is proved here.
-/

open MeasureTheory Set

/-- Left integrand of the concrete triangle-spline IPP identity. -/
noncomputable def leftIPPIntegrand
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    Real -> Complex :=
  fun x =>
    (TS42.MellinJackson.triangleSpline x : Complex) * phi.derivFun x

/-- Right integrand of the concrete triangle-spline IPP identity. -/
noncomputable def rightIPPIntegrand
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    Real -> Complex :=
  fun x =>
    (TS42.MellinJackson.triangleSplineDeriv x : Complex) * phi.toFun x

/--
Inputs already available before the integral-restriction proof.

This records that TS65 and TS66 have supplied the integrability and pointwise
support facts needed for the future proof.
-/
structure TriangleSplineIPPIntegralRestrictionInputs where
  integrability :
    TS64.MellinJackson.TriangleSplineIPPIntegrabilityInputs

  support_restriction :
    TS66.MellinJackson.TriangleSplineIPPProductSupportRestriction

/-- Concrete TS67 inputs from TS65 and TS66. -/
def triangleSplineIPPIntegralRestrictionInputs :
    TriangleSplineIPPIntegralRestrictionInputs where
  integrability :=
    TS65.MellinJackson.triangleSplineIPPIntegrabilityInputs
  support_restriction :=
    TS66.MellinJackson.triangleSplineIPPProductSupportRestriction

/--
Integral restriction contract for the two concrete IPP products.

This is the integral-level counterpart of TS66 pointwise support restriction.
It does not split `[-1, 1]` into branches and does not prove IPP.
-/
structure TriangleSplineIPPIntegralRestriction where
  inputs :
    TriangleSplineIPPIntegralRestrictionInputs

  left_global_eq_restrict :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral (volume : Measure Real) (leftIPPIntegrand phi)
        =
      integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
        (leftIPPIntegrand phi)

  right_global_eq_restrict :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral (volume : Measure Real) (rightIPPIntegrand phi)
        =
      integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
        (rightIPPIntegrand phi)

/-- Target proposition for TS67. -/
def TriangleSplineIPPIntegralRestrictionTarget : Prop :=
  Nonempty TriangleSplineIPPIntegralRestriction

/-- Target proposition for the already available TS67 inputs. -/
def TriangleSplineIPPIntegralRestrictionInputsTarget : Prop :=
  Nonempty TriangleSplineIPPIntegralRestrictionInputs

/-- TS65 and TS66 supply the inputs for the future integral-restriction proof. -/
theorem triangleSplineIPPIntegralRestrictionInputsTarget :
    TriangleSplineIPPIntegralRestrictionInputsTarget :=
  Nonempty.intro triangleSplineIPPIntegralRestrictionInputs

end MellinJackson
end TS67
