import Mathlib.Tactic
import TS.Goldbach.Strong.TS65.TriangleSplineIPPIntegrabilityDischarge
import TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
import TS.Goldbach.Strong.TS44.TriangleSplineMeasurabilitySupport

namespace TS66
namespace MellinJackson

/-!
# TS66 - Triangle Spline IPP Product Support Restriction

This sprint proves that the two concrete integration-by-parts products vanish
outside the triangle-spline support interval `[-1, 1]`.

Together with TS65 integrability, this prepares future restriction of the
global Bochner integrals to `[-1, 1]` before branchwise splitting. No
integration-by-parts identity is proved here.
-/

open Set

/--
The left IPP product vanishes outside `[-1, 1]`, because `triangleSpline`
itself vanishes there.
-/
theorem left_ipp_product_zero_outside_Icc
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction)
    {x : Real}
    (hx : Not ((Icc (-1 : Real) 1) x)) :
    (TS42.MellinJackson.triangleSpline x : Complex) * phi.derivFun x = 0 := by
  have hzero :
      TS42.MellinJackson.triangleSpline x = 0 :=
    TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc hx
  simp [hzero]

/--
The right IPP product vanishes outside `[-1, 1]`, because `triangleSplineDeriv`
vanishes there.
-/
theorem right_ipp_product_zero_outside_Icc
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction)
    {x : Real}
    (hx : Not ((Icc (-1 : Real) 1) x)) :
    (TS42.MellinJackson.triangleSplineDeriv x : Complex) * phi.toFun x = 0 := by
  have hzero :
      TS42.MellinJackson.triangleSplineDeriv x = 0 :=
    TS44.MellinJackson.triangleSplineDeriv_zero_outside_Icc hx
  simp [hzero]

/--
Support-restriction inputs for the two concrete IPP products.

This package records the exact pointwise support facts that future integral
restriction and branchwise splitting sprints will use.
-/
structure TriangleSplineIPPProductSupportRestriction where
  left_zero_outside :
    forall (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction)
      {x : Real},
      Not ((Icc (-1 : Real) 1) x) ->
      (TS42.MellinJackson.triangleSpline x : Complex) * phi.derivFun x = 0

  right_zero_outside :
    forall (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction)
      {x : Real},
      Not ((Icc (-1 : Real) 1) x) ->
      (TS42.MellinJackson.triangleSplineDeriv x : Complex) * phi.toFun x = 0

/-- Concrete support-restriction package for the two IPP products. -/
def triangleSplineIPPProductSupportRestriction :
    TriangleSplineIPPProductSupportRestriction where
  left_zero_outside := by
    intro phi x hx
    exact left_ipp_product_zero_outside_Icc phi hx
  right_zero_outside := by
    intro phi x hx
    exact right_ipp_product_zero_outside_Icc phi hx

/-- Target proposition for TS66. -/
def TriangleSplineIPPProductSupportRestrictionTarget : Prop :=
  Nonempty TriangleSplineIPPProductSupportRestriction

/-- TS66 discharges the product-support restriction target. -/
theorem triangleSplineIPPProductSupportRestrictionTarget :
    TriangleSplineIPPProductSupportRestrictionTarget :=
  Nonempty.intro triangleSplineIPPProductSupportRestriction

end MellinJackson
end TS66
