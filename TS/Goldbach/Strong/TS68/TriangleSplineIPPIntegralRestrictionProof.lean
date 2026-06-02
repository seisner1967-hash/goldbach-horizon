import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.SetIntegral
import TS.Goldbach.Strong.TS67.TriangleSplineIPPIntegralRestriction

namespace TS68
namespace MellinJackson

/-!
# TS68 - Triangle Spline IPP Integral Restriction Proof

This sprint discharges the integral-restriction contract isolated in TS67.

TS66 proves that both concrete integration-by-parts products vanish outside
`[-1, 1]`. Mathlib's `setIntegral_eq_integral_of_forall_compl_eq_zero` then
turns this pointwise support fact into equality between the global Bochner
integral over `volume` and the integral over
`volume.restrict (Icc (-1) 1)`.

No branch splitting, affine integration by parts, distributional derivative
identity, Sobolev-slot agreement, Plancherel, or Fourier-tail estimate is
proved here.
-/

open MeasureTheory Set

/--
The global integral of the left IPP integrand is equal to its integral over
the restricted measure on `[-1, 1]`.
-/
theorem left_global_eq_restrict
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral (volume : Measure Real)
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
      (TS67.MellinJackson.leftIPPIntegrand phi) := by
  have h :
      (integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
        (TS67.MellinJackson.leftIPPIntegrand phi))
        =
      integral (volume : Measure Real)
        (TS67.MellinJackson.leftIPPIntegrand phi) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simpa [TS67.MellinJackson.leftIPPIntegrand] using
      TS66.MellinJackson.left_ipp_product_zero_outside_Icc phi hx
  exact h.symm

/--
The global integral of the right IPP integrand is equal to its integral over
the restricted measure on `[-1, 1]`.
-/
theorem right_global_eq_restrict
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral (volume : Measure Real)
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  have h :
      (integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
        (TS67.MellinJackson.rightIPPIntegrand phi))
        =
      integral (volume : Measure Real)
        (TS67.MellinJackson.rightIPPIntegrand phi) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simpa [TS67.MellinJackson.rightIPPIntegrand] using
      TS66.MellinJackson.right_ipp_product_zero_outside_Icc phi hx
  exact h.symm

/-- Concrete discharge of the TS67 integral-restriction contract. -/
def triangleSplineIPPIntegralRestriction :
    TS67.MellinJackson.TriangleSplineIPPIntegralRestriction where
  inputs :=
    TS67.MellinJackson.triangleSplineIPPIntegralRestrictionInputs
  left_global_eq_restrict := by
    intro phi
    exact left_global_eq_restrict phi
  right_global_eq_restrict := by
    intro phi
    exact right_global_eq_restrict phi

/-- Target proposition for the concrete TS68 restriction discharge. -/
def TriangleSplineIPPIntegralRestrictionProofTarget : Prop :=
  Nonempty TS67.MellinJackson.TriangleSplineIPPIntegralRestriction

/-- TS68 discharges the TS67 target. -/
theorem triangleSplineIPPIntegralRestrictionTarget :
    TS67.MellinJackson.TriangleSplineIPPIntegralRestrictionTarget :=
  Nonempty.intro triangleSplineIPPIntegralRestriction

/-- TS68 also provides its local proof target. -/
theorem triangleSplineIPPIntegralRestrictionProofTarget :
    TriangleSplineIPPIntegralRestrictionProofTarget :=
  Nonempty.intro triangleSplineIPPIntegralRestriction

end MellinJackson
end TS68
