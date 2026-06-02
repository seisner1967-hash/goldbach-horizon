import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TS.Goldbach.Strong.TS64.TriangleSplineIPPIntegrabilityInputs
import TS.Goldbach.Strong.TS47.TriangleSplineSnormDischarge

namespace TS65
namespace MellinJackson

/-!
# TS65 - Triangle Spline IPP Integrability Discharge

This sprint proves the two Bochner-integrability inputs isolated in TS64 for
the concrete TS62 test-function API.

It does not prove the integration-by-parts identity itself, the distributional
derivative identity, Sobolev-slot agreement, Plancherel, or Fourier-tail
estimates.
-/

open MeasureTheory

/-- The complex-valued triangle spline is measurable. -/
theorem triangleSpline_complex_measurable :
    Measurable
      (fun x : Real => (TS42.MellinJackson.triangleSpline x : Complex)) := by
  apply Complex.measurable_ofReal.comp
  unfold TS42.MellinJackson.triangleSpline
  exact Measurable.ite measurableSet_Icc
    (measurable_const.sub continuous_abs.measurable)
    measurable_const

/-- The complex-valued triangle spline is pointwise bounded by `2`. -/
theorem triangleSpline_complex_norm_le_two
    (x : Real) :
    norm ((TS42.MellinJackson.triangleSpline x : Complex)) <= 2 := by
  unfold TS42.MellinJackson.triangleSpline
  by_cases hx : -1 <= x /\ x <= 1
  case pos =>
    have h_abs_le_one : abs x <= 1 := abs_le.mpr hx
    have h_abs_le_two : |(1 - |x| : Real)| <= 2 := by
      rw [abs_le]
      constructor <;> nlinarith [abs_nonneg x, h_abs_le_one]
    rw [if_pos hx, Complex.norm_eq_abs]
    change Complex.abs ((1 - |x| : Real) : Complex) <= 2
    rwa [Complex.abs_ofReal]
  case neg =>
    simp [hx]

/-- A concrete TS62 test function is integrable. -/
theorem testFunction_integrable
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    Integrable phi.toFun (volume : Measure Real) :=
  phi.contDiff_toFun.continuous.integrable_of_hasCompactSupport
    phi.compact_support

/-- The concrete derivative function of a TS62 test function is integrable. -/
theorem testFunction_deriv_integrable
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    Integrable phi.derivFun (volume : Measure Real) := by
  have h_cont : Continuous (deriv phi.toFun) :=
    phi.contDiff_toFun.continuous_deriv (by norm_num)
  have h_comp : HasCompactSupport (deriv phi.toFun) :=
    phi.compact_support.deriv
  have h_int : Integrable (deriv phi.toFun) (volume : Measure Real) :=
    h_cont.integrable_of_hasCompactSupport h_comp
  simpa [phi.deriv_agrees] using h_int

/--
The product `triangleSpline * phi'` is integrable for every concrete test
function `phi`.
-/
theorem triangleSpline_mul_testFunctionDeriv_integrable
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    Integrable
      (fun x : Real =>
        (TS42.MellinJackson.triangleSpline x : Complex) * phi.derivFun x)
      (volume : Measure Real) := by
  exact Integrable.bdd_mul
    (testFunction_deriv_integrable phi)
    triangleSpline_complex_measurable.aestronglyMeasurable
    (Exists.intro 2 triangleSpline_complex_norm_le_two)

/--
The product `triangleSplineDeriv * phi` is integrable for every concrete test
function `phi`.
-/
theorem triangleSplineDeriv_mul_testFunction_integrable
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    Integrable
      (fun x : Real =>
        (TS42.MellinJackson.triangleSplineDeriv x : Complex) * phi.toFun x)
      (volume : Measure Real) := by
  exact Integrable.bdd_mul
    (testFunction_integrable phi)
    TS47.MellinJackson.triangleSplineDeriv_complex_measurable.aestronglyMeasurable
    (Exists.intro 1 TS47.MellinJackson.triangleSplineDeriv_complex_norm_le_one)

/-- Concrete discharge of the TS64 integrability input package. -/
def triangleSplineIPPIntegrabilityInputs :
    TS64.MellinJackson.TriangleSplineIPPIntegrabilityInputs where
  left_integrable := by
    intro phi
    exact triangleSpline_mul_testFunctionDeriv_integrable phi
  right_integrable := by
    intro phi
    exact triangleSplineDeriv_mul_testFunction_integrable phi

/-- Target proposition for the concrete IPP integrability discharge. -/
def TriangleSplineIPPIntegrabilityDischargeTarget : Prop :=
  Nonempty TS64.MellinJackson.TriangleSplineIPPIntegrabilityInputs

/-- TS65 discharges the TS64 target. -/
theorem triangleSplineIPPIntegrabilityTarget :
    TS64.MellinJackson.TriangleSplineIPPIntegrabilityTarget :=
  Nonempty.intro triangleSplineIPPIntegrabilityInputs

/-- TS65 also provides its local discharge target. -/
theorem triangleSplineIPPIntegrabilityDischargeTarget :
    TriangleSplineIPPIntegrabilityDischargeTarget :=
  Nonempty.intro triangleSplineIPPIntegrabilityInputs

end MellinJackson
end TS65
