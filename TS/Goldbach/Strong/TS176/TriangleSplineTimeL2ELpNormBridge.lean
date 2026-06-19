import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS162.TriangleSplineTraceKernelInstantiation
import TS.Goldbach.Strong.TS175.TriangleSplineSpatialL2EnergyEvaluation

namespace TS176
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS176 - Triangle Spline Time L2 eLpNorm Bridge

TS175 evaluates the elementary interval integral
`int_{-1}^{1} triangleSpline(x)^2 dx = 2 / 3`.

TS174, however, names the time-side L2 quantity using Mathlib's global
`eLpNorm` over Lebesgue measure.  This sprint lifts the TS175 constant to the
global Lebesgue square-energy of the complexified spline:

`int x, ||triangleSplineAsComplex x||^2 dx = 2 / 3`.

The final conversion from this global square-energy identity to the concrete
`eLpNorm` value `sqrt (2 / 3)` is deliberately left as a named future
obligation.  Plancherel, spectral sinc integrability, the explicit formula,
and Goldbach remain out of scope.
-/

/-- Global real square-energy of the triangle spline. -/
noncomputable def triangleSplineGlobalRealSquareEnergy :
    Real :=
  integral
    (volume : Measure Real)
    (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)

/-- Global complex square-energy of the complexified triangle spline. -/
noncomputable def triangleSplineGlobalComplexSquareEnergy :
    Real :=
  integral
    (volume : Measure Real)
    (fun x : Real =>
      norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)

/-- Target statement for the global real square-energy lift. -/
def TriangleSplineGlobalRealSquareEnergyStatement : Prop :=
  triangleSplineGlobalRealSquareEnergy = (2 / 3 : Real)

/-- Target statement for the global complex square-energy lift. -/
def TriangleSplineGlobalComplexSquareEnergyStatement : Prop :=
  triangleSplineGlobalComplexSquareEnergy = (2 / 3 : Real)

/--
Future statement converting the global square-energy identity into the
`eLpNorm` value named in TS174.

TS176 only names this final `eLpNorm` bridge.  It does not prove it.
-/
def TriangleSplineTimeELpNormValueStatement : Prop :=
  TS174.Goldbach.triangleSplineTimeL2Energy =
    ENNReal.ofReal (Real.sqrt (2 / 3))

/-- The square of the real triangle spline is supported in `(-1, 1]`. -/
theorem triangleSplineSquare_support_subset_Ioc :
    Set.Subset
      (Function.support
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      )
      (Set.Ioc (-1 : Real) 1) := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  have hspline_ne :
      Not (TS42.MellinJackson.triangleSpline x = 0) := by
    intro hzero
    simp [hzero] at hx
  have hx_left : -1 < x := by
    by_contra hlt
    have hxle : x <= -1 := le_of_not_gt hlt
    have hzero :
        TS42.MellinJackson.triangleSpline x = 0 := by
      apply TS162.Goldbach.triangleSpline_eq_zero_of_one_le_abs
      have hxnonpos : x <= 0 := by
        linarith
      rw [abs_of_nonpos hxnonpos]
      linarith
    exact hspline_ne hzero
  have hx_right : x <= 1 := by
    by_contra hle
    have hxgt : 1 < x := lt_of_not_ge hle
    have hzero :
        TS42.MellinJackson.triangleSpline x = 0 := by
      apply TS162.Goldbach.triangleSpline_eq_zero_of_one_le_abs
      have hxnonneg : 0 <= x := by
        linarith
      rw [abs_of_nonneg hxnonneg]
      linarith
    exact hspline_ne hzero
  exact And.intro hx_left hx_right

/--
The TS175 interval square-energy is the same as the global Lebesgue
square-energy, because the squared spline is supported in `(-1, 1]`.
-/
theorem triangleSplineSpatialSquareEnergy_eq_globalRealSquareEnergy :
    TS175.Goldbach.triangleSplineSpatialSquareEnergy =
      triangleSplineGlobalRealSquareEnergy := by
  unfold TS175.Goldbach.triangleSplineSpatialSquareEnergy
    triangleSplineGlobalRealSquareEnergy
  exact
    intervalIntegral.integral_eq_integral_of_support_subset
      triangleSplineSquare_support_subset_Ioc

/-- The global real square-energy of the triangle spline is exactly `2/3`. -/
theorem triangleSplineGlobalRealSquareEnergy_eq_two_thirds :
    TriangleSplineGlobalRealSquareEnergyStatement := by
  unfold TriangleSplineGlobalRealSquareEnergyStatement
  calc
    triangleSplineGlobalRealSquareEnergy =
        TS175.Goldbach.triangleSplineSpatialSquareEnergy :=
          triangleSplineSpatialSquareEnergy_eq_globalRealSquareEnergy.symm
    _ = (2 / 3 : Real) :=
          TS175.Goldbach.triangleSplineSpatialSquareEnergy_eq_two_thirds

/--
Pointwise, the squared complex norm of the complexified spline is the same as
the square of the real spline.
-/
theorem triangleSplineAsComplex_norm_sq_eq_real_sq
    (x : Real) :
    norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2 =
      (TS42.MellinJackson.triangleSpline x) ^ 2 := by
  calc
    norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2 =
        Complex.normSq (TS166.Goldbach.triangleSplineAsComplex x) :=
          (Complex.normSq_eq_norm_sq
            (TS166.Goldbach.triangleSplineAsComplex x)).symm
    _ = (TS42.MellinJackson.triangleSpline x) ^ 2 := by
          simp [TS166.Goldbach.triangleSplineAsComplex,
            Complex.normSq_ofReal]
          ring

/-- The global complex square-energy equals the global real square-energy. -/
theorem triangleSplineGlobalComplexSquareEnergy_eq_real :
    triangleSplineGlobalComplexSquareEnergy =
      triangleSplineGlobalRealSquareEnergy := by
  unfold triangleSplineGlobalComplexSquareEnergy
    triangleSplineGlobalRealSquareEnergy
  rw [show
      (fun x : Real =>
        norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2) =
      (fun x : Real =>
        (TS42.MellinJackson.triangleSpline x) ^ 2) from by
        funext x
        exact triangleSplineAsComplex_norm_sq_eq_real_sq x]

/--
The global complex square-energy of the complexified triangle spline is
exactly `2/3`.
-/
theorem triangleSplineGlobalComplexSquareEnergy_eq_two_thirds :
    TriangleSplineGlobalComplexSquareEnergyStatement := by
  unfold TriangleSplineGlobalComplexSquareEnergyStatement
  calc
    triangleSplineGlobalComplexSquareEnergy =
        triangleSplineGlobalRealSquareEnergy :=
          triangleSplineGlobalComplexSquareEnergy_eq_real
    _ = (2 / 3 : Real) :=
          triangleSplineGlobalRealSquareEnergy_eq_two_thirds

/-- Ledger for the TS176 time-side measurable L2 lift. -/
structure TriangleSplineTimeL2ELpNormBridgeLedger where
  ts174_plancherel_interface :
    TS174.Goldbach.TriangleSplinePlancherelInterfaceProbeLedger

  ts175_spatial_square_energy :
    TS175.Goldbach.TriangleSplineSpatialL2EnergyEvaluationLedger

  global_real_square_energy :
    Real

  global_real_square_energy_eq :
    global_real_square_energy =
      triangleSplineGlobalRealSquareEnergy

  global_real_square_energy_value :
    TriangleSplineGlobalRealSquareEnergyStatement

  global_complex_square_energy :
    Real

  global_complex_square_energy_eq :
    global_complex_square_energy =
      triangleSplineGlobalComplexSquareEnergy

  global_complex_square_energy_value :
    TriangleSplineGlobalComplexSquareEnergyStatement

  time_eLpNorm_value_statement :
    Prop

  time_eLpNorm_value_statement_eq :
    time_eLpNorm_value_statement =
      TriangleSplineTimeELpNormValueStatement

  time_eLpNorm_value_not_claimed :
    True

  plancherel_not_claimed :
    True

  spectral_sinc_integrability_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS176 time-side measurable L2 lift ledger. -/
noncomputable def triangleSplineTimeL2ELpNormBridgeLedger :
    TriangleSplineTimeL2ELpNormBridgeLedger where
  ts174_plancherel_interface :=
    TS174.Goldbach.triangleSplinePlancherelInterfaceProbeLedger
  ts175_spatial_square_energy :=
    TS175.Goldbach.triangleSplineSpatialL2EnergyEvaluationLedger
  global_real_square_energy :=
    triangleSplineGlobalRealSquareEnergy
  global_real_square_energy_eq := rfl
  global_real_square_energy_value :=
    triangleSplineGlobalRealSquareEnergy_eq_two_thirds
  global_complex_square_energy :=
    triangleSplineGlobalComplexSquareEnergy
  global_complex_square_energy_eq := rfl
  global_complex_square_energy_value :=
    triangleSplineGlobalComplexSquareEnergy_eq_two_thirds
  time_eLpNorm_value_statement :=
    TriangleSplineTimeELpNormValueStatement
  time_eLpNorm_value_statement_eq := rfl
  time_eLpNorm_value_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  spectral_sinc_integrability_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS176. -/
def TriangleSplineTimeL2ELpNormBridgeTarget : Prop :=
  Nonempty TriangleSplineTimeL2ELpNormBridgeLedger

/-- The TS176 time-side measurable L2 lift target is populated. -/
theorem triangleSplineTimeL2ELpNormBridgeTarget :
    TriangleSplineTimeL2ELpNormBridgeTarget :=
  Nonempty.intro triangleSplineTimeL2ELpNormBridgeLedger

end Goldbach
end TS176
