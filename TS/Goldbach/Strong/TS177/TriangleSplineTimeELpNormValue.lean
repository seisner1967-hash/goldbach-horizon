import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import TS.Goldbach.Strong.TS176.TriangleSplineTimeL2ELpNormBridge

namespace TS177
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS177 - Triangle Spline Time eLpNorm Value

TS176 proves the global Lebesgue square-energy identity

`integral x, norm (triangleSplineAsComplex x) ^ 2 = 2 / 3`.

This sprint converts that global square-energy into the concrete time-side
`eLpNorm` value named in TS174:

`triangleSplineTimeL2Energy = ENNReal.ofReal (Real.sqrt (2 / 3))`.

The proof stays on the time side.  It does not prove Plancherel, spectral sinc
integrability, the Riemann-von Mangoldt explicit formula, or Goldbach.
-/

/-- The complexified triangle spline is a.e. strongly measurable. -/
theorem triangleSplineAsComplex_aestronglyMeasurable :
    AEStronglyMeasurable
      TS166.Goldbach.triangleSplineAsComplex
      (volume : Measure Real) := by
  apply Measurable.aestronglyMeasurable
  unfold TS166.Goldbach.triangleSplineAsComplex
  have hreal :
      Measurable TS42.MellinJackson.triangleSpline := by
    unfold TS42.MellinJackson.triangleSpline
    exact Measurable.ite
      (measurableSet_Ici.inter measurableSet_Iic)
      (measurable_const.sub continuous_abs.measurable)
      measurable_const
  exact Complex.continuous_ofReal.measurable.comp hreal

/-- The real squared spline is integrable on the global support interval. -/
theorem triangleSplineRealSquare_integrableOn_Ioc :
    IntegrableOn
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      (Set.Ioc (-1 : Real) 1)
      (volume : Measure Real) := by
  have hleft :
      IntegrableOn
        (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
        (Set.Ioc (-1 : Real) 0)
        (volume : Measure Real) := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by norm_num : (-1 : Real) <= 0)).mp
        TS175.Goldbach.triangleSplineSquare_intervalIntegrable_left
  have hright :
      IntegrableOn
        (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
        (Set.Ioc (0 : Real) 1)
        (volume : Measure Real) := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by norm_num : (0 : Real) <= 1)).mp
        TS175.Goldbach.triangleSplineSquare_intervalIntegrable_right
  have hunion :
      IntegrableOn
        (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
        (Set.union (Set.Ioc (-1 : Real) 0) (Set.Ioc (0 : Real) 1))
        (volume : Measure Real) := by
    exact hleft.union hright
  have hset :
      Set.union (Set.Ioc (-1 : Real) 0) (Set.Ioc (0 : Real) 1) =
        Set.Ioc (-1 : Real) 1 := by
    ext x
    constructor
    case mp =>
      intro hx
      rcases hx with hx | hx
      case inl =>
        exact And.intro hx.1 (by linarith [hx.2])
      case inr =>
        exact And.intro (by linarith [hx.1]) hx.2
    case mpr =>
      intro hx
      by_cases hx0 : x <= 0
      case pos =>
        left
        exact And.intro hx.1 hx0
      case neg =>
        right
        exact And.intro (lt_of_not_ge hx0) hx.2
  simpa [hset] using hunion

/-- The complex squared norm is integrable on the global support interval. -/
theorem triangleSplineComplexNormSq_integrableOn_Ioc :
    IntegrableOn
      (fun x : Real =>
        norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)
      (Set.Ioc (-1 : Real) 1)
      (volume : Measure Real) := by
  exact
    triangleSplineRealSquare_integrableOn_Ioc.congr_fun
      (by
        intro x _hx
        exact
          (TS176.Goldbach.triangleSplineAsComplex_norm_sq_eq_real_sq x).symm)
      measurableSet_Ioc

/-- The squared complex norm is supported in `(-1,1]`. -/
theorem triangleSplineComplexNormSq_support_subset_Ioc :
    Set.Subset
      (Function.support
        (fun x : Real =>
          norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2))
      (Set.Ioc (-1 : Real) 1) := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  have hxreal :
      Not ((TS42.MellinJackson.triangleSpline x) ^ 2 = 0) := by
    intro hzero
    exact hx
      ((TS176.Goldbach.triangleSplineAsComplex_norm_sq_eq_real_sq x).trans
        hzero)
  exact TS176.Goldbach.triangleSplineSquare_support_subset_Ioc
    (by
      simp only [Function.mem_support, ne_eq]
      exact hxreal)

/-- The global complex squared norm is integrable on the real line. -/
theorem triangleSplineComplexNormSq_integrable :
    Integrable
      (fun x : Real =>
        norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)
      (volume : Measure Real) := by
  exact
    (integrableOn_iff_integrable_of_support_subset
      triangleSplineComplexNormSq_support_subset_Ioc).mp
      triangleSplineComplexNormSq_integrableOn_Ioc

/--
The time-side L2 seminorm of the complexified triangle spline has exact value
`sqrt (2 / 3)`.
-/
theorem triangleSplineTimeELpNormValue :
    TS176.Goldbach.TriangleSplineTimeELpNormValueStatement := by
  unfold TS176.Goldbach.TriangleSplineTimeELpNormValueStatement
  unfold TS174.Goldbach.triangleSplineTimeL2Energy
  rw [eLpNorm_eq_lintegral_rpow_nnnorm
    (by norm_num : Not ((2 : ENNReal) = 0))
    ENNReal.two_ne_top]
  have hlintegral_ofReal :
      ENNReal.ofReal
        (integral
          (volume : Measure Real)
          (fun x : Real =>
            norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2))
        =
      lintegral
        (volume : Measure Real)
        (fun x : Real =>
          ENNReal.ofReal
            (norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)) := by
    exact
      ofReal_integral_eq_lintegral_ofReal
        triangleSplineComplexNormSq_integrable
        (Filter.Eventually.of_forall (by
          intro x
          positivity))
  have hlintegral :
      lintegral
        (volume : Measure Real)
        (fun x : Real =>
          (nnnorm (TS166.Goldbach.triangleSplineAsComplex x) :
            ENNReal) ^ (2 : ENNReal).toReal)
        =
      ENNReal.ofReal (2 / 3 : Real) := by
    have hcongr :
        lintegral
          (volume : Measure Real)
          (fun x : Real =>
            (nnnorm (TS166.Goldbach.triangleSplineAsComplex x) :
              ENNReal) ^ (2 : ENNReal).toReal)
          =
        lintegral
          (volume : Measure Real)
          (fun x : Real =>
            ENNReal.ofReal
              (norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (by
        intro x
        change
          (nnnorm (TS166.Goldbach.triangleSplineAsComplex x) :
            ENNReal) ^ (2 : Real) =
            ENNReal.ofReal
              (norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)
        rw [show
            (nnnorm (TS166.Goldbach.triangleSplineAsComplex x) :
              ENNReal) =
              ENNReal.ofReal
                (norm (TS166.Goldbach.triangleSplineAsComplex x)) from by
            exact
              (ofReal_norm_eq_coe_nnnorm
                (TS166.Goldbach.triangleSplineAsComplex x)).symm]
        rw [ENNReal.ofReal_rpow_of_nonneg
          (norm_nonneg _)
          (by norm_num : (0 : Real) <= 2)]
        norm_num)
    calc
      lintegral
          (volume : Measure Real)
          (fun x : Real =>
            (nnnorm (TS166.Goldbach.triangleSplineAsComplex x) :
              ENNReal) ^ (2 : ENNReal).toReal)
          =
        lintegral
          (volume : Measure Real)
          (fun x : Real =>
            ENNReal.ofReal
              (norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)) :=
          hcongr
      _ =
        ENNReal.ofReal
          (integral
            (volume : Measure Real)
            (fun x : Real =>
              norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2)) :=
          hlintegral_ofReal.symm
      _ =
        ENNReal.ofReal (2 / 3 : Real) := by
          have hglobal :
              TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy =
                (2 / 3 : Real) :=
            TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy_eq_two_thirds
          unfold TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy
            at hglobal
          rw [hglobal]
  rw [hlintegral]
  rw [Real.sqrt_eq_rpow]
  norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg
    (by norm_num : (0 : Real) <= 2 / 3)
    (by norm_num : (0 : Real) <= 1 / 2)]

/-- Ledger for the TS177 time-side eLpNorm value discharge. -/
structure TriangleSplineTimeELpNormValueLedger where
  ts176_time_l2_bridge :
    TS176.Goldbach.TriangleSplineTimeL2ELpNormBridgeLedger

  global_complex_square_energy :
    TS176.Goldbach.TriangleSplineGlobalComplexSquareEnergyStatement

  time_l2_energy_value :
    TS176.Goldbach.TriangleSplineTimeELpNormValueStatement

  plancherel_not_claimed :
    True

  spectral_sinc_integrability_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS177 time-side eLpNorm value ledger. -/
noncomputable def triangleSplineTimeELpNormValueLedger :
    TriangleSplineTimeELpNormValueLedger where
  ts176_time_l2_bridge :=
    TS176.Goldbach.triangleSplineTimeL2ELpNormBridgeLedger
  global_complex_square_energy :=
    TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy_eq_two_thirds
  time_l2_energy_value :=
    triangleSplineTimeELpNormValue
  plancherel_not_claimed := True.intro
  spectral_sinc_integrability_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS177. -/
def TriangleSplineTimeELpNormValueTarget : Prop :=
  Nonempty TriangleSplineTimeELpNormValueLedger

/-- The TS177 time-side eLpNorm value target is populated. -/
theorem triangleSplineTimeELpNormValueTarget :
    TriangleSplineTimeELpNormValueTarget :=
  Nonempty.intro triangleSplineTimeELpNormValueLedger

end Goldbach
end TS177
