import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L2Space
import TS.Goldbach.Strong.TS179.TriangleSplinePlancherelAPIProbe
import TS.Goldbach.Strong.TS204.FinalAnalyticInputsSpecification
import TS.Goldbach.Strong.TS207.NaiveHaarEnergyDivergenceObstruction

namespace TS208
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS208 - Triangle Spline Plancherel Evidence Probe

TS207 closed a false Wall 0 route: the naive Haar square energy diverges at the
lower endpoint.  This sprint returns to Wall 1, the Plancherel input, but does
so in a kernel-specific way.

Instead of trying to prove a global Plancherel theorem for Mathlib's real
Fourier integral, TS208 isolates the exact scalar calculation that would
populate the triangle-spline Plancherel input: the direct integral of the
pi-scale squared-sinc profile squared.

The sprint proves that a future scalar identity

`integral xi, triangleSplineSincRealWeight xi ^ 2 = 2 / 3`

is sufficient to:

* evaluate the TS174 spectral `eLpNorm` at `sqrt (2 / 3)`;
* prove the concrete TS174 triangle-spline Plancherel statement;
* populate the TS204 triangle-spline Plancherel evidence.

No direct `sinc^4` integral, general Plancherel theorem, explicit formula,
Gallagher comparison, or Goldbach theorem is proved.
-/

/--
The direct scalar spectral integral that would bypass a general Plancherel
theorem for this specific kernel.
-/
def TriangleSplineSincFourthIntegralValueStatement : Prop :=
  integral
    (volume : Measure Real)
    (fun xi : Real => TS178.Goldbach.triangleSplineSincRealWeight xi ^ 2) =
      (2 / 3 : Real)

/--
The kernel-specific spectral `eLpNorm` target needed by the TS174/TS204
Plancherel layer.
-/
def TriangleSplineDirectSpectralValueStatement : Prop :=
  TS174.Goldbach.triangleSplineSincL2Energy =
    ENNReal.ofReal (Real.sqrt (2 / 3))

/--
If the direct scalar `sinc^4` integral is known, then the complex spectral
`eLpNorm` is exactly `sqrt (2 / 3)`.
-/
theorem sincComplexELpNorm_eq_sqrt_two_thirds_of_sincFourthIntegral
    (h_sinc4 : TriangleSplineSincFourthIntegralValueStatement) :
    eLpNorm
      TS178.Goldbach.triangleSplineSincComplexWeight
      2
      (volume : Measure Real) =
        ENNReal.ofReal (Real.sqrt (2 / 3)) := by
  unfold TriangleSplineSincFourthIntegralValueStatement at h_sinc4
  rw [eLpNorm_eq_lintegral_rpow_nnnorm
    (by norm_num : Not ((2 : ENNReal) = 0))
    ENNReal.two_ne_top]
  have hnorm_integral :
      integral
        (volume : Measure Real)
        (fun xi : Real =>
          norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)
        =
      (2 / 3 : Real) := by
    calc
      integral
          (volume : Measure Real)
          (fun xi : Real =>
            norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)
          =
        integral
          (volume : Measure Real)
          (fun xi : Real =>
            TS178.Goldbach.triangleSplineSincRealWeight xi ^ 2) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (by
            intro xi
            unfold TS178.Goldbach.triangleSplineSincComplexWeight
            have hnon :
                0 <= TS178.Goldbach.triangleSplineSincRealWeight xi :=
              TS178.Goldbach.triangleSplineSincRealWeight_nonneg xi
            simp [Complex.normSq, Complex.normSq_apply, hnon])
      _ =
        (2 / 3 : Real) := h_sinc4
  have hlintegral_ofReal :
      ENNReal.ofReal
        (integral
          (volume : Measure Real)
          (fun xi : Real =>
            norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2))
        =
      lintegral
        (volume : Measure Real)
        (fun xi : Real =>
          ENNReal.ofReal
            (norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)) := by
    exact
      ofReal_integral_eq_lintegral_ofReal
        TS178.Goldbach.triangleSplineSincComplexNormSq_integrable
        (Filter.Eventually.of_forall (by
          intro xi
          positivity))
  have hlintegral :
      lintegral
        (volume : Measure Real)
        (fun xi : Real =>
          (nnnorm (TS178.Goldbach.triangleSplineSincComplexWeight xi) :
            ENNReal) ^ (2 : ENNReal).toReal)
        =
      ENNReal.ofReal (2 / 3 : Real) := by
    have hcongr :
        lintegral
          (volume : Measure Real)
          (fun xi : Real =>
            (nnnorm (TS178.Goldbach.triangleSplineSincComplexWeight xi) :
              ENNReal) ^ (2 : ENNReal).toReal)
          =
        lintegral
          (volume : Measure Real)
          (fun xi : Real =>
            ENNReal.ofReal
              (norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (by
        intro xi
        change
          (nnnorm (TS178.Goldbach.triangleSplineSincComplexWeight xi) :
            ENNReal) ^ (2 : Real) =
            ENNReal.ofReal
              (norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)
        rw [show
            (nnnorm (TS178.Goldbach.triangleSplineSincComplexWeight xi) :
              ENNReal) =
              ENNReal.ofReal
                (norm (TS178.Goldbach.triangleSplineSincComplexWeight xi)) from by
            exact
              (ofReal_norm_eq_coe_nnnorm
                (TS178.Goldbach.triangleSplineSincComplexWeight xi)).symm]
        rw [ENNReal.ofReal_rpow_of_nonneg
          (norm_nonneg _)
          (by norm_num : (0 : Real) <= 2)]
        norm_num)
    calc
      lintegral
          (volume : Measure Real)
          (fun xi : Real =>
            (nnnorm (TS178.Goldbach.triangleSplineSincComplexWeight xi) :
              ENNReal) ^ (2 : ENNReal).toReal)
          =
        lintegral
          (volume : Measure Real)
          (fun xi : Real =>
            ENNReal.ofReal
              (norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)) :=
          hcongr
      _ =
        ENNReal.ofReal
          (integral
            (volume : Measure Real)
            (fun xi : Real =>
              norm (TS178.Goldbach.triangleSplineSincComplexWeight xi) ^ 2)) :=
          hlintegral_ofReal.symm
      _ =
        ENNReal.ofReal (2 / 3 : Real) := by
          rw [hnorm_integral]
  rw [hlintegral]
  rw [Real.sqrt_eq_rpow]
  norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg
    (by norm_num : (0 : Real) <= 2 / 3)
    (by norm_num : (0 : Real) <= 1 / 2)]

/--
The scalar `sinc^4` integral would give the TS174 spectral energy value.
-/
theorem directSpectralValue_of_sincFourthIntegral
    (h_sinc4 : TriangleSplineSincFourthIntegralValueStatement) :
    TriangleSplineDirectSpectralValueStatement := by
  unfold TriangleSplineDirectSpectralValueStatement
  simpa [TS174.Goldbach.triangleSplineSincL2Energy,
    TS166.Goldbach.triangleSplineScaledSincCandidate,
    TS178.Goldbach.triangleSplineSincComplexWeight,
    TS178.Goldbach.triangleSplineSincRealWeight] using
      sincComplexELpNorm_eq_sqrt_two_thirds_of_sincFourthIntegral h_sinc4

/--
The scalar `sinc^4` integral is enough to prove the concrete TS174
triangle-spline Plancherel statement.
-/
theorem triangleSplinePlancherel_of_sincFourthIntegral
    (h_sinc4 : TriangleSplineSincFourthIntegralValueStatement) :
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement := by
  unfold TS174.Goldbach.TriangleSplinePlancherelIsometryStatement
  have hspectral :
      TS174.Goldbach.triangleSplineSincL2Energy =
        ENNReal.ofReal (Real.sqrt (2 / 3)) :=
    directSpectralValue_of_sincFourthIntegral h_sinc4
  calc
    TS174.Goldbach.triangleSplineFourierL2Energy =
        TS174.Goldbach.triangleSplineSincL2Energy :=
          TS174.Goldbach.triangleSplineFourierL2Energy_eq_sincL2Energy
    _ =
        ENNReal.ofReal (Real.sqrt (2 / 3)) :=
          hspectral
    _ =
        TS174.Goldbach.triangleSplineTimeL2Energy :=
          TS177.Goldbach.triangleSplineTimeELpNormValue.symm

/--
The direct scalar spectral integral would populate the TS204 Plancherel input
evidence bundle.
-/
theorem triangleSplinePlancherelInputEvidence_of_sincFourthIntegral
    (h_sinc4 : TriangleSplineSincFourthIntegralValueStatement) :
    TS204.Goldbach.TriangleSplinePlancherelInputEvidence
      TS204.Goldbach.triangleSplinePlancherelInputContract := by
  exact
    { plancherel := triangleSplinePlancherel_of_sincFourthIntegral h_sinc4
      spectral_energy_transport :=
        TS204.Goldbach.triangleSplinePlancherelEnergyTransport_available }

/-- Ledger recording the TS208 Plancherel evidence probe. -/
structure TriangleSplinePlancherelEvidenceProbeLedger where
  ts179_plancherel_api_probe :
    TS179.Goldbach.TriangleSplinePlancherelAPIProbeLedger

  ts204_final_analytic_inputs :
    TS204.Goldbach.FinalAnalyticInputsSpecificationLedger

  ts207_naive_haar_obstruction :
    TS207.Goldbach.NaiveHaarEnergyDivergenceObstructionLedger

  sinc_fourth_integral_statement :
    Prop

  direct_spectral_value_statement :
    Prop

  sinc_fourth_implies_direct_spectral_value :
    sinc_fourth_integral_statement ->
      direct_spectral_value_statement

  sinc_fourth_implies_plancherel :
    sinc_fourth_integral_statement ->
      TS174.Goldbach.TriangleSplinePlancherelIsometryStatement

  sinc_fourth_implies_ts204_plancherel_evidence :
    sinc_fourth_integral_statement ->
      TS204.Goldbach.TriangleSplinePlancherelInputEvidence
        TS204.Goldbach.triangleSplinePlancherelInputContract

  sinc_fourth_integral_not_proved :
    True

  general_plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS208 Plancherel evidence probe ledger. -/
noncomputable def triangleSplinePlancherelEvidenceProbeLedger :
    TriangleSplinePlancherelEvidenceProbeLedger where
  ts179_plancherel_api_probe :=
    TS179.Goldbach.triangleSplinePlancherelAPIProbeLedger
  ts204_final_analytic_inputs :=
    TS204.Goldbach.finalAnalyticInputsSpecificationLedger
  ts207_naive_haar_obstruction :=
    TS207.Goldbach.naiveHaarEnergyDivergenceObstructionLedger
  sinc_fourth_integral_statement :=
    TriangleSplineSincFourthIntegralValueStatement
  direct_spectral_value_statement :=
    TriangleSplineDirectSpectralValueStatement
  sinc_fourth_implies_direct_spectral_value :=
    directSpectralValue_of_sincFourthIntegral
  sinc_fourth_implies_plancherel :=
    triangleSplinePlancherel_of_sincFourthIntegral
  sinc_fourth_implies_ts204_plancherel_evidence :=
    triangleSplinePlancherelInputEvidence_of_sincFourthIntegral
  sinc_fourth_integral_not_proved := True.intro
  general_plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS208. -/
def TriangleSplinePlancherelEvidenceProbeTarget : Prop :=
  Nonempty TriangleSplinePlancherelEvidenceProbeLedger

/-- The TS208 Plancherel evidence probe target is populated. -/
theorem triangleSplinePlancherelEvidenceProbeTarget :
    TriangleSplinePlancherelEvidenceProbeTarget :=
  Nonempty.intro triangleSplinePlancherelEvidenceProbeLedger

end Goldbach
end TS208
