import Mathlib.Tactic
import TS.Goldbach.Strong.TS178.TriangleSplineSincSpectralIntegrability

namespace TS179
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS179 - Triangle Spline Plancherel API Probe

TS177 proves the exact time-side L2 value of the triangle spline.  TS178 proves
that the pi-scale squared-sinc spectral candidate has finite L2 `eLpNorm`.

TS179 checks the Plancherel boundary without claiming a theorem that Mathlib
does not currently expose under the expected concrete names.  The local probe
confirmed that `Real.fourierIntegral`, `Real.fourierIntegralInv`, and
`Real.fourierChar` are available, while ready-made names such as
`Real.fourierIntegral_isometry`, `Real.fourierIntegral_plancherel`,
`fourierIntegral_Plancherel`, and `fourierIntegral_isometry` are not available
in the current Mathlib surface.

The sprint therefore keeps Plancherel as the TS174 contract and proves the
final conditional consumption theorem:

if the TS174 concrete Plancherel isometry is supplied, then the squared-sinc
spectral L2 energy is exactly `ENNReal.ofReal (Real.sqrt (2 / 3))`.

No unconditional Plancherel theorem, explicit formula, zeta-zero summability,
or Goldbach result is claimed here.
-/

/-- Plancherel API names probed during TS179. -/
def plancherelAPIProbeCandidates : List String :=
  [ "Real.fourierIntegral"
  , "Real.fourierIntegralInv"
  , "Real.fourierChar"
  , "Real.fourierIntegral_isometry"
  , "Real.fourierIntegral_plancherel"
  , "fourierIntegral_Plancherel"
  , "fourierIntegral_isometry"
  ]

/-- Read-only outcome of the TS179 Plancherel API probe. -/
inductive PlancherelAPIProbeOutcome where
  | mathlibFourierObjectsAvailable
  | readyMadePlancherelNameNotAvailable
  | useTS174ConcreteContract
  deriving DecidableEq, Repr

/--
If the concrete TS174 Plancherel isometry is supplied, then TS174, TS177, and
TS178 give the exact squared-sinc spectral L2 energy value.
-/
theorem triangleSplineSincL2Energy_eq_sqrt_two_thirds_of_plancherel
    (hplancherel :
      TS174.Goldbach.TriangleSplinePlancherelIsometryStatement) :
    TS174.Goldbach.triangleSplineSincL2Energy =
      ENNReal.ofReal (Real.sqrt (2 / 3)) := by
  calc
    TS174.Goldbach.triangleSplineSincL2Energy =
        TS174.Goldbach.triangleSplineTimeL2Energy :=
          TS174.Goldbach.triangleSplineSincL2Energy_eq_timeL2Energy_of_plancherel
            hplancherel
    _ =
        ENNReal.ofReal (Real.sqrt (2 / 3)) :=
          TS177.Goldbach.triangleSplineTimeELpNormValue

/-- Ledger for the TS179 Plancherel API reality probe. -/
structure TriangleSplinePlancherelAPIProbeLedger where
  ts178_spectral_finiteness :
    TS178.Goldbach.TriangleSplineSincSpectralIntegrabilityLedger

  probed_candidates :
    List String

  probed_candidates_eq :
    probed_candidates = plancherelAPIProbeCandidates

  api_outcome :
    PlancherelAPIProbeOutcome

  api_outcome_eq :
    api_outcome =
      PlancherelAPIProbeOutcome.useTS174ConcreteContract

  plancherel_statement :
    Prop

  plancherel_statement_eq :
    plancherel_statement =
      TS174.Goldbach.TriangleSplinePlancherelIsometryStatement

  spectral_l2_energy_finite :
    TS174.Goldbach.triangleSplineSincL2Energy <
      (Top.top : ENNReal)

  time_l2_energy_value :
    TS174.Goldbach.triangleSplineTimeL2Energy =
      ENNReal.ofReal (Real.sqrt (2 / 3))

  conditional_spectral_value :
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement ->
      TS174.Goldbach.triangleSplineSincL2Energy =
        ENNReal.ofReal (Real.sqrt (2 / 3))

  unconditional_plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  zeta_zero_summability_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS179 Plancherel API probe ledger. -/
noncomputable def triangleSplinePlancherelAPIProbeLedger :
    TriangleSplinePlancherelAPIProbeLedger where
  ts178_spectral_finiteness :=
    TS178.Goldbach.triangleSplineSincSpectralIntegrabilityLedger
  probed_candidates := plancherelAPIProbeCandidates
  probed_candidates_eq := rfl
  api_outcome := PlancherelAPIProbeOutcome.useTS174ConcreteContract
  api_outcome_eq := rfl
  plancherel_statement :=
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement
  plancherel_statement_eq := rfl
  spectral_l2_energy_finite :=
    TS178.Goldbach.triangleSplineSincL2Energy_lt_top
  time_l2_energy_value :=
    TS177.Goldbach.triangleSplineTimeELpNormValue
  conditional_spectral_value :=
    triangleSplineSincL2Energy_eq_sqrt_two_thirds_of_plancherel
  unconditional_plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  zeta_zero_summability_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS179. -/
def TriangleSplinePlancherelAPIProbeTarget : Prop :=
  Nonempty TriangleSplinePlancherelAPIProbeLedger

/-- The TS179 Plancherel API probe target is populated. -/
theorem triangleSplinePlancherelAPIProbeTarget :
    TriangleSplinePlancherelAPIProbeTarget :=
  Nonempty.intro triangleSplinePlancherelAPIProbeLedger

end Goldbach
end TS179

