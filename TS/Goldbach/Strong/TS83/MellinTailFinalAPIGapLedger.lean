import Mathlib.Tactic
import TS.Goldbach.Strong.TS54.FourierPlancherelGapLedger
import TS.Goldbach.Strong.TS82.TriangleSplineSobolevAPIRealityProbe

namespace TS83
namespace MellinJackson

/-!
# TS83 - Mellin Tail Final API Gap Ledger

The triangle-spline real-analysis front is now complete up to explicit API
bindings. TS82 isolates the Sobolev-slot recognition contract, and TS54
isolates the compatible Plancherel/L2 `snorm` contract.

This sprint records those final API gaps for the `Cm <= 1` Mellin-tail route
and proves that a compatible final contract package mechanically yields the
TS51 Fourier-tail comparison target, the TS42 triangle-spline tail target, and
the TS33 Mellin-tail majorant contract.
-/

open MeasureTheory
open scoped ENNReal

/--
Final API-gap ledger for the Mellin-tail route.

This is a status object: it records that the remaining `Cm` work is no longer
local spline calculus, but two external API bindings plus the compatible
Fourier-tail comparison package.
-/
structure MellinTailFinalAPIGapLedger where
  sobolev_probe :
    TS82.MellinJackson.TriangleSplineSobolevAPIRealityProbe

  plancherel_gap :
    TS54.MellinJackson.FourierPlancherelGapLedger

  sobolev_slot_recognition_required :
    True

  plancherel_l2_contract_required :
    True

  fourier_tail_comparison_required :
    True

/-- Concrete final API-gap ledger for the current repository state. -/
noncomputable def mellinTailFinalAPIGapLedger :
    MellinTailFinalAPIGapLedger where
  sobolev_probe := TS82.MellinJackson.triangleSplineSobolevAPIRealityProbe
  plancherel_gap := TS54.MellinJackson.fourierPlancherelGapLedger
  sobolev_slot_recognition_required := True.intro
  plancherel_l2_contract_required := True.intro
  fourier_tail_comparison_required := True.intro

/--
Final compatible API contracts for the Mellin-tail route.

The Sobolev recognition contract closes the TS49 side through TS82/TS81/TS80.
The Plancherel contract records the missing TS54 L2/snorm theorem. The
Fourier-tail fields record the final TS51 comparison in a form tied to the
same TS41 ledger.
-/
structure MellinTailFinalAPIContracts where
  sobolev_recognition :
    TS82.MellinJackson.SobolevSlotRecognitionContract

  plancherel :
    TS54.MellinJackson.FourierPlancherelL2Contract

  plancherel_ledger_eq :
    plancherel.ledger = sobolev_recognition.api

  fourierTail :
    TS40.MellinJackson.FourierTailInfrastructure

  fourierTransform_eq_api :
    fourierTail.fourierTransform = sobolev_recognition.api.fourierTransform

  sobolevDerivative_eq_api :
    fourierTail.sobolevDerivative = sobolev_recognition.api.sobolevDerivative

  cutoff :
    Real

  cutoff_pos :
    0 < cutoff

  cutoff_ge_two :
    2 <= cutoff

  tail_snorm_le_one :
    snorm
      (TS51.MellinJackson.triangleSplineFourierTail
        fourierTail.fourierTransform cutoff)
      2
      (volume : Measure Real)
    <= (1 : ENNReal)

/-- A Sobolev recognition contract gives the TS80 Sobolev assembly package. -/
noncomputable def sobolevSlotAssembly_of_recognitionContract
    (H : TS82.MellinJackson.SobolevSlotRecognitionContract) :
    TS80.MellinJackson.TriangleSplineSobolevSlotAssembly :=
  TS81.MellinJackson.triangleSplineSobolevSlotAssembly_of_apiBinding
    (TS82.MellinJackson.apiBinding_of_sobolevSlotRecognitionContract H)

/-- A Sobolev recognition contract gives TS49 infrastructure. -/
noncomputable def sobolevAgreementInfrastructure_of_recognitionContract
    (H : TS82.MellinJackson.SobolevSlotRecognitionContract) :
    TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure :=
  TS80.MellinJackson.triangleSplineSobolevAgreementInfrastructure
    (sobolevSlotAssembly_of_recognitionContract H)

/-- The final contract package supplies the TS51 Fourier-tail comparison input. -/
noncomputable def triangleSplineFourierTailComparisonInputs_of_finalAPIContracts
    (H : MellinTailFinalAPIContracts) :
    TS51.MellinJackson.TriangleSplineFourierTailComparisonInputs where
  fourierTail := H.fourierTail
  sobolev :=
    sobolevAgreementInfrastructure_of_recognitionContract
      H.sobolev_recognition
  fourierTransform_eq_api := H.fourierTransform_eq_api
  sobolevDerivative_eq_api := H.sobolevDerivative_eq_api
  cutoff := H.cutoff
  cutoff_pos := H.cutoff_pos
  cutoff_ge_two := H.cutoff_ge_two
  tail_snorm_le_one := H.tail_snorm_le_one

/-- Target proposition for the final API-gap ledger. -/
def MellinTailFinalAPIGapLedgerTarget : Prop :=
  Nonempty MellinTailFinalAPIGapLedger

/-- Target proposition for the final compatible API contracts. -/
def MellinTailFinalAPIContractsTarget : Prop :=
  Nonempty MellinTailFinalAPIContracts

/-- The final API-gap ledger is populated. -/
theorem mellinTailFinalAPIGapLedgerTarget :
    MellinTailFinalAPIGapLedgerTarget :=
  Nonempty.intro mellinTailFinalAPIGapLedger

/-- Final contracts supply the TS82 Sobolev recognition target. -/
theorem sobolevSlotRecognitionContractTarget_of_finalAPIContractsTarget
    (H : MellinTailFinalAPIContractsTarget) :
    TS82.MellinJackson.SobolevSlotRecognitionContractTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.sobolev_recognition

/-- Final contracts supply the TS54 Plancherel/L2 target. -/
theorem fourierPlancherelL2Target_of_finalAPIContractsTarget
    (H : MellinTailFinalAPIContractsTarget) :
    TS54.MellinJackson.FourierPlancherelL2Target := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.plancherel

/-- Final contracts supply the TS51 Fourier-tail comparison target. -/
theorem triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget
    (H : MellinTailFinalAPIContractsTarget) :
    TS51.MellinJackson.TriangleSplineFourierTailComparisonTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (triangleSplineFourierTailComparisonInputs_of_finalAPIContracts h)

/-- Final contracts supply the TS42 triangle-spline tail target. -/
theorem triangleSplineTailTarget_of_finalAPIContractsTarget
    (H : MellinTailFinalAPIContractsTarget) :
    TS42.MellinJackson.TriangleSplineTailTarget :=
  TS51.MellinJackson.triangleSplineTailTarget_of_fourierTailComparisonTarget
    (triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget H)

/-- Final contracts supply the TS33 Mellin-tail majorant contract `Cm <= 1`. -/
theorem mellinTailContractTarget_of_finalAPIContractsTarget
    (H : MellinTailFinalAPIContractsTarget) :
    Nonempty TS33.Goldbach.MellinTailMajorantContract :=
  TS51.MellinJackson.mellinTailContractTarget_of_fourierTailComparisonTarget
    (triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget H)

end MellinJackson
end TS83
