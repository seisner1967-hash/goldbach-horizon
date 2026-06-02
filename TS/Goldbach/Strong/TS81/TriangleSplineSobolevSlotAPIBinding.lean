import Mathlib.Tactic
import TS.Goldbach.Strong.TS80.TriangleSplineSobolevSlotAssembly

namespace TS81
namespace MellinJackson

/-!
# TS81 - Triangle Spline Sobolev Slot API Binding

TS80 showed that the TS49/TS55 Sobolev agreement follows from one exact
Sobolev-slot agreement for the TS41 Fourier API ledger. This sprint isolates
that API-level binding as the final local interface obligation.

No concrete Fourier/Sobolev API is fabricated here. A future sprint must
provide a TS41 ledger whose `sobolevDerivative` slot recognizes the already
proved TS79 distributional derivative of the triangle spline.
-/

open MeasureTheory

/--
API binding required to close the triangle-spline Sobolev slot.

The field `sobolev_slot_agreement` is the exact statement that the selected
TS41 `sobolevDerivative` representative agrees a.e. with the explicit weak
derivative `triangleSplineDeriv` proved distributionally in TS79.
-/
structure TriangleSplineSobolevSlotAPIBinding where
  api :
    TS41.MellinJackson.FourierAPINormalizationLedger

  sobolev_slot_agreement :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (api.sobolevDerivative 1
        (fun x : Real => (TS42.MellinJackson.triangleSpline x : Complex)))
      (fun x : Real => (TS42.MellinJackson.triangleSplineDeriv x : Complex))

/-- A TS81 API binding gives the TS80 Sobolev-slot assembly package. -/
noncomputable def triangleSplineSobolevSlotAssembly_of_apiBinding
    (H : TriangleSplineSobolevSlotAPIBinding) :
    TS80.MellinJackson.TriangleSplineSobolevSlotAssembly where
  inputs := TS80.MellinJackson.triangleSplineSobolevSlotAssemblyInputs
  api := H.api
  sobolev_slot_agreement := H.sobolev_slot_agreement

/-- Target proposition for the TS81 API binding. -/
def TriangleSplineSobolevSlotAPIBindingTarget : Prop :=
  Nonempty TriangleSplineSobolevSlotAPIBinding

/-- A TS81 API binding target discharges the TS80 assembly target. -/
theorem triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget
    (H : TriangleSplineSobolevSlotAPIBindingTarget) :
    TS80.MellinJackson.TriangleSplineSobolevSlotAssemblyTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (triangleSplineSobolevSlotAssembly_of_apiBinding h)

/-- A TS81 API binding target discharges the TS55 ledger target. -/
theorem triangleSplineSobolevAgreementLedgerTarget_of_apiBindingTarget
    (H : TriangleSplineSobolevSlotAPIBindingTarget) :
    TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget :=
  TS80.MellinJackson.triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget
    (triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget H)

/-- A TS81 API binding target discharges the TS49 Sobolev target. -/
theorem triangleSplineSobolevAgreementTarget_of_apiBindingTarget
    (H : TriangleSplineSobolevSlotAPIBindingTarget) :
    TS49.MellinJackson.TriangleSplineSobolevAgreementTarget :=
  TS80.MellinJackson.triangleSplineSobolevAgreementTarget_of_slotAssemblyTarget
    (triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget H)

end MellinJackson
end TS81
