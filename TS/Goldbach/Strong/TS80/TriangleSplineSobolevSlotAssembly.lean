import Mathlib.Tactic
import TS.Goldbach.Strong.TS55.TriangleSplineSobolevAgreementLedger
import TS.Goldbach.Strong.TS60.TriangleSplineAEClassicalDerivative
import TS.Goldbach.Strong.TS79.TriangleSplineDistributionalDerivativeDischarge

namespace TS80
namespace MellinJackson

/-!
# TS80 - Triangle Spline Sobolev Slot Assembly

TS60 proves the a.e. classical derivative agreement, and TS79 proves the
abstract distributional derivative target. The remaining Sobolev-side step is
the exact agreement between the TS41 selected `sobolevDerivative` slot and the
explicit representative `triangleSplineDeriv`.

This sprint records that last slot agreement in a local package and proves
that, once supplied, it mechanically discharges both the TS55 ledger target and
the TS49 Sobolev-agreement target.
-/

open MeasureTheory

/-- Proven inputs available before the final Sobolev-slot agreement. -/
structure TriangleSplineSobolevSlotAssemblyInputs where
  ae_classical_derivative :
    TS60.MellinJackson.TriangleSplineAEClassicalDerivative

  distributional_derivative :
    TS61.MellinJackson.TriangleSplineDistributionalDerivativeContract

/-- Concrete inputs from TS60 and TS79. -/
noncomputable def triangleSplineSobolevSlotAssemblyInputs :
    TriangleSplineSobolevSlotAssemblyInputs where
  ae_classical_derivative :=
    TS60.MellinJackson.triangleSplineAEClassicalDerivative
  distributional_derivative :=
    TS79.MellinJackson.triangleSplineDistributionalDerivativeContract

/--
Sobolev-slot assembly package.

The first two fields are the already-proved real-analysis inputs. The final
field is the exact TS41 Sobolev derivative slot agreement still needed to
produce the TS55/TS49 Sobolev agreement.
-/
structure TriangleSplineSobolevSlotAssembly where
  inputs :
    TriangleSplineSobolevSlotAssemblyInputs

  api :
    TS41.MellinJackson.FourierAPINormalizationLedger

  sobolev_slot_agreement :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (api.sobolevDerivative 1
        (fun x : Real => (TS42.MellinJackson.triangleSpline x : Complex)))
      (fun x : Real => (TS42.MellinJackson.triangleSplineDeriv x : Complex))

/-- A Sobolev-slot assembly package gives the TS55 ledger. -/
noncomputable def triangleSplineSobolevAgreementLedger
    (H : TriangleSplineSobolevSlotAssembly) :
    TS55.MellinJackson.TriangleSplineSobolevAgreementLedger where
  api := H.api
  left_branch_derivative := by
    intro x hx1 hx0
    exact True.intro
  right_branch_derivative := by
    intro x hx0 hx1
    exact True.intro
  boundary_control := True.intro
  distributional_derivative_identity := True.intro
  sobolev_slot_agreement := H.sobolev_slot_agreement

/-- A Sobolev-slot assembly package gives TS49 infrastructure directly. -/
noncomputable def triangleSplineSobolevAgreementInfrastructure
    (H : TriangleSplineSobolevSlotAssembly) :
    TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure :=
  TS55.MellinJackson.triangleSplineSobolevAgreementInfrastructure
    (triangleSplineSobolevAgreementLedger H)

/-- Target proposition for the Sobolev-slot assembly package. -/
def TriangleSplineSobolevSlotAssemblyTarget : Prop :=
  Nonempty TriangleSplineSobolevSlotAssembly

/-- Target proposition for the proved input package. -/
def TriangleSplineSobolevSlotAssemblyInputsTarget : Prop :=
  Nonempty TriangleSplineSobolevSlotAssemblyInputs

/-- TS60 and TS79 provide the input package unconditionally. -/
theorem triangleSplineSobolevSlotAssemblyInputsTarget :
    TriangleSplineSobolevSlotAssemblyInputsTarget :=
  Nonempty.intro triangleSplineSobolevSlotAssemblyInputs

/-- A Sobolev-slot assembly target discharges the TS55 ledger target. -/
theorem triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget
    (H : TriangleSplineSobolevSlotAssemblyTarget) :
    TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget := by
  cases H with
  | intro h =>
      exact
        TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget.of_ledger
          (triangleSplineSobolevAgreementLedger h)

/-- A Sobolev-slot assembly target discharges the TS49 Sobolev target. -/
theorem triangleSplineSobolevAgreementTarget_of_slotAssemblyTarget
    (H : TriangleSplineSobolevSlotAssemblyTarget) :
    TS49.MellinJackson.TriangleSplineSobolevAgreementTarget := by
  exact
    TS55.MellinJackson.triangleSplineSobolevAgreementTarget_of_ledgerTarget
      (triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget H)

end MellinJackson
end TS80
