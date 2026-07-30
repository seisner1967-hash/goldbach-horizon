import Mathlib.Tactic
import TS.Goldbach.Strong.TS324.CertifiedZeroCoverSemantics

namespace TS325
namespace Goldbach

/-!
# TS325: executable payload checker and declared-majorant reflection

This module checks the rational, decidable part of the TS324 zero-box payload.
It verifies interval validity, nonnegative box masses, and the comparison of
the computed rational core majorant with a declared rational bound.

The final theorem combines this Boolean reflection with an independently
supplied `TS324.CertifiedTruncatedZeroCover`.  The checker never inspects true
zeta zeros and does not attempt to decide analytic coverage or box-mass
validity.
-/

/-! ## Boolean structural checker -/

/-- Closed rational interval validity check. -/
def checkRationalInterval
    (I : TS324.Goldbach.RationalInterval) : Bool :=
  decide (I.lower <= I.upper)

/-- Structural checks for one raw zero-box payload. -/
def checkZeroBoxPayload
    (box : TS324.Goldbach.ZeroBoxPayload) : Bool :=
  checkRationalInterval box.realPart &&
    checkRationalInterval box.imagPart &&
      decide (0 <= box.coefficientMassUpper)

/-- Array-level rational well-formedness check. -/
def checkPayloadWellFormed
    (data : TS324.Goldbach.ZeroCoverPayload) : Bool :=
  data.boxes.all checkZeroBoxPayload

theorem checkRationalInterval_iff
    (I : TS324.Goldbach.RationalInterval) :
    checkRationalInterval I = true <-> I.lower <= I.upper := by
  simp [checkRationalInterval]

theorem checkZeroBoxPayload_iff
    (box : TS324.Goldbach.ZeroBoxPayload) :
    checkZeroBoxPayload box = true <->
      box.realPart.lower <= box.realPart.upper /\
      box.imagPart.lower <= box.imagPart.upper /\
      0 <= box.coefficientMassUpper := by
  simp [checkZeroBoxPayload, checkRationalInterval, and_assoc]

theorem checkPayloadWellFormed_iff
    (data : TS324.Goldbach.ZeroCoverPayload) :
    checkPayloadWellFormed data = true <->
      TS324.Goldbach.PayloadWellFormed data := by
  constructor
  next =>
    intro hCheck
    have hAll := Array.all_eq_true.mp hCheck
    exact {
      realIntervalsValid := fun i =>
        (checkZeroBoxPayload_iff data.boxes[i]).mp (hAll i) |>.1
      imagIntervalsValid := fun i =>
        (checkZeroBoxPayload_iff data.boxes[i]).mp (hAll i) |>.2.1
      coefficientMassesNonnegative := fun i =>
        (checkZeroBoxPayload_iff data.boxes[i]).mp (hAll i) |>.2.2
    }
  next =>
    intro hData
    apply Array.all_eq_true.mpr
    intro i
    exact (checkZeroBoxPayload_iff data.boxes[i]).mpr
      (And.intro (hData.realIntervalsValid i)
        (And.intro (hData.imagIntervalsValid i)
          (hData.coefficientMassesNonnegative i)))

instance payloadWellFormedDecidable
    (data : TS324.Goldbach.ZeroCoverPayload) :
    Decidable (TS324.Goldbach.PayloadWellFormed data) := by
  by_cases hCheck : checkPayloadWellFormed data = true
  next => exact isTrue ((checkPayloadWellFormed_iff data).mp hCheck)
  next =>
    exact isFalse (fun hData =>
      hCheck ((checkPayloadWellFormed_iff data).mpr hData))

/-! ## Declared rational majorant checker -/

/-- Check both payload structure and the declared rational core majorant. -/
def checkPayloadBudget
    (data : TS324.Goldbach.ZeroCoverPayload) (declared : Rat) : Bool :=
  checkPayloadWellFormed data &&
    decide (TS324.Goldbach.computedCoreMajorant data <= declared)

/-- Raw claim format suitable for an untrusted external generator. -/
structure PayloadBudgetClaim where
  data : TS324.Goldbach.ZeroCoverPayload
  declaredMajorant : Rat
deriving DecidableEq

/-- Execute all rational checks attached to a payload claim. -/
def checkPayloadBudgetClaim (claim : PayloadBudgetClaim) : Bool :=
  checkPayloadBudget claim.data claim.declaredMajorant

theorem checkPayloadBudget_iff
    (data : TS324.Goldbach.ZeroCoverPayload) (declared : Rat) :
    checkPayloadBudget data declared = true <->
      TS324.Goldbach.PayloadWellFormed data /\
        TS324.Goldbach.computedCoreMajorant data <= declared := by
  simp [checkPayloadBudget, checkPayloadWellFormed_iff]

theorem checkPayloadBudgetClaim_iff (claim : PayloadBudgetClaim) :
    checkPayloadBudgetClaim claim = true <->
      TS324.Goldbach.PayloadWellFormed claim.data /\
        TS324.Goldbach.computedCoreMajorant claim.data <=
          claim.declaredMajorant := by
  exact checkPayloadBudget_iff claim.data claim.declaredMajorant

/-! ## Conditional semantic routing -/

/-- A successful rational check and an independent analytic cover certificate
bound the exact finite TS322 core by the declared rational majorant. -/
theorem finiteWeightedLocalCore_le_of_check
    {H : Nat} {data : TS324.Goldbach.ZeroCoverPayload} {declared : Rat}
    (hCheck : checkPayloadBudget data declared = true)
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H data) :
    TS322.Goldbach.finiteWeightedLocalCore H <= (declared : Real) := by
  have hReflected := (checkPayloadBudget_iff data declared).mp hCheck
  calc
    TS322.Goldbach.finiteWeightedLocalCore H <=
        (TS324.Goldbach.computedCoreMajorant data : Real) :=
      TS324.Goldbach.finiteWeightedLocalCore_le_computedCoreMajorant
        hReflected.1 C
    _ <= (declared : Real) := by exact_mod_cast hReflected.2

theorem finiteWeightedLocalCore_le_of_claim_check
    {H : Nat} {claim : PayloadBudgetClaim}
    (hCheck : checkPayloadBudgetClaim claim = true)
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H claim.data) :
    TS322.Goldbach.finiteWeightedLocalCore H <=
      (claim.declaredMajorant : Real) := by
  exact finiteWeightedLocalCore_le_of_check hCheck C

/-! ## Fail-closed ledger -/

structure TS325Ledger where
  boolean_interval_checker_defined : True
  boolean_box_checker_defined : True
  boolean_payload_checker_defined : True
  boolean_checker_prop_iff_proved : True
  payload_well_formed_decidable_instance_proved : True
  declared_majorant_comparison_checked : True
  payload_budget_reflection_iff_proved : True
  nonredundant_claim_payload_defined : True
  finite_core_bound_routed_conditionally : True
  analytic_zero_cover_not_decided : True
  analytic_zero_cover_not_constructed : True
  concrete_zero_dataset_not_imported : True
  ts323_certificate_not_inhabited : True
  unconditional_half_budget_not_claimed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts325Ledger : TS325Ledger where
  boolean_interval_checker_defined := True.intro
  boolean_box_checker_defined := True.intro
  boolean_payload_checker_defined := True.intro
  boolean_checker_prop_iff_proved := True.intro
  payload_well_formed_decidable_instance_proved := True.intro
  declared_majorant_comparison_checked := True.intro
  payload_budget_reflection_iff_proved := True.intro
  nonredundant_claim_payload_defined := True.intro
  finite_core_bound_routed_conditionally := True.intro
  analytic_zero_cover_not_decided := True.intro
  analytic_zero_cover_not_constructed := True.intro
  concrete_zero_dataset_not_imported := True.intro
  ts323_certificate_not_inhabited := True.intro
  unconditional_half_budget_not_claimed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS325
