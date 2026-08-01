import Mathlib.Tactic
import TS.Goldbach.Strong.TS325.ExecutablePayloadChecker
import TS.Goldbach.Strong.TS326.ZeroCountSaturationCover
import TS.Goldbach.Strong.TS327.PositiveSymmetryAdapter

namespace TS328
namespace Goldbach

/-!
# TS328: executable grouped zero payload

This module checks the purely rational conditions needed by grouped zero-box
payloads.  It combines the TS325 declared-core check with the TS326 coefficient
allocation and strict imaginary-interval separation.  The external analytic
zero cover remains an explicit premise of the terminal theorem.

The concrete data below are synthetic smoke tests only.  No empirical zero
dataset, analytic counting certificate, trace-budget certificate, or ledger is
introduced here.
-/

/-! ## Symmetric payload construction -/

/-- Append the reflected lower-half-plane boxes to an upper-half-plane payload. -/
def symmetricPayload
    (upper : TS324.Goldbach.ZeroCoverPayload) :
    TS324.Goldbach.ZeroCoverPayload where
  boxes := upper.boxes ++ upper.boxes.map TS327.Goldbach.mirrorBox

/-! ## Executable coefficient allocation -/

/-- Check the rational TS326 coefficient allocation for every box. -/
def checkCoefficientMassAllocation
    (data : TS324.Goldbach.ZeroCoverPayload) : Bool :=
  data.boxes.all fun box =>
    let u := TS326.Goldbach.intervalAbsLower box.imagPart
    decide (0 < u) &&
      decide ((box.multiplicityUpper : Rat) / u ^ 2 <=
        box.coefficientMassUpper)

theorem checkCoefficientMassAllocation_iff
    (data : TS324.Goldbach.ZeroCoverPayload) :
    checkCoefficientMassAllocation data = true <->
      TS326.Goldbach.CertifiedCoefficientMassAllocation data := by
  constructor
  next =>
    intro hCheck
    unfold checkCoefficientMassAllocation at hCheck
    have hAll := Array.all_eq_true.mp hCheck
    exact {
      ordinateLowerPositive := fun i => by
        have hBox := hAll i
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hBox
        exact hBox.1
      allocated := fun i => by
        have hBox := hAll i
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hBox
        exact hBox.2
    }
  next =>
    intro hAllocation
    unfold checkCoefficientMassAllocation
    apply Array.all_eq_true.mpr
    intro i
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact And.intro
      (hAllocation.ordinateLowerPositive i)
      (hAllocation.allocated i)

/-! ## Strict imaginary-interval separation -/

/-- Every pair of distinct boxes has strictly separated imaginary intervals. -/
def ImaginaryIntervalsStrictlyDisjoint
    (data : TS324.Goldbach.ZeroCoverPayload) : Prop :=
  forall i j : Fin data.boxes.size,
    Not (i = j) ->
      data.boxes[i].imagPart.upper < data.boxes[j].imagPart.lower \/
        data.boxes[j].imagPart.upper < data.boxes[i].imagPart.lower

/-- Executable strict-separation check over all finite box indices. -/
def checkImagDisjoint
    (data : TS324.Goldbach.ZeroCoverPayload) : Bool :=
  (List.finRange data.boxes.size).all fun i =>
    (List.finRange data.boxes.size).all fun j =>
      if i = j then true
      else decide (
        data.boxes[i].imagPart.upper < data.boxes[j].imagPart.lower \/
          data.boxes[j].imagPart.upper < data.boxes[i].imagPart.lower)

theorem checkImagDisjoint_iff
    (data : TS324.Goldbach.ZeroCoverPayload) :
    checkImagDisjoint data = true <->
      ImaginaryIntervalsStrictlyDisjoint data := by
  constructor
  next =>
    intro hCheck i j hNe
    unfold checkImagDisjoint at hCheck
    have hOuter := List.all_eq_true.mp hCheck
    have hAtI := hOuter i (List.mem_finRange i)
    have hInner := List.all_eq_true.mp hAtI
    have hAtJ := hInner j (List.mem_finRange j)
    simp only [hNe, if_false, decide_eq_true_eq] at hAtJ
    exact hAtJ
  next =>
    intro hDisjoint
    unfold checkImagDisjoint
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro j hj
    by_cases hEq : i = j
    next => simp [hEq]
    next =>
      simp only [hEq, if_false, decide_eq_true_eq]
      exact hDisjoint i j hEq

/-- Strict rational separation prevents one zero from lying in two distinct boxes. -/
theorem zero_not_in_distinct_boxes_of_checkImagDisjoint
    {data : TS324.Goldbach.ZeroCoverPayload}
    (hCheck : checkImagDisjoint data = true)
    (i j : Fin data.boxes.size) (hNe : Not (i = j))
    (rho : TS324.Goldbach.ConcreteNontrivialZero)
    (hI : TS324.Goldbach.zeroLiesInBox rho data.boxes[i])
    (hJ : TS324.Goldbach.zeroLiesInBox rho data.boxes[j]) :
    False := by
  have hSeparated := (checkImagDisjoint_iff data).mp hCheck i j hNe
  rcases hSeparated with hIJ | hJI
  next =>
    have hIJReal :
        (data.boxes[i].imagPart.upper : Real) <
          (data.boxes[j].imagPart.lower : Real) := by
      exact_mod_cast hIJ
    linarith [hI.2.2.2, hJ.2.2.1]
  next =>
    have hJIReal :
        (data.boxes[j].imagPart.upper : Real) <
          (data.boxes[i].imagPart.lower : Real) := by
      exact_mod_cast hJI
    linarith [hJ.2.2.2, hI.2.2.1]

/-! ## Executable saturation arithmetic -/

/-- Check the finite arithmetic fields of a TS326 saturation certificate. -/
def checkSaturationArithmetic
    (data : TS324.Goldbach.ZeroCoverPayload)
    (localCount : Fin data.boxes.size -> Nat) (N : Nat) : Bool :=
  decide (Finset.sum Finset.univ localCount = N) &&
    decide (forall i : Fin data.boxes.size,
      localCount i <= data.boxes[i].multiplicityUpper)

theorem checkSaturationArithmetic_iff
    (data : TS324.Goldbach.ZeroCoverPayload)
    (localCount : Fin data.boxes.size -> Nat) (N : Nat) :
    checkSaturationArithmetic data localCount N = true <->
      Finset.sum Finset.univ localCount = N /\
        forall i : Fin data.boxes.size,
          localCount i <= data.boxes[i].multiplicityUpper := by
  simp [checkSaturationArithmetic]

/-! ## Grouped payload and budget checks -/

/-- Check all structural, allocation, and separation conditions. -/
def checkGroupedPayload
    (data : TS324.Goldbach.ZeroCoverPayload) : Bool :=
  TS325.Goldbach.checkPayloadWellFormed data &&
    (checkCoefficientMassAllocation data && checkImagDisjoint data)

theorem checkGroupedPayload_iff
    (data : TS324.Goldbach.ZeroCoverPayload) :
    checkGroupedPayload data = true <->
      TS324.Goldbach.PayloadWellFormed data /\
        (TS326.Goldbach.CertifiedCoefficientMassAllocation data /\
          ImaginaryIntervalsStrictlyDisjoint data) := by
  simp [checkGroupedPayload, TS325.Goldbach.checkPayloadWellFormed_iff,
    checkCoefficientMassAllocation_iff, checkImagDisjoint_iff]

/-- Add allocation and strict separation to the TS325 declared-core check. -/
def checkGroupedPayloadBudget
    (claim : TS325.Goldbach.PayloadBudgetClaim) : Bool :=
  TS325.Goldbach.checkPayloadBudgetClaim claim &&
    (checkCoefficientMassAllocation claim.data &&
      checkImagDisjoint claim.data)

theorem checkGroupedPayloadBudget_iff
    (claim : TS325.Goldbach.PayloadBudgetClaim) :
    checkGroupedPayloadBudget claim = true <->
      (TS324.Goldbach.PayloadWellFormed claim.data /\
        TS324.Goldbach.computedCoreMajorant claim.data <=
          claim.declaredMajorant) /\
      (TS326.Goldbach.CertifiedCoefficientMassAllocation claim.data /\
        ImaginaryIntervalsStrictlyDisjoint claim.data) := by
  simp [checkGroupedPayloadBudget,
    TS325.Goldbach.checkPayloadBudgetClaim_iff,
    checkCoefficientMassAllocation_iff, checkImagDisjoint_iff]

/-! ## Synthetic native smoke test -/

def syntheticPositiveBox0 : TS324.Goldbach.ZeroBoxPayload where
  realPart := { lower := 0, upper := 1 }
  imagPart := { lower := 14, upper := 15 }
  multiplicityUpper := 1
  coefficientMassUpper := (1 : Rat) / 100

def syntheticPositiveBox1 : TS324.Goldbach.ZeroBoxPayload where
  realPart := { lower := 0, upper := 1 }
  imagPart := { lower := 20, upper := 21 }
  multiplicityUpper := 1
  coefficientMassUpper := (1 : Rat) / 200

def syntheticUpperPayload : TS324.Goldbach.ZeroCoverPayload where
  boxes := #[syntheticPositiveBox0, syntheticPositiveBox1]

def syntheticSymmetricPayload : TS324.Goldbach.ZeroCoverPayload :=
  symmetricPayload syntheticUpperPayload

def syntheticBudgetClaim : TS325.Goldbach.PayloadBudgetClaim where
  data := syntheticSymmetricPayload
  declaredMajorant := 1

def syntheticLocalCount :
    Fin syntheticSymmetricPayload.boxes.size -> Nat :=
  fun _ => 1

theorem synthetic_grouped_payload_check :
    checkGroupedPayload syntheticSymmetricPayload = true := by
  native_decide

theorem synthetic_grouped_budget_check :
    checkGroupedPayloadBudget syntheticBudgetClaim = true := by
  native_decide

theorem synthetic_saturation_arithmetic_check :
    checkSaturationArithmetic syntheticSymmetricPayload
      syntheticLocalCount 4 = true := by
  native_decide

/-! ## Conditional semantic routing -/

/-- A grouped check only strengthens the TS325 rational check; analytic
coverage remains an independent premise. -/
theorem finiteWeightedLocalCore_le_of_grouped_check
    {H : Nat} {claim : TS325.Goldbach.PayloadBudgetClaim}
    (hCheck : checkGroupedPayloadBudget claim = true)
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H claim.data) :
    TS322.Goldbach.finiteWeightedLocalCore H <=
      (claim.declaredMajorant : Real) := by
  rw [checkGroupedPayloadBudget, Bool.and_eq_true] at hCheck
  exact TS325.Goldbach.finiteWeightedLocalCore_le_of_claim_check hCheck.1 C

end Goldbach
end TS328
