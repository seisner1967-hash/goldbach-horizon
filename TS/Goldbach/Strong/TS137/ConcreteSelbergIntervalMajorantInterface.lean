import Mathlib.Tactic
import TS.Goldbach.Strong.TS136.SelbergIntervalMajorantLedger

namespace TS137
namespace Goldbach

/-!
# TS137 - Concrete Selberg Interval Majorant Interface

TS136 connects the finite optimal Selberg weights to the TS30/TS99/TS97
interfaces once an interval majorant, interval sieve theorem, and
Brun-Titchmarsh budget comparison are supplied.

This sprint names the concrete analytic interface for those remaining interval
inputs.  It does not prove the Selberg interval sieve theorem or the
Brun-Titchmarsh comparison.  Instead it fixes the data and the exact proof
fields needed to instantiate the TS30 objects and then feeds them through the
TS136 bridge.
-/

/--
Concrete data for an interval Selberg majorant.

The natural-valued `majorantValue` is the actual TS30 majorant.  The rational
`mainTerm`, `errorTerm`, and `majorantRat` fields document the intended
analytic decomposition of the majorant and keep the future asymptotic
comparison target local.
-/
structure ConcreteSelbergIntervalMajorantData where
  level :
    Nat

  hlevel :
    0 < level

  majorantValue :
    Nat -> Nat -> Nat -> Nat

  mainTerm :
    Nat -> Nat -> Nat -> Rat

  errorTerm :
    Nat -> Nat -> Nat -> Rat

  majorantRat :
    Nat -> Nat -> Nat -> Rat

  majorant_rat_formula :
    forall x Q n : Nat,
      majorantRat x Q n =
        mainTerm x Q n + errorTerm x Q n

  error_nonnegative :
    forall x Q n : Nat,
      0 <= errorTerm x Q n

  denominator_evaluation_obligation :
    True

  interval_remainder_obligation :
    True

/-- The TS30 natural-valued interval majorant attached to concrete data. -/
def concreteSelbergIntervalMajorant
    (data : ConcreteSelbergIntervalMajorantData) :
    TS30.Goldbach.SelbergIntervalMajorant where
  majorant := data.majorantValue

/--
Concrete proof obligations for the interval Selberg majorant.

These are exactly the two TS30 theorems still needed after the finite Selberg
algebra has been closed:

* the interval sieve bound;
* the comparison with the TS22 Brun-Titchmarsh ceiling.
-/
structure ConcreteSelbergIntervalMajorantProofs
    (data : ConcreteSelbergIntervalMajorantData) where
  sieve_bound :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      TS22.Goldbach.primeIntervalCard n
          (TS15.Goldbach.intervalScale x Q) <=
        data.majorantValue x Q n

  majorant_le_budget :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      data.majorantValue x Q n <=
        TS22.Goldbach.brunTitchmarshCeilBudget x Q

  interval_sieve_theorem_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Concrete data and proofs instantiate the TS30 sieve-bound package. -/
def concreteSelbergSieveIntervalBound
    (data : ConcreteSelbergIntervalMajorantData)
    (proofs : ConcreteSelbergIntervalMajorantProofs data) :
    TS30.Goldbach.SelbergSieveIntervalBound
      (concreteSelbergIntervalMajorant data) where
  sieve_bound := by
    intro x Q n hx hQ hn
    exact proofs.sieve_bound x Q n hx hQ hn

/-- Concrete data and proofs instantiate the TS30 budget-comparison package. -/
def concreteSelbergMajorantBudgetComparison
    (data : ConcreteSelbergIntervalMajorantData)
    (proofs : ConcreteSelbergIntervalMajorantProofs data) :
    TS30.Goldbach.SelbergMajorantBudgetComparison
      (concreteSelbergIntervalMajorant data) where
  majorant_le_budget := by
    intro x Q n hx hQ hn
    exact proofs.majorant_le_budget x Q n hx hQ hn

/--
Concrete interval-majorant ledger.

Given concrete data and the two TS30 proof obligations, the finite optimal
Selberg weights from TS135/TS136 feed the TS99 and TS97 high-level routes.
-/
structure ConcreteSelbergIntervalMajorantLedger
    (data : ConcreteSelbergIntervalMajorantData) where
  proofs :
    ConcreteSelbergIntervalMajorantProofs data

  majorant :
    TS30.Goldbach.SelbergIntervalMajorant

  majorant_eq :
    majorant =
      concreteSelbergIntervalMajorant data

  sieve :
    TS30.Goldbach.SelbergSieveIntervalBound majorant

  budget :
    TS30.Goldbach.SelbergMajorantBudgetComparison majorant

  optimalBudgetBridge :
    TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudget data.level

  weightInfrastructure :
    TS99.Goldbach.SelbergSieveWeightInfrastructure

  brunTitchmarshInput :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger

  data_majorant_formula :
    forall x Q n : Nat,
      data.majorantRat x Q n =
        data.mainTerm x Q n + data.errorTerm x Q n

  data_error_nonnegative :
    forall x Q n : Nat,
      0 <= data.errorTerm x Q n

  denominator_evaluation_obligation :
    True

  interval_remainder_obligation :
    True

/-- Concrete data and proofs populate the TS137 interval-majorant ledger. -/
noncomputable def concreteSelbergIntervalMajorantLedger
    (data : ConcreteSelbergIntervalMajorantData)
    (proofs : ConcreteSelbergIntervalMajorantProofs data) :
    ConcreteSelbergIntervalMajorantLedger data where
  proofs := proofs
  majorant :=
    concreteSelbergIntervalMajorant data
  majorant_eq := rfl
  sieve :=
    concreteSelbergSieveIntervalBound data proofs
  budget :=
    concreteSelbergMajorantBudgetComparison data proofs
  optimalBudgetBridge :=
    TS136.Goldbach.selbergIntervalMajorantFromOptimalBudget
      data.level
      data.hlevel
      (concreteSelbergIntervalMajorant data)
      (concreteSelbergSieveIntervalBound data proofs)
      (concreteSelbergMajorantBudgetComparison data proofs)
  weightInfrastructure :=
    TS136.Goldbach.selbergSieveWeightInfrastructure_of_intervalMajorant
      (TS136.Goldbach.selbergIntervalMajorantFromOptimalBudget
        data.level
        data.hlevel
        (concreteSelbergIntervalMajorant data)
        (concreteSelbergSieveIntervalBound data proofs)
        (concreteSelbergMajorantBudgetComparison data proofs))
  brunTitchmarshInput :=
    TS136.Goldbach.brunTitchmarshFinalInputLedger_of_intervalMajorant
      (TS136.Goldbach.selbergIntervalMajorantFromOptimalBudget
        data.level
        data.hlevel
        (concreteSelbergIntervalMajorant data)
        (concreteSelbergSieveIntervalBound data proofs)
        (concreteSelbergMajorantBudgetComparison data proofs))
  data_majorant_formula :=
    data.majorant_rat_formula
  data_error_nonnegative :=
    data.error_nonnegative
  denominator_evaluation_obligation :=
    data.denominator_evaluation_obligation
  interval_remainder_obligation :=
    data.interval_remainder_obligation

/-- A TS137 concrete ledger supplies the TS99 infrastructure. -/
def selbergSieveWeightInfrastructure_of_concreteIntervalMajorant
    {data : ConcreteSelbergIntervalMajorantData}
    (H : ConcreteSelbergIntervalMajorantLedger data) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure :=
  H.weightInfrastructure

/-- A TS137 concrete ledger supplies the TS97 final Brun-Titchmarsh input. -/
def brunTitchmarshFinalInputLedger_of_concreteIntervalMajorant
    {data : ConcreteSelbergIntervalMajorantData}
    (H : ConcreteSelbergIntervalMajorantLedger data) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger :=
  H.brunTitchmarshInput

/--
Bridge target: concrete data plus the two TS30 proof obligations populate the
TS137 concrete interval-majorant ledger.
-/
def ConcreteSelbergIntervalMajorantBridgeTarget : Prop :=
  forall data : ConcreteSelbergIntervalMajorantData,
    ConcreteSelbergIntervalMajorantProofs data ->
      Nonempty (ConcreteSelbergIntervalMajorantLedger data)

/-- The concrete interval-majorant bridge target is populated. -/
theorem concreteSelbergIntervalMajorantBridgeTarget :
    ConcreteSelbergIntervalMajorantBridgeTarget := by
  intro data proofs
  exact
    Nonempty.intro
      (concreteSelbergIntervalMajorantLedger data proofs)

/-- Target proposition for a fully supplied concrete interval-majorant ledger. -/
def ConcreteSelbergIntervalMajorantLedgerTarget : Prop :=
  Nonempty (Sigma fun data : ConcreteSelbergIntervalMajorantData =>
    ConcreteSelbergIntervalMajorantLedger data)

/-- A fully supplied TS137 ledger feeds the TS99 infrastructure target. -/
theorem selbergSieveWeightInfrastructureTarget_of_concreteIntervalMajorantTarget
    (H : ConcreteSelbergIntervalMajorantLedgerTarget) :
    TS99.Goldbach.SelbergSieveWeightInfrastructureTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk data package =>
          exact
            Nonempty.intro
              (selbergSieveWeightInfrastructure_of_concreteIntervalMajorant
                package)

/-- A fully supplied TS137 ledger feeds the TS97 final Brun-Titchmarsh target. -/
theorem brunTitchmarshFinalInputLedgerTarget_of_concreteIntervalMajorantTarget
    (H : ConcreteSelbergIntervalMajorantLedgerTarget) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk data package =>
          exact
            Nonempty.intro
              (brunTitchmarshFinalInputLedger_of_concreteIntervalMajorant
                package)

/-- TS137 keeps the TS136 bridge target available. -/
theorem selbergIntervalMajorantFromOptimalBudgetBridgeTarget :
    TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudgetBridgeTarget :=
  TS136.Goldbach.selbergIntervalMajorantFromOptimalBudgetBridgeTarget

end Goldbach
end TS137
