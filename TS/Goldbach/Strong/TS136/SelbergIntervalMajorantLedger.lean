import Mathlib.Tactic
import TS.Goldbach.Strong.TS135.SelbergFiniteMobiusReconstructionExpansionDischarge

namespace TS136
namespace Goldbach

/-!
# TS136 - Selberg Interval Majorant Ledger

TS135 closes the finite Mobius reconstruction and proves that the reconstructed
optimal Selberg weights attain the exact dense-side budget `1 / D`.

This sprint connects that finite algebraic package to the existing interval
Selberg interfaces from TS30/TS99.  It proves that the TS135 optimal
reconstructed weights satisfy the raw TS99 support and normalization fields.
The actual interval majorant, sieve theorem, and budget comparison remain the
explicit TS30 obligations.
-/

/-- The optimal original Selberg weight reconstructed from the TS128 vector. -/
def selbergOptimalIntervalWeight
    (level : Nat) :
    Nat -> Rat :=
  TS130.Goldbach.optimalReconstructedSelbergWeight level

/-- The optimal reconstructed weights are supported inside `level`. -/
theorem selbergOptimalIntervalWeight_support_bound
    (level : Nat) :
    forall d : Nat,
      ((selbergOptimalIntervalWeight level d = 0) -> False) ->
        d <= level := by
  intro d hd
  exact
    TS130.Goldbach.reconstructedSelbergWeight_support_bound
      level
      (TS128.Goldbach.selbergOptimalDiagonalVector level)
      d
      hd

/--
For positive level, the reconstructed optimal Selberg weight is normalized at
`1`.

The point is that the reconstruction formula at `m = 1` is exactly the Mobius
linear constraint of the TS128 optimal diagonal vector.
-/
theorem selbergOptimalIntervalWeight_one
    (level : Nat)
    (hlevel : 0 < level) :
    selbergOptimalIntervalWeight level 1 = 1 := by
  unfold selbergOptimalIntervalWeight
  unfold TS130.Goldbach.optimalReconstructedSelbergWeight
  unfold TS130.Goldbach.reconstructedSelbergWeight
  unfold TS130.Goldbach.absorbedCoefficientFromDiagonalVector
  simp [TS130.Goldbach.selbergReconstructionSupport]
  simpa [TS122.Goldbach.selbergMobiusLinearForm] using
    TS128.Goldbach.selbergOptimalDiagonalVector_linear_constraint
      level
      hlevel

/-- TS99 Selberg weight ledger supplied by the TS135 optimal weights. -/
def selbergOptimalSieveWeightLedger
    (level : Nat)
    (hlevel : 0 < level) :
    TS99.Goldbach.SelbergSieveWeightLedger where
  level := level
  weight := selbergOptimalIntervalWeight level
  support_bound :=
    selbergOptimalIntervalWeight_support_bound level
  weight_one :=
    selbergOptimalIntervalWeight_one level hlevel
  finite_support_ready := True.intro
  quadratic_form_ready := True.intro
  divisor_sum_majorant_ready := True.intro

/-- Exact dense-side budget for the TS136 optimal interval weights. -/
theorem selbergOptimalIntervalWeight_dense_budget_exact
    (level : Nat)
    (hlevel : 0 < level) :
    TS110.Goldbach.selbergDenseSide
        level
        (selbergOptimalIntervalWeight level) =
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  exact
    TS135.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget
      level
      hlevel

/--
Package connecting the exact TS135 diagonal budget to a concrete interval
majorant supplied through the TS30 interface.

The fields `majorant`, `sieve`, and `budget` are the remaining interval-level
Selberg/Brun-Titchmarsh inputs.  Everything finite about the optimal weights
and diagonal budget is supplied here.
-/
structure SelbergIntervalMajorantFromOptimalBudget
    (level : Nat) where
  hlevel :
    0 < level

  majorant :
    TS30.Goldbach.SelbergIntervalMajorant

  sieve :
    TS30.Goldbach.SelbergSieveIntervalBound majorant

  budget :
    TS30.Goldbach.SelbergMajorantBudgetComparison majorant

  weightLedger :
    TS99.Goldbach.SelbergSieveWeightLedger

  weight_ledger_eq :
    weightLedger =
      selbergOptimalSieveWeightLedger level hlevel

  finite_reconstruction :
    TS135.Goldbach.SelbergFiniteMobiusReconstructionExpansionDischarge level

  dense_budget_exact :
    TS110.Goldbach.selbergDenseSide
        level
        (selbergOptimalIntervalWeight level) =
      1 / TS122.Goldbach.selbergOptimizationDenominator level

  diagonalBudgetPackage :
    TS129.Goldbach.SelbergSieveMajorantFromDiagonalBudget
      level
      (selbergOptimalIntervalWeight level)

  weightInfrastructure :
    TS99.Goldbach.SelbergSieveWeightInfrastructure

  diagonal_budget_to_interval_majorant_ready :
    True

  brun_titchmarsh_ready_from_interval_obligations :
    True

/-- Concrete TS136 bridge once the TS30 interval objects are supplied. -/
noncomputable def selbergIntervalMajorantFromOptimalBudget
    (level : Nat)
    (hlevel : 0 < level)
    (majorant : TS30.Goldbach.SelbergIntervalMajorant)
    (sieve : TS30.Goldbach.SelbergSieveIntervalBound majorant)
    (budget : TS30.Goldbach.SelbergMajorantBudgetComparison majorant) :
    SelbergIntervalMajorantFromOptimalBudget level where
  hlevel := hlevel
  majorant := majorant
  sieve := sieve
  budget := budget
  weightLedger :=
    selbergOptimalSieveWeightLedger level hlevel
  weight_ledger_eq := rfl
  finite_reconstruction :=
    TS135.Goldbach.selbergFiniteMobiusReconstructionExpansionDischarge level
  dense_budget_exact :=
    selbergOptimalIntervalWeight_dense_budget_exact level hlevel
  diagonalBudgetPackage := {
    diagonalBudget :=
      TS129.Goldbach.selbergDiagonalBudgetMajorant
        level
        (selbergOptimalIntervalWeight level)
    weightLedger :=
      selbergOptimalSieveWeightLedger level hlevel
    majorant := majorant
    sieve := sieve
    budget := budget
    diagonal_budget_to_interval_majorant_ready := True.intro
  }
  weightInfrastructure :=
    TS129.Goldbach.selbergSieveWeightInfrastructure_of_diagonalBudget
      {
        diagonalBudget :=
          TS129.Goldbach.selbergDiagonalBudgetMajorant
            level
            (selbergOptimalIntervalWeight level)
        weightLedger :=
          selbergOptimalSieveWeightLedger level hlevel
        majorant := majorant
        sieve := sieve
        budget := budget
        diagonal_budget_to_interval_majorant_ready := True.intro
      }
  diagonal_budget_to_interval_majorant_ready := True.intro
  brun_titchmarsh_ready_from_interval_obligations := True.intro

/-- A TS136 package supplies the TS99 Selberg weight infrastructure. -/
def selbergSieveWeightInfrastructure_of_intervalMajorant
    {level : Nat}
    (H : SelbergIntervalMajorantFromOptimalBudget level) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure :=
  H.weightInfrastructure

/-- A TS136 package supplies the TS97 final Brun-Titchmarsh input ledger. -/
noncomputable def brunTitchmarshFinalInputLedger_of_intervalMajorant
    {level : Nat}
    (H : SelbergIntervalMajorantFromOptimalBudget level) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger :=
  TS99.Goldbach.brunTitchmarshFinalInputLedger_of_weightInfrastructure
    H.weightInfrastructure

/--
Bridge target: if the interval majorant, sieve bound, and budget comparison are
provided for a positive level, then the TS136 package is populated.
-/
def SelbergIntervalMajorantFromOptimalBudgetBridgeTarget : Prop :=
  forall level : Nat,
    0 < level ->
      forall majorant : TS30.Goldbach.SelbergIntervalMajorant,
        TS30.Goldbach.SelbergSieveIntervalBound majorant ->
          TS30.Goldbach.SelbergMajorantBudgetComparison majorant ->
            Nonempty (SelbergIntervalMajorantFromOptimalBudget level)

/-- The TS136 bridge target is populated. -/
theorem selbergIntervalMajorantFromOptimalBudgetBridgeTarget :
    SelbergIntervalMajorantFromOptimalBudgetBridgeTarget := by
  intro level hlevel majorant sieve budget
  exact
    Nonempty.intro
      (selbergIntervalMajorantFromOptimalBudget
        level
        hlevel
        majorant
        sieve
        budget)

/-- Target proposition for a fully supplied TS136 interval-majorant package. -/
def SelbergIntervalMajorantFromOptimalBudgetTarget : Prop :=
  Nonempty (Sigma fun level : Nat =>
    SelbergIntervalMajorantFromOptimalBudget level)

/-- A fully supplied TS136 package feeds the TS99 infrastructure target. -/
theorem selbergSieveWeightInfrastructureTarget_of_intervalMajorantTarget
    (H : SelbergIntervalMajorantFromOptimalBudgetTarget) :
    TS99.Goldbach.SelbergSieveWeightInfrastructureTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level package =>
          exact
            Nonempty.intro
              (selbergSieveWeightInfrastructure_of_intervalMajorant package)

/-- A fully supplied TS136 package feeds the TS97 final Brun-Titchmarsh target. -/
theorem brunTitchmarshFinalInputLedgerTarget_of_intervalMajorantTarget
    (H : SelbergIntervalMajorantFromOptimalBudgetTarget) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level package =>
          exact
            Nonempty.intro
              (brunTitchmarshFinalInputLedger_of_intervalMajorant
                (level := level)
                package)

/-- TS136 keeps the TS135 target available. -/
theorem selbergFiniteMobiusReconstructionExpansionDischargeTarget :
    TS135.Goldbach.SelbergFiniteMobiusReconstructionExpansionDischargeTarget :=
  TS135.Goldbach.selbergFiniteMobiusReconstructionExpansionDischargeTarget

end Goldbach
end TS136
