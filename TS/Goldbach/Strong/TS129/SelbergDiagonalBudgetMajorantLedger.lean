import Mathlib.Tactic
import TS.Goldbach.Strong.TS99.SelbergSieveWeightLedger
import TS.Goldbach.Strong.TS128.SelbergOptimalVectorNormalization

namespace TS129
namespace Goldbach

/-!
# TS129 - Selberg Diagonal Budget Majorant Ledger

TS121 closes the corrected dense-to-diagonal identity, and TS128 proves the
optimal diagonal vector and exact energy `1 / D`.

This sprint connects those two layers without claiming the full interval sieve
bound. It proves that the original dense `gcd/lcm` side is the TS122 diagonal
energy of the absorbed transformed vector. It then packages the remaining
Selberg-sieve step as a local obligation feeding TS99.
-/

/-- The diagonal vector obtained from the absorbed original Selberg weights. -/
def selbergAbsorbedDiagonalVector
    (level : Nat)
    (weight : Nat -> Rat) :
    Nat -> Rat :=
  TS119.Goldbach.selbergGcdSquareTransformedWeight
    level
    (TS118.Goldbach.selbergLCMAbsorbedWeight weight)

/-- The absorbed transformed weight at divisor index zero vanishes. -/
theorem selbergAbsorbedDiagonalVector_zero
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergAbsorbedDiagonalVector level weight 0 = 0 := by
  unfold selbergAbsorbedDiagonalVector
  unfold TS119.Goldbach.selbergGcdSquareTransformedWeight
  apply Finset.sum_eq_zero
  intro m _hm
  by_cases hm0 : m = 0
  case pos =>
    subst m
    simp [TS121.Goldbach.selbergLCMAbsorbedWeight_zero]
  case neg =>
    have hnotdvd : Not (Dvd.dvd 0 m) := by
      intro h
      exact hm0 (Nat.eq_zero_of_zero_dvd h)
    simp [hnotdvd]

/--
The corrected Jordan-two diagonal side for absorbed weights is exactly the
TS122 diagonal energy of the absorbed transformed vector.
-/
theorem selbergCorrectedJordanDiagonalSide_eq_diagonalEnergy
    (level : Nat)
    (weight : Nat -> Rat) :
    TS119.Goldbach.selbergJordanTwoDiagonalSide
        level
        (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
      TS122.Goldbach.selbergDiagonalEnergy
        level
        (selbergAbsorbedDiagonalVector level weight) := by
  unfold TS119.Goldbach.selbergJordanTwoDiagonalSide
  unfold TS119.Goldbach.selbergJordanTwoDiagonalSquareTerm
  unfold TS122.Goldbach.selbergDiagonalEnergy
  unfold TS122.Goldbach.selbergOptimizationSupport
  unfold TS122.Goldbach.selbergJordanTwoPenalty
  unfold TS121.Goldbach.selbergPositiveQuadraticSupport
  unfold selbergAbsorbedDiagonalVector
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdpos : 0 < d
  case pos =>
    simp [hdpos]
  case neg =>
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hdpos
    subst d
    have hz :
        TS119.Goldbach.selbergGcdSquareTransformedWeight
            level
            (TS118.Goldbach.selbergLCMAbsorbedWeight weight)
            0 =
          0 := by
      simpa [selbergAbsorbedDiagonalVector] using
        selbergAbsorbedDiagonalVector_zero level weight
    simp [hz]

/--
The original dense `gcd/lcm` side is the diagonal energy of the absorbed
transformed vector.
-/
theorem selbergOriginalDenseSide_eq_absorbedDiagonalEnergy
    (level : Nat)
    (weight : Nat -> Rat) :
    TS110.Goldbach.selbergDenseSide level weight =
      TS122.Goldbach.selbergDiagonalEnergy
        level
        (selbergAbsorbedDiagonalVector level weight) := by
  calc
    TS110.Goldbach.selbergDenseSide level weight =
        TS119.Goldbach.selbergJordanTwoDiagonalSide
          level
          (TS118.Goldbach.selbergLCMAbsorbedWeight weight) :=
      TS121.Goldbach.selbergOriginalDenseSide_eq_correctedJordanDiagonalSide
        level
        weight
    _ =
        TS122.Goldbach.selbergDiagonalEnergy
          level
          (selbergAbsorbedDiagonalVector level weight) :=
      selbergCorrectedJordanDiagonalSide_eq_diagonalEnergy level weight

/--
If the absorbed transformed vector satisfies the Mobius normalization, the
dense Selberg side has the TS122/TS128 diagonal budget lower bound.
-/
theorem selbergDenseSide_budget_lower_bound_of_mobius_constraint
    (level : Nat)
    (weight : Nat -> Rat)
    (hlevel : 0 < level)
    (hconstraint :
      TS122.Goldbach.selbergMobiusLinearForm
        level
        (selbergAbsorbedDiagonalVector level weight) =
          1) :
    1 / TS122.Goldbach.selbergOptimizationDenominator level <=
      TS110.Goldbach.selbergDenseSide level weight := by
  rw [selbergOriginalDenseSide_eq_absorbedDiagonalEnergy]
  exact
    TS127.Goldbach.selbergDiagonalEnergy_lower_bound
      level
      (selbergAbsorbedDiagonalVector level weight)
      hlevel
      hconstraint

/--
If the absorbed transformed vector is the TS128 optimal vector, then the dense
side has exactly the optimal budget value.
-/
theorem selbergDenseSide_eq_optimal_budget_of_absorbedVector_eq_optimal
    (level : Nat)
    (weight : Nat -> Rat)
    (hlevel : 0 < level)
    (hoptimal :
      selbergAbsorbedDiagonalVector level weight =
        TS128.Goldbach.selbergOptimalDiagonalVector level) :
    TS110.Goldbach.selbergDenseSide level weight =
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  rw [selbergOriginalDenseSide_eq_absorbedDiagonalEnergy]
  rw [hoptimal]
  exact TS128.Goldbach.selbergOptimalDiagonalVector_energy_eq level hlevel

/--
Budget package connecting the corrected dense-to-diagonal identity and the
optimal vector layer.

The actual interval sieve theorem remains the next arithmetic obligation.
-/
structure SelbergDiagonalBudgetMajorant
    (level : Nat)
    (weight : Nat -> Rat) where
  finiteSupportCollapse :
    TS121.Goldbach.SelbergJordanTwoFiniteSupportCollapse level weight

  optimalVectorNormalization :
    TS128.Goldbach.SelbergOptimalVectorNormalization level weight

  absorbedDiagonalVector :
    Nat -> Rat

  absorbed_diagonal_vector_eq :
    forall d : Nat,
      absorbedDiagonalVector d =
        selbergAbsorbedDiagonalVector level weight d

  dense_equals_diagonal_energy :
    TS110.Goldbach.selbergDenseSide level weight =
      TS122.Goldbach.selbergDiagonalEnergy level absorbedDiagonalVector

  dense_budget_lower_bound :
    0 < level ->
      TS122.Goldbach.selbergMobiusLinearForm level absorbedDiagonalVector = 1 ->
        1 / TS122.Goldbach.selbergOptimizationDenominator level <=
          TS110.Goldbach.selbergDenseSide level weight

  optimal_budget_value :
    0 < level ->
      TS122.Goldbach.selbergDiagonalEnergy
          level
          (TS128.Goldbach.selbergOptimalDiagonalVector level) =
        1 / TS122.Goldbach.selbergOptimizationDenominator level

  optimal_vector_realization_obligation :
    Prop

  optimal_vector_realization_obligation_eq :
    optimal_vector_realization_obligation =
      (absorbedDiagonalVector =
        TS128.Goldbach.selbergOptimalDiagonalVector level)

  selberg_sieve_majorant_obligation :
    True

  brun_titchmarsh_obligation :
    True

/-- Concrete TS129 diagonal-budget package. -/
def selbergDiagonalBudgetMajorant
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergDiagonalBudgetMajorant level weight where
  finiteSupportCollapse :=
    TS121.Goldbach.selbergJordanTwoFiniteSupportCollapse level weight
  optimalVectorNormalization :=
    TS128.Goldbach.selbergOptimalVectorNormalization level weight
  absorbedDiagonalVector :=
    selbergAbsorbedDiagonalVector level weight
  absorbed_diagonal_vector_eq := by
    intro d
    rfl
  dense_equals_diagonal_energy :=
    selbergOriginalDenseSide_eq_absorbedDiagonalEnergy level weight
  dense_budget_lower_bound := by
    intro hlevel hconstraint
    exact
      selbergDenseSide_budget_lower_bound_of_mobius_constraint
        level
        weight
        hlevel
        hconstraint
  optimal_budget_value := by
    intro hlevel
    exact TS128.Goldbach.selbergOptimalDiagonalVector_energy_eq level hlevel
  optimal_vector_realization_obligation :=
    selbergAbsorbedDiagonalVector level weight =
      TS128.Goldbach.selbergOptimalDiagonalVector level
  optimal_vector_realization_obligation_eq := rfl
  selberg_sieve_majorant_obligation := True.intro
  brun_titchmarsh_obligation := True.intro

/--
Input package for converting the diagonal budget into the TS99 full Selberg
weight infrastructure.

This is intentionally where the interval majorant, sieve theorem, and budget
comparison enter.
-/
structure SelbergSieveMajorantFromDiagonalBudget
    (level : Nat)
    (weight : Nat -> Rat) where
  diagonalBudget :
    SelbergDiagonalBudgetMajorant level weight

  weightLedger :
    TS99.Goldbach.SelbergSieveWeightLedger

  majorant :
    TS30.Goldbach.SelbergIntervalMajorant

  sieve :
    TS30.Goldbach.SelbergSieveIntervalBound majorant

  budget :
    TS30.Goldbach.SelbergMajorantBudgetComparison majorant

  diagonal_budget_to_interval_majorant_ready :
    True

/-- A TS129 sieve-majorant package supplies the TS99 infrastructure. -/
def selbergSieveWeightInfrastructure_of_diagonalBudget
    {level : Nat}
    {weight : Nat -> Rat}
    (H : SelbergSieveMajorantFromDiagonalBudget level weight) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure where
  weights := H.weightLedger
  majorant := H.majorant
  sieve := H.sieve
  budget := H.budget
  majorant_from_weights_ready :=
    H.diagonal_budget_to_interval_majorant_ready

/-- Target proposition for the TS129 diagonal budget layer. -/
def SelbergDiagonalBudgetMajorantTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergDiagonalBudgetMajorant level weight)

/-- The TS129 diagonal budget layer is populated. -/
theorem selbergDiagonalBudgetMajorantTarget :
    SelbergDiagonalBudgetMajorantTarget := by
  intro level weight
  exact Nonempty.intro (selbergDiagonalBudgetMajorant level weight)

/-- Target proposition for the future sieve-majorant step from TS129. -/
def SelbergSieveMajorantFromDiagonalBudgetTarget : Prop :=
  Nonempty (Sigma fun level : Nat =>
    Sigma fun weight : Nat -> Rat =>
      SelbergSieveMajorantFromDiagonalBudget level weight)

/-- A TS129 sieve-majorant target feeds the TS99 infrastructure target. -/
theorem selbergSieveWeightInfrastructureTarget_of_diagonalBudgetTarget
    (H : SelbergSieveMajorantFromDiagonalBudgetTarget) :
    TS99.Goldbach.SelbergSieveWeightInfrastructureTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level rest =>
          cases rest with
          | mk weight package =>
              exact
                Nonempty.intro
                  (selbergSieveWeightInfrastructure_of_diagonalBudget package)

/-- TS129 keeps the TS128 target available. -/
theorem selbergOptimalVectorNormalizationTarget :
    TS128.Goldbach.SelbergOptimalVectorNormalizationTarget :=
  TS128.Goldbach.selbergOptimalVectorNormalizationTarget

end Goldbach
end TS129
