import Mathlib.Tactic
import TS.Goldbach.Strong.TS152.FiniteHeadPrimeIntervalBudgetReduction

namespace TS153
namespace Goldbach

/-!
# TS153 - Dependent Selberg Budget Feasibility Probe

TS151 leaves a dependent comparison between the refined Selberg ceiling and
the TS22 Brun-Titchmarsh ceiling.  This sprint extracts exact necessary
conditions from that comparison.

No asymptotic estimate is asserted.  In particular, the sprint does not
replace either ceiling by a logarithmic approximation and does not claim that
the TS122 denominator grows.
-/

/-- Principal rational contribution to the refined TS150 budget. -/
def refinedSelbergMainTermRat
    (level x Q : Nat) :
    Rat :=
  ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
    (1 / TS122.Goldbach.selbergOptimizationDenominator level)

/-- Quadratic error contribution to the refined TS150 budget. -/
def refinedSelbergErrorTermRat
    (level : Nat) :
    Rat :=
  ((level : Rat) /
    TS122.Goldbach.selbergOptimizationDenominator level) ^ 2

/-- TS150 is definitionally the sum of its principal and error terms. -/
theorem refinedSelbergBudgetRat_eq_main_add_error
    (level x Q : Nat) :
    TS150.Goldbach.refinedSelbergBudgetRat level x Q =
      refinedSelbergMainTermRat level x Q +
        refinedSelbergErrorTermRat level := by
  rfl

/-- The refined rational budget lies below its own natural ceiling. -/
theorem refinedSelbergBudgetRat_le_ceil_cast
    (level x Q : Nat) :
    TS150.Goldbach.refinedSelbergBudgetRat level x Q <=
      (TS150.Goldbach.refinedSelbergBudgetCeil level x Q : Rat) := by
  have hreal :
      (TS150.Goldbach.refinedSelbergBudgetRat level x Q : Real) <=
        (TS150.Goldbach.refinedSelbergBudgetCeil level x Q : Real) := by
    unfold TS150.Goldbach.refinedSelbergBudgetCeil
    exact Nat.le_ceil _
  exact_mod_cast hreal

/-- A TS150 scale comparison bounds the full rational budget by the BT ceil. -/
theorem refinedSelbergBudgetRat_le_brunTitchmarshCeil_cast
    (level x Q : Nat)
    (hscale :
      TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    TS150.Goldbach.refinedSelbergBudgetRat level x Q <=
      (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
  exact le_trans
    (refinedSelbergBudgetRat_le_ceil_cast level x Q)
    (by exact_mod_cast hscale)

/-- The quadratic error term is always nonnegative. -/
theorem refinedSelbergErrorTermRat_nonneg
    (level : Nat) :
    0 <= refinedSelbergErrorTermRat level := by
  unfold refinedSelbergErrorTermRat
  exact sq_nonneg _

/-- The principal term is bounded by the complete refined budget. -/
theorem refinedSelbergMainTermRat_le_refinedBudget
    (level x Q : Nat) :
    refinedSelbergMainTermRat level x Q <=
      TS150.Goldbach.refinedSelbergBudgetRat level x Q := by
  rw [refinedSelbergBudgetRat_eq_main_add_error]
  exact le_add_of_nonneg_right
    (refinedSelbergErrorTermRat_nonneg level)

/--
The principal term alone must fit below the Brun-Titchmarsh ceiling.
-/
theorem refinedSelbergMainTermRat_le_brunTitchmarshCeil_cast
    (level x Q : Nat)
    (hscale :
      TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    refinedSelbergMainTermRat level x Q <=
      (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
  exact le_trans
    (refinedSelbergMainTermRat_le_refinedBudget level x Q)
    (refinedSelbergBudgetRat_le_brunTitchmarshCeil_cast
      level x Q hscale)

/--
The quadratic error term alone must also fit below the Brun-Titchmarsh ceil.
-/
theorem refinedSelbergErrorTermRat_le_brunTitchmarshCeil_cast
    (level x Q : Nat)
    (hlevel : 0 < level)
    (hscale :
      TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    refinedSelbergErrorTermRat level <=
      (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
  have hDpos :
      0 < TS122.Goldbach.selbergOptimizationDenominator level :=
    TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hmain_nonneg :
      0 <= refinedSelbergMainTermRat level x Q := by
    unfold refinedSelbergMainTermRat
    positivity
  exact le_trans
    (le_add_of_nonneg_left hmain_nonneg)
    (by
      rw [<- refinedSelbergBudgetRat_eq_main_add_error]
      exact refinedSelbergBudgetRat_le_brunTitchmarshCeil_cast
        level x Q hscale)

/-- Exact denominator threshold forced by the principal term and the BT ceil. -/
noncomputable def necessarySelbergDenominatorLowerBoundRat
    (x Q : Nat) :
    Rat :=
  ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) /
    (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat)

/-- Under a valid comparison, the BT ceiling is necessarily positive. -/
theorem brunTitchmarshCeilBudget_pos_of_refinedComparison
    (level x Q : Nat)
    (hlevel : 0 < level)
    (hscale :
      TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q := by
  have hDpos :
      0 < TS122.Goldbach.selbergOptimizationDenominator level :=
    TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hmain_pos :
      0 < refinedSelbergMainTermRat level x Q := by
    unfold refinedSelbergMainTermRat
    positivity
  have hbudget_rat_pos :
      (0 : Rat) <
        (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) :=
    lt_of_lt_of_le hmain_pos
      (refinedSelbergMainTermRat_le_brunTitchmarshCeil_cast
        level x Q hscale)
  exact_mod_cast hbudget_rat_pos

/--
Exact necessary lower bound on `D(level)` imposed by the TS150 comparison.

This is the ceiling-aware replacement for informal statements such as
`D(level) >= log(Q+1)/4`.
-/
theorem necessarySelbergDenominatorLowerBoundRat_le_denominator
    (level x Q : Nat)
    (hlevel : 0 < level)
    (hscale :
      TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    necessarySelbergDenominatorLowerBoundRat x Q <=
      TS122.Goldbach.selbergOptimizationDenominator level := by
  have hDpos :
      0 < TS122.Goldbach.selbergOptimizationDenominator level :=
    TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hbudget_nat_pos :
      0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q :=
    brunTitchmarshCeilBudget_pos_of_refinedComparison
      level x Q hlevel hscale
  have hbudget_rat_pos :
      (0 : Rat) <
        (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
    exact_mod_cast hbudget_nat_pos
  have hmain :=
    refinedSelbergMainTermRat_le_brunTitchmarshCeil_cast
      level x Q hscale
  unfold refinedSelbergMainTermRat at hmain
  unfold necessarySelbergDenominatorLowerBoundRat
  have hscaled := (mul_le_mul_left hDpos).2 hmain
  field_simp [hDpos.ne'] at hscaled
  have hmul :=
    mul_le_mul_of_nonneg_right hscaled (le_of_lt (inv_pos.mpr hbudget_rat_pos))
  simpa [div_eq_mul_inv, mul_assoc, hbudget_rat_pos.ne'] using hmul

/-- Dependent feasibility requirements extracted from a TS151 scale package. -/
structure DependentSelbergBudgetNecessaryConditions
    (level : TS151.Goldbach.SelbergLevelSelection) where
  denominator_requirement :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
        necessarySelbergDenominatorLowerBoundRat x Q <=
          TS122.Goldbach.selbergOptimizationDenominator (level x Q)

  error_requirement :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
        refinedSelbergErrorTermRat (level x Q) <=
          (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat)

  denominator_feasibility_obligation :
    True

/-- Any TS151 dependent scale comparison satisfies the TS153 requirements. -/
noncomputable def dependentSelbergBudgetNecessaryConditions
    (level : TS151.Goldbach.SelbergLevelSelection)
    (scale :
      TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) :
    DependentSelbergBudgetNecessaryConditions level where
  denominator_requirement := by
    intro x Q hx hQ
    exact
      necessarySelbergDenominatorLowerBoundRat_le_denominator
        (level x Q)
        x
        Q
        (scale.level_positive x Q hx hQ)
        (scale.refined_budget_le_brun_titchmarsh x Q hx hQ)
  error_requirement := by
    intro x Q hx hQ
    exact
      refinedSelbergErrorTermRat_le_brunTitchmarshCeil_cast
        (level x Q)
        x
        Q
        (scale.level_positive x Q hx hQ)
        (scale.refined_budget_le_brun_titchmarsh x Q hx hQ)
  denominator_feasibility_obligation :=
    scale.refined_budget_comparison_obligation

/-- TS153 ledger exposing the exact necessary conditions. -/
structure DependentSelbergBudgetFeasibilityLedger
    (level : TS151.Goldbach.SelbergLevelSelection) where
  scale :
    TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level

  necessaryConditions :
    DependentSelbergBudgetNecessaryConditions level

  necessary_conditions_eq :
    necessaryConditions =
      dependentSelbergBudgetNecessaryConditions level scale

  denominator_feasibility_obligation :
    True

  cumulative_head_prime_count_obligation :
    True

/-- Build the feasibility ledger from a supplied TS151 scale comparison. -/
noncomputable def dependentSelbergBudgetFeasibilityLedger
    (level : TS151.Goldbach.SelbergLevelSelection)
    (scale :
      TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) :
    DependentSelbergBudgetFeasibilityLedger level where
  scale := scale
  necessaryConditions :=
    dependentSelbergBudgetNecessaryConditions level scale
  necessary_conditions_eq := rfl
  denominator_feasibility_obligation :=
    scale.refined_budget_comparison_obligation
  cumulative_head_prime_count_obligation := True.intro

/-- Target recording the exact TS153 diagnostic extraction. -/
def DependentSelbergBudgetFeasibilityTarget : Prop :=
  forall level : TS151.Goldbach.SelbergLevelSelection,
    TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level ->
      Nonempty (DependentSelbergBudgetFeasibilityLedger level)

/-- The TS153 feasibility target is populated. -/
theorem dependentSelbergBudgetFeasibilityTarget :
    DependentSelbergBudgetFeasibilityTarget := by
  intro level scale
  exact Nonempty.intro
    (dependentSelbergBudgetFeasibilityLedger level scale)

end Goldbach
end TS153
