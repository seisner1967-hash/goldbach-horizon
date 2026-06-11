import Mathlib.Tactic
import TS.Goldbach.Strong.TS150.RefinedSelbergBudgetScaleInterface

namespace TS151
namespace Goldbach

/-!
# TS151 - Dependent Selberg Scale Split Interface

TS150 packages a fixed Selberg level and combines it with the TS140
large-prime admissibility structure.  The latter asks for `level < n` for
every left endpoint `n < x + 1`, including `n = 0`.  No positive fixed level
can satisfy that condition.

This sprint proves the obstruction, replaces the fixed level by a selection
depending on `(x,Q)`, and splits the interval theorem into two honest pieces:

* a finite-head bound for `n <= level x Q`;
* the TS140 large-prime argument for `level x Q < n`.

The split package constructs the exact TS22 natural-interval theorem and the
TS97 final arithmetic-input ledger.  No denominator-growth claim and no
specific level selection are introduced here.
-/

/-- The uniform TS140 admissibility package is impossible at every level. -/
theorem largePrimeAdmissibleIntervalSieveTheorem_uninhabited
    (level : Nat) :
    Not (Nonempty
      (TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem level)) := by
  intro H
  let package := Classical.choice H
  have hx : TS15.Goldbach.LargeX 16 := by
    norm_num [TS15.Goldbach.LargeX]
  have hlevel_lt_zero : level < 0 :=
    package.left_endpoint_large
      16
      (Nat.log 2 16 * Nat.log 2 16)
      0
      hx
      rfl
      (by norm_num)
  exact (Nat.not_lt_zero level) hlevel_lt_zero

/-- Consequently, the combined fixed-level TS150 ledger is uninhabited. -/
theorem refinedSelbergBudgetScaleLedger_uninhabited
    (level : Nat) :
    Not (Nonempty (TS150.Goldbach.RefinedSelbergBudgetScaleLedger level)) := by
  intro H
  let package := Classical.choice H
  exact
    largePrimeAdmissibleIntervalSieveTheorem_uninhabited level
      (Nonempty.intro package.admissibility)

/-- A sieve level may depend on the global parameters `(x,Q)`. -/
def SelbergLevelSelection := Nat -> Nat -> Nat

/--
Parametric TS150 budget comparison for a level selected separately at each
pair `(x,Q)`.
-/
structure DependentRefinedSelbergBudgetScaleComparison
    (level : SelbergLevelSelection) where
  level_positive :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
        0 < level x Q

  refined_budget_le_brun_titchmarsh :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
        TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh
          (level x Q) x Q

  level_selection_obligation :
    True

  refined_budget_comparison_obligation :
    True

/--
The finite-head input controls precisely the left endpoints not covered by
the large-prime argument.
-/
structure FiniteHeadPrimeIntervalBudget
    (level : SelbergLevelSelection) where
  head_bound :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      Membership.mem (Finset.range (x + 1)) n ->
      n <= level x Q ->
        TS22.Goldbach.primeIntervalCard n
            (TS15.Goldbach.intervalScale x Q) <=
          TS22.Goldbach.brunTitchmarshCeilBudget x Q

  finite_head_bound_obligation :
    True

/--
For a late window, TS140 admissibility and the selected TS150 budget close the
TS22 interval estimate directly.
-/
theorem primeIntervalCard_le_brunTitchmarshCeilBudget_of_dependentLevel
    (level : SelbergLevelSelection)
    (scale : DependentRefinedSelbergBudgetScaleComparison level)
    (x Q n : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x)
    (htail : level x Q < n) :
    TS22.Goldbach.primeIntervalCard n
        (TS15.Goldbach.intervalScale x Q) <=
      TS22.Goldbach.brunTitchmarshCeilBudget x Q := by
  exact le_trans
    (TS140.Goldbach.primeIntervalCard_le_concreteMajorantValue_of_level_lt_leftEndpoint
      (level x Q)
      x
      Q
      n
      (scale.level_positive x Q hx hQ)
      htail)
    (TS150.Goldbach.selbergConcreteMajorantValue_le_brunTitchmarshCeilBudget
      (level x Q)
      x
      Q
      n
      (scale.level_positive x Q hx hQ)
      (scale.refined_budget_le_brun_titchmarsh x Q hx hQ))

/--
The finite-head input and the dependent late-window estimate assemble the
exact natural-interval Brun-Titchmarsh object required by TS22.
-/
noncomputable def brunTitchmarshNatIntervalBound_of_dependentScaleSplit
    (level : SelbergLevelSelection)
    (scale : DependentRefinedSelbergBudgetScaleComparison level)
    (head : FiniteHeadPrimeIntervalBudget level) :
    TS22.Goldbach.BrunTitchmarshNatIntervalBound where
  interval_bound := by
    intro x Q n hx hQ hn
    by_cases htail : level x Q < n
    case pos =>
      exact
        primeIntervalCard_le_brunTitchmarshCeilBudget_of_dependentLevel
          level scale x Q n hx hQ htail
    case neg =>
      exact
        head.head_bound x Q n hx hQ hn (Nat.le_of_not_gt htail)

/-- The corrected split route populates the TS97 final arithmetic input. -/
noncomputable def brunTitchmarshFinalInputLedger_of_dependentScaleSplit
    (level : SelbergLevelSelection)
    (scale : DependentRefinedSelbergBudgetScaleComparison level)
    (head : FiniteHeadPrimeIntervalBudget level) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger where
  bt := brunTitchmarshNatIntervalBound_of_dependentScaleSplit level scale head

/-- TS151 ledger for the corrected dependent-level head/tail route. -/
structure DependentSelbergScaleSplitLedger
    (level : SelbergLevelSelection) where
  scale :
    DependentRefinedSelbergBudgetScaleComparison level

  finiteHead :
    FiniteHeadPrimeIntervalBudget level

  brunTitchmarshBound :
    TS22.Goldbach.BrunTitchmarshNatIntervalBound

  brun_titchmarsh_bound_eq :
    brunTitchmarshBound =
      brunTitchmarshNatIntervalBound_of_dependentScaleSplit
        level scale finiteHead

  finalInput :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger

  final_input_eq :
    finalInput =
      brunTitchmarshFinalInputLedger_of_dependentScaleSplit
        level scale finiteHead

  fixed_level_admissibility_obstruction_closed :
    True

  finite_head_bound_obligation :
    True

  dependent_budget_comparison_obligation :
    True

/-- Build the corrected TS151 ledger from the two remaining honest inputs. -/
noncomputable def dependentSelbergScaleSplitLedger
    (level : SelbergLevelSelection)
    (scale : DependentRefinedSelbergBudgetScaleComparison level)
    (head : FiniteHeadPrimeIntervalBudget level) :
    DependentSelbergScaleSplitLedger level where
  scale := scale
  finiteHead := head
  brunTitchmarshBound :=
    brunTitchmarshNatIntervalBound_of_dependentScaleSplit level scale head
  brun_titchmarsh_bound_eq := rfl
  finalInput :=
    brunTitchmarshFinalInputLedger_of_dependentScaleSplit level scale head
  final_input_eq := rfl
  fixed_level_admissibility_obstruction_closed := True.intro
  finite_head_bound_obligation := head.finite_head_bound_obligation
  dependent_budget_comparison_obligation :=
    scale.refined_budget_comparison_obligation

/-- Corrected TS151 bridge target. -/
def DependentSelbergScaleSplitBridgeTarget : Prop :=
  forall level : SelbergLevelSelection,
    DependentRefinedSelbergBudgetScaleComparison level ->
      FiniteHeadPrimeIntervalBudget level ->
        Nonempty (DependentSelbergScaleSplitLedger level)

/-- The corrected dependent-level bridge is populated. -/
theorem dependentSelbergScaleSplitBridgeTarget :
    DependentSelbergScaleSplitBridgeTarget := by
  intro level scale head
  exact Nonempty.intro
    (dependentSelbergScaleSplitLedger level scale head)

end Goldbach
end TS151
