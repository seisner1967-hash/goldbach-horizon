import Mathlib.Tactic
import TS.Goldbach.Strong.TS158.SelbergBTObstructionClosureLedger

namespace TS159
namespace Goldbach

/-!
# TS159 - Selberg Denominator Refactor Interface

TS158 closes the current Selberg/Brun-Titchmarsh route: the TS150 refined
comparison fails throughout the Goldbach tail for the current TS122 Jordan-two
denominator.

This sprint does not change that old route. It defines a forward-compatible
interface for any replacement denominator and records the exact diagnostic
showing why the legacy Jordan-two denominator cannot implement a growth
requirement that reaches `2` on the positive-level regime.
-/

/-- The minimal positive-level regime in which a replacement denominator is
expected to have a lower bound. -/
def SelbergDenominatorGrowthRegime (level : Nat) : Prop :=
  0 < level

/--
Abstract data for a denominator that can replace the current TS122 denominator.

The `requiredGrowth` field is deliberately supplied as data: future sprints can
choose a logarithmic, threshold, or scale-dependent lower-bound curve without
changing the interface.
-/
structure SelbergGrowingDenominatorData where
  denominator : Nat -> Rat
  requiredGrowth : Nat -> Rat
  positive :
    forall level : Nat, 0 < level -> 0 < denominator level
  lower_bound :
    forall level : Nat, SelbergDenominatorGrowthRegime level ->
      requiredGrowth level <= denominator level

/--
The refactored Selberg/BT route.  This is an interface only: a future
implementation must supply a denominator and prove that the refined Selberg
budget built from it fits below the TS22 ceiling.
-/
structure RefactoredSelbergBTComparisonRoute where
  data : SelbergGrowingDenominatorData
  refined_budget :
    forall level x Q : Nat,
      0 < level ->
        Nat.ceil
          ((((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) /
              data.denominator level) +
            (((level : Rat) / data.denominator level) ^ (2 : Nat))) <=
          TS22.Goldbach.brunTitchmarshCeilBudget x Q

/--
Predicate stating that a concrete denominator realizes a growth interface with
the supplied required-growth curve.
-/
def SelbergGrowingDenominatorDataSatisfiedBy
    (den : Nat -> Rat)
    (reqGrowth : Nat -> Rat) : Prop :=
  Nonempty
    (Subtype fun data : SelbergGrowingDenominatorData =>
      data.denominator = den /\ data.requiredGrowth = reqGrowth)

/--
The legacy TS122 Jordan-two denominator cannot satisfy any replacement
interface whose required-growth curve is at least `2` at every positive level.

The proof instantiates the interface at `level = 1`: the interface would give
`2 <= D(1)`, while TS154 proves `D(1) < 2`.
-/
theorem current_jordanTwo_denominator_not_growing
    (reqGrowth : Nat -> Rat)
    (h_req :
      forall level : Nat,
        SelbergDenominatorGrowthRegime level -> 2 <= reqGrowth level) :
    Not
      (SelbergGrowingDenominatorDataSatisfiedBy
        TS122.Goldbach.selbergOptimizationDenominator
        reqGrowth) := by
  intro hsat
  cases hsat with
  | intro hsub =>
      cases hsub with
      | mk data hprops =>
          cases hprops with
          | intro hden hgrowth =>
              have hreg : SelbergDenominatorGrowthRegime 1 := by
                exact Nat.zero_lt_one
              have hreq_ge_two : (2 : Rat) <= reqGrowth 1 := h_req 1 hreg
              have hreq_le_data : reqGrowth 1 <= data.denominator 1 := by
                have h := data.lower_bound 1 hreg
                simpa [hgrowth] using h
              have hdata_ge_two : (2 : Rat) <= data.denominator 1 :=
                le_trans hreq_ge_two hreq_le_data
              have hlegacy_ge_two :
                  (2 : Rat) <= TS122.Goldbach.selbergOptimizationDenominator 1 := by
                simpa [hden] using hdata_ge_two
              have hlegacy_lt_two :
                  TS122.Goldbach.selbergOptimizationDenominator 1 < (2 : Rat) :=
                TS154.Goldbach.selbergOptimizationDenominator_lt_two
                  1 Nat.zero_lt_one
              linarith

/-- Named status for the TS159 refactor interface. -/
inductive SelbergDenominatorRefactorStatus where
  | legacyJordanTwoRouteClosed
  | replacementInterfaceOpen
  deriving DecidableEq, Repr

/--
Closure-and-refactor package: it carries the TS158 obstruction closure and the
new denominator interface diagnostic in one object.
-/
structure SelbergDenominatorRefactorInterfaceLedger where
  obstruction_closure :
    TS158.Goldbach.SelbergBTObstructionClosure

  status :
    SelbergDenominatorRefactorStatus

  status_eq :
    status =
      SelbergDenominatorRefactorStatus.replacementInterfaceOpen

  legacy_route_closed :
    forall level : TS151.Goldbach.SelbergLevelSelection,
      forall x : Nat,
        TS157.Goldbach.goldbachObstructionThreshold <= x ->
          Not
            (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level)

  legacy_denominator_not_growing :
    forall reqGrowth : Nat -> Rat,
      (forall level : Nat,
        SelbergDenominatorGrowthRegime level -> 2 <= reqGrowth level) ->
        Not
          (SelbergGrowingDenominatorDataSatisfiedBy
            TS122.Goldbach.selbergOptimizationDenominator
            reqGrowth)

  replacement_route_type_available :
    True

  no_claim_about_all_selberg_sieves :
    True

/-- Concrete TS159 refactor-interface ledger. -/
def selbergDenominatorRefactorInterfaceLedger :
    SelbergDenominatorRefactorInterfaceLedger where
  obstruction_closure := TS158.Goldbach.selbergBTObstructionClosure
  status :=
    SelbergDenominatorRefactorStatus.replacementInterfaceOpen
  status_eq := rfl
  legacy_route_closed := by
    intro level x hx
    exact
      TS158.Goldbach.no_TS150_dependent_BT_comparison_eventually
        level hx
  legacy_denominator_not_growing := by
    intro reqGrowth h_req
    exact current_jordanTwo_denominator_not_growing reqGrowth h_req
  replacement_route_type_available := True.intro
  no_claim_about_all_selberg_sieves := True.intro

/-- Target proposition for TS159. -/
def SelbergDenominatorRefactorInterfaceTarget : Prop :=
  Nonempty SelbergDenominatorRefactorInterfaceLedger

/-- The TS159 refactor-interface target is populated. -/
theorem selbergDenominatorRefactorInterfaceTarget :
    SelbergDenominatorRefactorInterfaceTarget :=
  Nonempty.intro selbergDenominatorRefactorInterfaceLedger

end Goldbach
end TS159
