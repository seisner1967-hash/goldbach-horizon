import Mathlib.Tactic
import TS.Goldbach.Strong.TS157.GoldbachScaleEventualObstruction

namespace TS158
namespace Goldbach

set_option maxRecDepth 10000

/-!
# TS158 - Selberg/Brun-Titchmarsh Obstruction Closure Ledger

TS153--TS157 prove that the current refined Selberg budget comparison cannot
hold throughout the Goldbach tail.

This sprint packages that verdict as a terminal ledger. It does not refactor
the denominator, change the TS22 budget, or claim a general impossibility for
all Selberg sieve formulations. The affected route is precisely the TS150
comparison using the current TS122 Jordan-two denominator.
-/

/-- The precise high-level route ruled out by the TS153--TS157 obstruction. -/
inductive SelbergBTObstructionRoute where
  | refinedSelbergBudgetToTS22
  deriving DecidableEq, Repr

/-- Named formal causes recorded by the closure ledger. -/
inductive SelbergBTObstructionCause where
  | jordanTwoDenominatorBoundedByTwo
  | thresholdGeometryForcesOppositeInequality
  | goldbachScaleEventuallyTriggersThreshold
  deriving DecidableEq, Repr

/-- Terminal theorem: the TS150 dependent comparison fails beyond `2^3000`. -/
theorem no_TS150_dependent_BT_comparison_eventually
    (level : TS151.Goldbach.SelbergLevelSelection)
    {x : Nat}
    (hx : TS157.Goldbach.goldbachObstructionThreshold <= x) :
    Not (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) := by
  exact
    TS157.Goldbach.no_dependentRefinedComparison_of_goldbachObstructionThreshold_le
      level hx

/-- The Goldbach-scale TS156 obstruction regime holds throughout the tail. -/
theorem goldbach_obstruction_regime_eventually
    {x : Nat}
    (hx : TS157.Goldbach.goldbachObstructionThreshold <= x) :
    TS156.Goldbach.GoldbachThresholdObstructionRegime x := by
  exact TS157.Goldbach.goldbachThresholdObstructionRegime_of_threshold_le hx

/-- The TS155 geometric obstruction also holds throughout the tail. -/
theorem geometric_obstruction_eventually
    {x : Nat}
    (hx : TS157.Goldbach.goldbachObstructionThreshold <= x) :
    TS155.Goldbach.SelbergBTGeometricObstruction
      x
      (TS156.Goldbach.goldbachScaleQ x) := by
  exact TS157.Goldbach.geometricObstruction_of_goldbachObstructionThreshold_le hx

/-- The denominator cap that causes the obstruction remains available here. -/
theorem jordanTwo_denominator_le_two
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationDenominator level <= 2 := by
  exact TS154.Goldbach.selbergOptimizationDenominator_le_two level

/-- Strict denominator cap at positive levels. -/
theorem jordanTwo_denominator_lt_two_of_pos
    (level : Nat)
    (hlevel : 0 < level) :
    TS122.Goldbach.selbergOptimizationDenominator level < 2 := by
  exact TS154.Goldbach.selbergOptimizationDenominator_lt_two level hlevel

/--
Closure package for the current Selberg/BT obstruction.

The ledger records:
* the explicit threshold `2^3000`;
* the affected route, namely the TS150 refined Selberg budget comparison;
* the three named causes proved in TS154--TS157;
* the terminal impossibility theorem on the Goldbach tail.
-/
structure SelbergBTObstructionClosure where
  threshold : Nat

  threshold_eq :
    threshold = TS157.Goldbach.goldbachObstructionThreshold

  affected_route :
    SelbergBTObstructionRoute

  route_eq :
    affected_route =
      SelbergBTObstructionRoute.refinedSelbergBudgetToTS22

  denominator_cause :
    SelbergBTObstructionCause

  denominator_cause_eq :
    denominator_cause =
      SelbergBTObstructionCause.jordanTwoDenominatorBoundedByTwo

  geometry_cause :
    SelbergBTObstructionCause

  geometry_cause_eq :
    geometry_cause =
      SelbergBTObstructionCause.thresholdGeometryForcesOppositeInequality

  scale_cause :
    SelbergBTObstructionCause

  scale_cause_eq :
    scale_cause =
      SelbergBTObstructionCause.goldbachScaleEventuallyTriggersThreshold

  denominator_le_two :
    forall level : Nat,
      TS122.Goldbach.selbergOptimizationDenominator level <= 2

  obstruction_regime :
    forall x : Nat,
      threshold <= x ->
        TS156.Goldbach.GoldbachThresholdObstructionRegime x

  geometric_obstruction :
    forall x : Nat,
      threshold <= x ->
        TS155.Goldbach.SelbergBTGeometricObstruction
          x
          (TS156.Goldbach.goldbachScaleQ x)

  no_dependent_comparison :
    forall level : TS151.Goldbach.SelbergLevelSelection,
      forall x : Nat,
        threshold <= x ->
          Not
            (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level)

  scope_is_current_TS150_route :
    True

  denominator_or_budget_refactor_obligation :
    True

  cumulative_head_prime_count_obligation :
    True

/-- Concrete TS158 obstruction-closure package. -/
def selbergBTObstructionClosure : SelbergBTObstructionClosure where
  threshold := TS157.Goldbach.goldbachObstructionThreshold
  threshold_eq := rfl
  affected_route :=
    SelbergBTObstructionRoute.refinedSelbergBudgetToTS22
  route_eq := rfl
  denominator_cause :=
    SelbergBTObstructionCause.jordanTwoDenominatorBoundedByTwo
  denominator_cause_eq := rfl
  geometry_cause :=
    SelbergBTObstructionCause.thresholdGeometryForcesOppositeInequality
  geometry_cause_eq := rfl
  scale_cause :=
    SelbergBTObstructionCause.goldbachScaleEventuallyTriggersThreshold
  scale_cause_eq := rfl
  denominator_le_two := jordanTwo_denominator_le_two
  obstruction_regime := by
    intro x hx
    exact goldbach_obstruction_regime_eventually hx
  geometric_obstruction := by
    intro x hx
    exact geometric_obstruction_eventually hx
  no_dependent_comparison := by
    intro level x hx
    exact no_TS150_dependent_BT_comparison_eventually level hx
  scope_is_current_TS150_route := True.intro
  denominator_or_budget_refactor_obligation := True.intro
  cumulative_head_prime_count_obligation := True.intro

/-- Target proposition for the TS158 closure ledger. -/
def SelbergBTObstructionClosureTarget : Prop :=
  Nonempty SelbergBTObstructionClosure

/-- The TS158 obstruction closure target is populated. -/
theorem selbergBTObstructionClosureTarget :
    SelbergBTObstructionClosureTarget :=
  Nonempty.intro selbergBTObstructionClosure

end Goldbach
end TS158
