import Mathlib.Tactic
import TS.Goldbach.Strong.TS154.SelbergDenominatorUpperBoundObstructionProbe

namespace TS155
namespace Goldbach

/-!
# TS155 - Brun-Titchmarsh Threshold Obstruction Geometry

TS154 proves that the TS122 Selberg denominator is strictly below `2` at
every positive level. TS153 shows that any successful refined Selberg/BT
comparison forces the exact rational threshold

`(intervalScale x Q + 1) / brunTitchmarshCeilBudget x Q`

below that denominator.

This sprint rewrites the threshold obstruction in natural-number geometry.
Once the BT ceiling is positive, the threshold is at least `2` exactly when

`2 * brunTitchmarshCeilBudget x Q <= intervalScale x Q + 1`.

Consequently every successful dependent comparison requires the strict
opposite inequality. The result is finite and ceiling-aware; no asymptotic
formula for the TS22 budget is used.
-/

/-- The exact rational obstruction detected by TS153 and TS154. -/
def SelbergBTThresholdObstructed (x Q : Nat) : Prop :=
  (2 : Rat) <=
    TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat x Q

/-- Natural-number form of the obstruction, including the required positive ceiling. -/
def SelbergBTGeometricObstruction (x Q : Nat) : Prop :=
  0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q /\
    2 * TS22.Goldbach.brunTitchmarshCeilBudget x Q <=
      TS15.Goldbach.intervalScale x Q + 1

/-- Strict natural-number feasibility region forced by a successful comparison. -/
def SelbergBTGeometricFeasibility (x Q : Nat) : Prop :=
  TS15.Goldbach.intervalScale x Q + 1 <
    2 * TS22.Goldbach.brunTitchmarshCeilBudget x Q

/-- A threshold obstruction forces the BT natural ceiling to be positive. -/
theorem brunTitchmarshCeilBudget_pos_of_thresholdObstructed
    (x Q : Nat)
    (hob : SelbergBTThresholdObstructed x Q) :
    0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q := by
  unfold SelbergBTThresholdObstructed at hob
  unfold TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat at hob
  by_contra hpos
  have hzero : TS22.Goldbach.brunTitchmarshCeilBudget x Q = 0 :=
    Nat.eq_zero_of_not_pos hpos
  simp [hzero] at hob
  norm_num at hob

/-- Rational threshold obstruction implies the natural geometric inequality. -/
theorem geometricObstruction_of_thresholdObstructed
    (x Q : Nat)
    (hob : SelbergBTThresholdObstructed x Q) :
    SelbergBTGeometricObstruction x Q := by
  have hbudgetNat : 0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q :=
    brunTitchmarshCeilBudget_pos_of_thresholdObstructed x Q hob
  have hbudgetRat :
      (0 : Rat) < (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
    exact_mod_cast hbudgetNat
  unfold SelbergBTThresholdObstructed at hob
  unfold TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat at hob
  have hrat := mul_le_mul_of_nonneg_right hob hbudgetRat.le
  field_simp [hbudgetRat.ne'] at hrat
  refine And.intro hbudgetNat ?_
  exact_mod_cast hrat

/-- The positive natural geometric inequality reconstructs the rational obstruction. -/
theorem thresholdObstructed_of_geometricObstruction
    (x Q : Nat)
    (hob : SelbergBTGeometricObstruction x Q) :
    SelbergBTThresholdObstructed x Q := by
  have hbudgetRat :
      (0 : Rat) < (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
    exact_mod_cast hob.1
  unfold SelbergBTThresholdObstructed
  unfold TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat
  have hrat :
      (2 : Rat) * (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) <=
        (TS15.Goldbach.intervalScale x Q + 1 : Nat) := by
    exact_mod_cast hob.2
  calc
    (2 : Rat) =
        ((2 : Rat) * (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat)) /
          (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
      field_simp [hbudgetRat.ne']
    _ <=
        ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) /
          (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) :=
      div_le_div_of_nonneg_right hrat hbudgetRat.le

/-- Exact equivalence between the TS153 threshold and its natural geometry. -/
theorem thresholdObstructed_iff_geometricObstruction
    (x Q : Nat) :
    SelbergBTThresholdObstructed x Q <->
      SelbergBTGeometricObstruction x Q := by
  constructor
  case mp => exact geometricObstruction_of_thresholdObstructed x Q
  case mpr => exact thresholdObstructed_of_geometricObstruction x Q

/--
Every successful dependent comparison lies in the strict geometric feasibility
region. This is the ceiling-aware necessary condition promised by TS154.
-/
theorem dependentRefinedComparison_forces_geometricFeasibility
    (level : TS151.Goldbach.SelbergLevelSelection)
    (scale :
      TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level)
    (x Q : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x) :
    SelbergBTGeometricFeasibility x Q := by
  have hlevel : 0 < level x Q := scale.level_positive x Q hx hQ
  have hscale := scale.refined_budget_le_brun_titchmarsh x Q hx hQ
  have hbudgetNat : 0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q :=
    TS153.Goldbach.brunTitchmarshCeilBudget_pos_of_refinedComparison
      (level x Q) x Q hlevel hscale
  have hbudgetRat :
      (0 : Rat) < (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Rat) := by
    exact_mod_cast hbudgetNat
  have hthreshold :
      TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat x Q < 2 :=
    TS154.Goldbach.dependentRefinedComparison_forces_threshold_lt_two
      level scale x Q hx hQ
  unfold TS153.Goldbach.necessarySelbergDenominatorLowerBoundRat at hthreshold
  have hrat := mul_lt_mul_of_pos_right hthreshold hbudgetRat
  field_simp [hbudgetRat.ne'] at hrat
  unfold SelbergBTGeometricFeasibility
  exact_mod_cast hrat

/-- The geometric obstruction rules out every dependent Selberg level selection. -/
theorem no_dependentRefinedComparison_of_geometricObstruction
    (level : TS151.Goldbach.SelbergLevelSelection)
    (x Q : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x)
    (hob : SelbergBTGeometricObstruction x Q) :
    Not (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) := by
  intro scale
  have hfeasible :=
    dependentRefinedComparison_forces_geometricFeasibility
      level scale x Q hx hQ
  exact (not_lt_of_ge hob.2) hfeasible

/--
The raw natural inequality is enough to contradict any successful comparison:
the latter supplies positivity of the BT ceiling automatically.
-/
theorem no_dependentRefinedComparison_of_twice_budget_le_interval
    (level : TS151.Goldbach.SelbergLevelSelection)
    (x Q : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x)
    (hob :
      2 * TS22.Goldbach.brunTitchmarshCeilBudget x Q <=
        TS15.Goldbach.intervalScale x Q + 1) :
    Not (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) := by
  intro scale
  have hfeasible :=
    dependentRefinedComparison_forces_geometricFeasibility
      level scale x Q hx hQ
  exact (not_lt_of_ge hob) hfeasible

/-- TS155 package exposing the exact threshold geometry and obstruction. -/
structure BrunTitchmarshThresholdObstructionGeometry where
  threshold_geometry :
    forall x Q : Nat,
      SelbergBTThresholdObstructed x Q <->
        SelbergBTGeometricObstruction x Q

  successful_comparison_feasible :
    forall level : TS151.Goldbach.SelbergLevelSelection,
      TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level ->
        forall x Q : Nat,
          TS15.Goldbach.LargeX x ->
            Q = Nat.log 2 x * Nat.log 2 x ->
              SelbergBTGeometricFeasibility x Q

  denominator_or_budget_refactor_obligation :
    True

  cumulative_head_prime_count_obligation :
    True

/-- Concrete TS155 geometry package. -/
def brunTitchmarshThresholdObstructionGeometry :
    BrunTitchmarshThresholdObstructionGeometry where
  threshold_geometry := thresholdObstructed_iff_geometricObstruction
  successful_comparison_feasible := by
    intro level scale x Q hx hQ
    exact dependentRefinedComparison_forces_geometricFeasibility
      level scale x Q hx hQ
  denominator_or_budget_refactor_obligation := True.intro
  cumulative_head_prime_count_obligation := True.intro

/-- Target proposition for the TS155 obstruction geometry sprint. -/
def BrunTitchmarshThresholdObstructionGeometryTarget : Prop :=
  Nonempty BrunTitchmarshThresholdObstructionGeometry

/-- The TS155 target is populated without external assumptions. -/
theorem brunTitchmarshThresholdObstructionGeometryTarget :
    BrunTitchmarshThresholdObstructionGeometryTarget :=
  Nonempty.intro brunTitchmarshThresholdObstructionGeometry

end Goldbach
end TS155
