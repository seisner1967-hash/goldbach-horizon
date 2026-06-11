import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS145.EulerTotientDiagonalizationJordanDomination

namespace TS146
namespace Goldbach

/-!
# TS146 - Weighted LCM Error Aggregation

TS143 bounds every local lcm multiplicity error by one, while TS145 bounds
the fractional main term by the optimized Selberg budget.  This sprint
aggregates the local errors over the finite TS122 support.

The resulting global error is bounded by the square of the finite `L1` norm
of the reconstructed Selberg weights.  Estimating that norm, estimating the
optimization denominator, and comparing the combined bound with the final
Brun-Titchmarsh budget remain separate analytic tasks.
-/

/-- Finite `L1` norm of the reconstructed optimal interval weights. -/
def selbergConcreteLambdaL1Rat
    (level : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
    abs (TS142.Goldbach.selbergConcreteLambda level d)

/-- Pairwise absolute budget arising from the local error estimate. -/
def selbergWeightedLCMErrorPairBudgetRat
    (level : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
      abs (TS142.Goldbach.selbergConcreteLambda level d1) *
        abs (TS142.Goldbach.selbergConcreteLambda level d2)

/-- The pairwise absolute budget factors as the square of the finite `L1` norm. -/
theorem selbergWeightedLCMErrorPairBudget_eq_l1_sq
    (level : Nat) :
    selbergWeightedLCMErrorPairBudgetRat level =
      (selbergConcreteLambdaL1Rat level) ^ 2 := by
  unfold selbergWeightedLCMErrorPairBudgetRat
  unfold selbergConcreteLambdaL1Rat
  rw [pow_two, Finset.sum_mul_sum]

/-- One summand of the weighted fractional error. -/
def weightedLCMLocalErrorTerm
    (level x Q n d1 d2 : Nat) : Rat :=
  TS142.Goldbach.selbergConcreteLambda level d1 *
    TS142.Goldbach.selbergConcreteLambda level d2 *
      TS142.Goldbach.lcmMultiplicityErrorRat x Q n d1 d2

/-- Absolute product of the two reconstructed weights. -/
def selbergLambdaAbsPair
    (level d1 d2 : Nat) : Rat :=
  abs (TS142.Goldbach.selbergConcreteLambda level d1) *
    abs (TS142.Goldbach.selbergConcreteLambda level d2)

/-- Pointwise weighted error proposition on the finite support. -/
def WeightedLCMLocalErrorBound
    (level x Q n d1 d2 : Nat) : Prop :=
  abs (weightedLCMLocalErrorTerm level x Q n d1 d2) <=
    selbergLambdaAbsPair level d1 d2

set_option maxHeartbeats 4000000 in
/-- One weighted local error is bounded by the corresponding absolute weight product. -/
theorem weightedLCMLocalError_abs_le
    (level x Q n d1 d2 : Nat)
    (hd1 : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d1)
    (hd2 : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d2) :
    WeightedLCMLocalErrorBound level x Q n d1 d2 := by
  have hd1pos : 0 < d1 :=
    TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hd1
  have hd2pos : 0 < d2 :=
    TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hd2
  have hlcm : 0 < Nat.lcm d1 d2 := Nat.lcm_pos hd1pos hd2pos
  have herror :=
    TS143.Goldbach.lcmMultiplicityErrorRat_abs_le_one x Q n d1 d2 hlcm
  unfold WeightedLCMLocalErrorBound
  unfold weightedLCMLocalErrorTerm
  unfold selbergLambdaAbsPair
  rw [abs_mul, abs_mul]
  have hweights_nonneg :
      0 <=
        abs (TS142.Goldbach.selbergConcreteLambda level d1) *
          abs (TS142.Goldbach.selbergConcreteLambda level d2) :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left herror hweights_nonneg
  simpa using hmul

/-- The global fractional error is bounded by the pairwise absolute budget. -/
theorem selbergFractionalErrorTerm_abs_le_pairBudget
    (level x Q n : Nat) :
    abs (TS142.Goldbach.selbergFractionalErrorTermRat level x Q n) <=
      selbergWeightedLCMErrorPairBudgetRat level := by
  unfold TS142.Goldbach.selbergFractionalErrorTermRat
  unfold selbergWeightedLCMErrorPairBudgetRat
  calc
    abs
        (Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
          Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
            weightedLCMLocalErrorTerm level x Q n d1 d2) <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
          abs
            (Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
              weightedLCMLocalErrorTerm level x Q n d1 d2) := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
          Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
            abs
              (weightedLCMLocalErrorTerm level x Q n d1 d2) := by
      apply Finset.sum_le_sum
      intro d1 _hd1
      exact Finset.abs_sum_le_sum_abs _ _
    _ <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
          Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
            selbergLambdaAbsPair level d1 d2 := by
      apply Finset.sum_le_sum
      intro d1 hd1
      apply Finset.sum_le_sum
      intro d2 hd2
      exact weightedLCMLocalError_abs_le level x Q n d1 d2 hd1 hd2

/-- Final finite aggregation: the global error is bounded by the squared `L1` norm. -/
theorem selbergFractionalErrorTerm_abs_le_l1_sq
    (level x Q n : Nat) :
    abs (TS142.Goldbach.selbergFractionalErrorTermRat level x Q n) <=
      (selbergConcreteLambdaL1Rat level) ^ 2 := by
  calc
    abs (TS142.Goldbach.selbergFractionalErrorTermRat level x Q n) <=
        selbergWeightedLCMErrorPairBudgetRat level :=
      selbergFractionalErrorTerm_abs_le_pairBudget level x Q n
    _ = (selbergConcreteLambdaL1Rat level) ^ 2 :=
      selbergWeightedLCMErrorPairBudget_eq_l1_sq level

/--
The complete rational square majorant is bounded by its optimized main term
plus the squared finite `L1` norm of the reconstructed weights.
-/
theorem selbergConcreteSquareMajorantRat_le_mainBudget_add_l1_sq
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        (selbergConcreteLambdaL1Rat level) ^ 2 := by
  rw [TS142.Goldbach.selbergConcreteSquareMajorantRat_eq_fractionalExpansion]
  unfold TS142.Goldbach.selbergFractionalExpansionRat
  exact add_le_add
    (TS145.Goldbach.selbergFractionalMainTerm_le_optimalBudget level x Q hlevel)
    (le_trans (le_abs_self _)
      (selbergFractionalErrorTerm_abs_le_l1_sq level x Q n))

/-- TS146 package for the finite weighted aggregation step. -/
structure WeightedLCMErrorAggregation
    (level x Q n : Nat) where
  hlevel :
    0 < level

  local_error_bound :
    TS142.Goldbach.LCMMultiplicityErrorBound x Q n

  global_error_pair_bound :
    abs (TS142.Goldbach.selbergFractionalErrorTermRat level x Q n) <=
      selbergWeightedLCMErrorPairBudgetRat level

  pair_budget_factorization :
    selbergWeightedLCMErrorPairBudgetRat level =
      (selbergConcreteLambdaL1Rat level) ^ 2

  global_error_l1_bound :
    abs (TS142.Goldbach.selbergFractionalErrorTermRat level x Q n) <=
      (selbergConcreteLambdaL1Rat level) ^ 2

  square_majorant_upper_budget :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        (selbergConcreteLambdaL1Rat level) ^ 2

  l1_norm_estimate_obligation :
    True

  denominator_estimate_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Construct the unconditional finite TS146 aggregation package. -/
def weightedLCMErrorAggregation
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    WeightedLCMErrorAggregation level x Q n where
  hlevel := hlevel
  local_error_bound := TS143.Goldbach.lcmMultiplicityErrorBound x Q n
  global_error_pair_bound :=
    selbergFractionalErrorTerm_abs_le_pairBudget level x Q n
  pair_budget_factorization :=
    selbergWeightedLCMErrorPairBudget_eq_l1_sq level
  global_error_l1_bound :=
    selbergFractionalErrorTerm_abs_le_l1_sq level x Q n
  square_majorant_upper_budget :=
    selbergConcreteSquareMajorantRat_le_mainBudget_add_l1_sq
      level x Q n hlevel
  l1_norm_estimate_obligation := True.intro
  denominator_estimate_obligation := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Target proposition for the unconditional finite TS146 step. -/
def WeightedLCMErrorAggregationTarget : Prop :=
  forall level x Q n : Nat,
    0 < level -> Nonempty (WeightedLCMErrorAggregation level x Q n)

/-- The TS146 target is populated for every positive level. -/
theorem weightedLCMErrorAggregationTarget :
    WeightedLCMErrorAggregationTarget := by
  intro level x Q n hlevel
  exact Nonempty.intro (weightedLCMErrorAggregation level x Q n hlevel)

end Goldbach
end TS146
