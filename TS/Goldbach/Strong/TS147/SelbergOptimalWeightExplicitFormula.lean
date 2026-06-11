import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS146.WeightedLCMErrorAggregation

namespace TS147
namespace Goldbach

/-!
# TS147 - Selberg Optimal Weight Explicit Formula

TS146 reduces the global interval error to the finite `L1` norm of the
reconstructed optimal Selberg weights. This sprint unfolds those weights back
to the TS128 optimal diagonal vector and proves a finite explicit envelope.

The outcome is deliberately non-asymptotic. It exposes the exact Mobius
reconstruction formula, removes the Mobius coefficient by `|mu| <= 1`, and
reindexes the resulting `L1` envelope by divisors. Estimating that explicit
divisor envelope is left to the next arithmetic sprint.
-/

/-- The upward Mobius sum occurring in the reconstructed optimal weight. -/
def selbergOptimalWeightMobiusSum
    (level m : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
    if Dvd.dvd m d then
      TS122.Goldbach.selbergMobiusRatCoefficient (d / m) *
        TS128.Goldbach.selbergOptimalDiagonalVector level d
    else
      0

/-- Explicit reconstructed-weight formula written under a TS147 name. -/
def selbergOptimalWeightExplicitRat
    (level m : Nat) : Rat :=
  (m : Rat) * selbergOptimalWeightMobiusSum level m

/-- The concrete TS142 coefficient is exactly the reconstructed Mobius formula. -/
theorem selbergConcreteLambda_eq_explicit
    (level m : Nat) :
    TS142.Goldbach.selbergConcreteLambda level m =
      selbergOptimalWeightExplicitRat level m := by
  rfl

/-- The rational Mobius coefficient has absolute value at most one. -/
theorem abs_selbergMobiusRatCoefficient_le_one
    (d : Nat) :
    abs (TS122.Goldbach.selbergMobiusRatCoefficient d) <= 1 := by
  have hInt :
      abs (ArithmeticFunction.moebius d) <= (1 : Int) :=
    ArithmeticFunction.abs_moebius_le_one
  unfold TS122.Goldbach.selbergMobiusRatCoefficient
  rw [ArithmeticFunction.intCoe_apply]
  exact_mod_cast hInt

/-- Pointwise envelope after removing the Mobius coefficient by `|mu| <= 1`. -/
def selbergOptimalWeightDiagonalEnvelopeRat
    (level m : Nat) : Rat :=
  (m : Rat) *
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
      if Dvd.dvd m d then
        abs (TS128.Goldbach.selbergOptimalDiagonalVector level d)
      else
        0

/-- One summand of the Mobius reconstruction is bounded by `|Y_d|`. -/
theorem abs_mobius_mul_optimalVector_le
    (level m d : Nat) :
    abs
        (TS122.Goldbach.selbergMobiusRatCoefficient (d / m) *
          TS128.Goldbach.selbergOptimalDiagonalVector level d) <=
      abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) := by
  rw [abs_mul]
  have hmu := abs_selbergMobiusRatCoefficient_le_one (d / m)
  have hy : 0 <= abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) :=
    abs_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hmu hy
  simpa using hmul

/-- The absolute reconstructed weight is bounded by the diagonal envelope. -/
theorem abs_selbergConcreteLambda_le_diagonalEnvelope
    (level m : Nat) :
    abs (TS142.Goldbach.selbergConcreteLambda level m) <=
      selbergOptimalWeightDiagonalEnvelopeRat level m := by
  rw [selbergConcreteLambda_eq_explicit]
  unfold selbergOptimalWeightExplicitRat
  unfold selbergOptimalWeightMobiusSum
  unfold selbergOptimalWeightDiagonalEnvelopeRat
  rw [abs_mul]
  rw [abs_of_nonneg (by positivity : (0 : Rat) <= (m : Rat))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    abs
        (Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
          if Dvd.dvd m d then
            TS122.Goldbach.selbergMobiusRatCoefficient (d / m) *
              TS128.Goldbach.selbergOptimalDiagonalVector level d
          else
            0) <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
          abs
            (if Dvd.dvd m d then
              TS122.Goldbach.selbergMobiusRatCoefficient (d / m) *
                TS128.Goldbach.selbergOptimalDiagonalVector level d
            else
              0) := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
          if Dvd.dvd m d then
            abs (TS128.Goldbach.selbergOptimalDiagonalVector level d)
          else
            0 := by
      apply Finset.sum_le_sum
      intro d _hd
      by_cases hmd : Dvd.dvd m d
      case pos =>
        simp only [hmd, if_true]
        exact abs_mobius_mul_optimalVector_le level m d
      case neg =>
        simp [hmd]

/-- Finite explicit envelope for the TS146 `L1` norm. -/
def selbergOptimalWeightL1EnvelopeRat
    (level : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun m =>
    selbergOptimalWeightDiagonalEnvelopeRat level m

/-- TS146's finite `L1` norm is bounded by the explicit diagonal envelope. -/
theorem selbergConcreteLambdaL1_le_explicitEnvelope
    (level : Nat) :
    TS146.Goldbach.selbergConcreteLambdaL1Rat level <=
      selbergOptimalWeightL1EnvelopeRat level := by
  unfold TS146.Goldbach.selbergConcreteLambdaL1Rat
  unfold selbergOptimalWeightL1EnvelopeRat
  apply Finset.sum_le_sum
  intro m _hm
  exact abs_selbergConcreteLambda_le_diagonalEnvelope level m

/-- Sum of supported divisors weighted by their natural size. -/
def selbergSupportedDivisorMassRat
    (level d : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun m =>
    if Dvd.dvd m d then (m : Rat) else 0

/-- Divisor-first form of the explicit `L1` envelope. -/
def selbergOptimalWeightDivisorEnvelopeRat
    (level : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
    abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) *
      selbergSupportedDivisorMassRat level d

/-- Finite Fubini reindexing of the explicit `L1` envelope. -/
theorem selbergOptimalWeightL1Envelope_eq_divisorEnvelope
    (level : Nat) :
    selbergOptimalWeightL1EnvelopeRat level =
      selbergOptimalWeightDivisorEnvelopeRat level := by
  unfold selbergOptimalWeightL1EnvelopeRat
  unfold selbergOptimalWeightDiagonalEnvelopeRat
  unfold selbergOptimalWeightDivisorEnvelopeRat
  unfold selbergSupportedDivisorMassRat
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hmd : Dvd.dvd m d
  case pos =>
    simp [hmd]
    ring
  case neg =>
    simp [hmd]

/-- Direct divisor-first upper bound for the TS146 `L1` norm. -/
theorem selbergConcreteLambdaL1_le_divisorEnvelope
    (level : Nat) :
    TS146.Goldbach.selbergConcreteLambdaL1Rat level <=
      selbergOptimalWeightDivisorEnvelopeRat level := by
  rw [<- selbergOptimalWeightL1Envelope_eq_divisorEnvelope]
  exact selbergConcreteLambdaL1_le_explicitEnvelope level

/--
The TS146 square majorant can use the explicit divisor envelope in place of
the still opaque `L1` norm.
-/
theorem selbergConcreteSquareMajorantRat_le_mainBudget_add_divisorEnvelope_sq
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        (selbergOptimalWeightDivisorEnvelopeRat level) ^ 2 := by
  have hL1 := selbergConcreteLambdaL1_le_divisorEnvelope level
  have hL1_nonneg :
      0 <= TS146.Goldbach.selbergConcreteLambdaL1Rat level := by
    unfold TS146.Goldbach.selbergConcreteLambdaL1Rat
    positivity
  have hEnvelope_nonneg :
      0 <= selbergOptimalWeightDivisorEnvelopeRat level := by
    rw [<- selbergOptimalWeightL1Envelope_eq_divisorEnvelope]
    unfold selbergOptimalWeightL1EnvelopeRat
    unfold selbergOptimalWeightDiagonalEnvelopeRat
    positivity
  have hsq :
      (TS146.Goldbach.selbergConcreteLambdaL1Rat level) ^ 2 <=
        (selbergOptimalWeightDivisorEnvelopeRat level) ^ 2 := by
    nlinarith
  exact le_trans
    (TS146.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_l1_sq
      level x Q n hlevel)
    (add_le_add_left hsq _)

/-- TS147 package exposing the finite weight formula and divisor envelope. -/
structure SelbergOptimalWeightExplicitFormula
    (level x Q n : Nat) where
  hlevel :
    0 < level

  weight_formula :
    forall m : Nat,
      TS142.Goldbach.selbergConcreteLambda level m =
        selbergOptimalWeightExplicitRat level m

  pointwise_envelope :
    forall m : Nat,
      abs (TS142.Goldbach.selbergConcreteLambda level m) <=
        selbergOptimalWeightDiagonalEnvelopeRat level m

  l1_envelope :
    TS146.Goldbach.selbergConcreteLambdaL1Rat level <=
      selbergOptimalWeightDivisorEnvelopeRat level

  square_majorant_upper_budget :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        (selbergOptimalWeightDivisorEnvelopeRat level) ^ 2

  divisor_envelope_estimate_obligation :
    True

  denominator_estimate_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Construct the unconditional finite TS147 package. -/
def selbergOptimalWeightExplicitFormula
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    SelbergOptimalWeightExplicitFormula level x Q n where
  hlevel := hlevel
  weight_formula := by
    intro m
    exact selbergConcreteLambda_eq_explicit level m
  pointwise_envelope := by
    intro m
    exact abs_selbergConcreteLambda_le_diagonalEnvelope level m
  l1_envelope := selbergConcreteLambdaL1_le_divisorEnvelope level
  square_majorant_upper_budget :=
    selbergConcreteSquareMajorantRat_le_mainBudget_add_divisorEnvelope_sq
      level x Q n hlevel
  divisor_envelope_estimate_obligation := True.intro
  denominator_estimate_obligation := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Target proposition for the unconditional finite TS147 step. -/
def SelbergOptimalWeightExplicitFormulaTarget : Prop :=
  forall level x Q n : Nat,
    0 < level -> Nonempty (SelbergOptimalWeightExplicitFormula level x Q n)

/-- The TS147 target is populated for every positive level. -/
theorem selbergOptimalWeightExplicitFormulaTarget :
    SelbergOptimalWeightExplicitFormulaTarget := by
  intro level x Q n hlevel
  exact Nonempty.intro
    (selbergOptimalWeightExplicitFormula level x Q n hlevel)

end Goldbach
end TS147
