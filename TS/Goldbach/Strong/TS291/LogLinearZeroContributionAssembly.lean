import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import TS.Goldbach.Strong.TS290.RiemannXiLogLinearZeroCounting

/-!
# TS291 - Log-Linear Zero-Contribution Assembly

TS290 supplies an unconditional global multiplicity count of order
`T * log (T + 2)`.  TS271--TS273 already transport every such count through
an exact finite Abel sum, but leave that amortized expression unevaluated.

This sprint closes the finite arithmetic estimate.  The shifted integer Abel
weights are dominated by a reciprocal-square sum, whose finite partial sums
are bounded by two.  Consequently the complete high residual mass is bounded
by a closed logarithmic envelope, and the real finite zero contribution is
bounded by the exact low mass plus an explicit `X * log X` high term.

No infinite zero sum, Riemann-von-Mangoldt asymptotic, explicit formula,
residual estimate, Gallagher estimate, OTSA bridge, or Goldbach statement is
proved.
-/

noncomputable section

namespace TS291
namespace Goldbach

open scoped BigOperators

/-- Finite reciprocal-square partial sums starting at one are at most two. -/
theorem reciprocalSquareRangeSum_le_two
    (K : Nat) :
    Finset.sum (Finset.range K)
        (fun n => 1 / (((n + 1 : Nat) : Real) ^ 2)) <= 2 := by
  have hStrong :
      forall N : Nat,
        Finset.sum (Finset.range N)
            (fun n => 1 / (((n + 1 : Nat) : Real) ^ 2)) <=
          2 - 2 / (((N + 1 : Nat) : Real)) := by
    intro N
    induction N with
    | zero =>
        norm_num
    | succ N hN =>
        rw [Finset.sum_range_succ]
        calc
          Finset.sum (Finset.range N)
                (fun n => 1 / (((n + 1 : Nat) : Real) ^ 2)) +
              1 / (((N + 1 : Nat) : Real) ^ 2) <=
              (2 - 2 / (((N + 1 : Nat) : Real))) +
                1 / (((N + 1 : Nat) : Real) ^ 2) := by
                  gcongr
          _ <= 2 - 2 / ((((N + 1) + 1 : Nat) : Real)) := by
            have hA : 0 < (((N + 1 : Nat) : Real)) := by positivity
            have hAOne : (1 : Real) <= (((N + 1 : Nat) : Real)) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
            have hCast :
                ((((N + 1) + 1 : Nat) : Real)) =
                  (((N + 1 : Nat) : Real)) + 1 := by
              norm_num
            rw [hCast]
            have hReciprocal :
                1 / (((N + 1 : Nat) : Real) ^ 2) <=
                  2 /
                    ((((N + 1 : Nat) : Real)) *
                      ((((N + 1 : Nat) : Real)) + 1)) := by
              have hDenominator :
                  (((N + 1 : Nat) : Real)) *
                        ((((N + 1 : Nat) : Real)) + 1) / 2 <=
                    (((N + 1 : Nat) : Real) ^ 2) := by
                nlinarith [sq_nonneg (((N + 1 : Nat) : Real))]
              have hInv := one_div_le_one_div_of_le
                (by positivity :
                  0 <
                    (((N + 1 : Nat) : Real)) *
                      ((((N + 1 : Nat) : Real)) + 1) / 2)
                hDenominator
              calc
                1 / (((N + 1 : Nat) : Real) ^ 2) <=
                    1 /
                      ((((N + 1 : Nat) : Real)) *
                        ((((N + 1 : Nat) : Real)) + 1) / 2) := hInv
                _ = 2 /
                    ((((N + 1 : Nat) : Real)) *
                      ((((N + 1 : Nat) : Real)) + 1)) := by
                      field_simp
            have hDifference :
                2 / (((N + 1 : Nat) : Real)) -
                    2 / ((((N + 1 : Nat) : Real)) + 1) =
                  2 /
                    ((((N + 1 : Nat) : Real)) *
                      ((((N + 1 : Nat) : Real)) + 1)) := by
              field_simp
              ring
            rw [hDifference.symm] at hReciprocal
            linarith
  have h := hStrong K
  have hNonnegative :
      0 <= 2 / (((K + 1 : Nat) : Real)) := by positivity
  linarith

/-- One shifted Abel coefficient, after multiplication by its height, is
bounded by twice the corresponding reciprocal square. -/
theorem shiftedIntegerAbelCoefficient_le
    (n : Nat) :
    (((n + 2 : Nat) : Real)) *
        (1 / (((n + 1 : Nat) : Real) ^ 2) -
          1 / (((n + 2 : Nat) : Real) ^ 2)) <=
      2 / (((n + 1 : Nat) : Real) ^ 2) := by
  have hA : 0 < (((n + 1 : Nat) : Real)) := by positivity
  have hCast :
      (((n + 2 : Nat) : Real)) = (((n + 1 : Nat) : Real)) + 1 := by
    push_cast
    ring
  rw [hCast]
  have hIdentity :
      ((((n + 1 : Nat) : Real)) + 1) *
          (1 / (((n + 1 : Nat) : Real) ^ 2) -
            1 / ((((n + 1 : Nat) : Real)) + 1) ^ 2) =
        (2 * (((n + 1 : Nat) : Real)) + 1) /
          ((((n + 1 : Nat) : Real)) ^ 2 *
            ((((n + 1 : Nat) : Real)) + 1)) := by
    field_simp
    ring
  rw [hIdentity]
  have hDifference :
      (2 * (((n + 1 : Nat) : Real)) + 1) /
          ((((n + 1 : Nat) : Real)) ^ 2 *
            ((((n + 1 : Nat) : Real)) + 1)) =
        2 / (((n + 1 : Nat) : Real) ^ 2) -
          1 /
            ((((n + 1 : Nat) : Real)) ^ 2 *
              ((((n + 1 : Nat) : Real)) + 1)) := by
    field_simp
    ring
  rw [hDifference]
  exact sub_le_self _ (by positivity)

/-- The safe log-linear envelope simplifies exactly at shifted integer
heights. -/
theorem logLinearEnvelope_shiftedIntegerHeight
    (C : Real)
    (n : Nat) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope C
        (TS272.Goldbach.shiftedIntegerHeight n) =
      C * (((n + 1 : Nat) : Real)) *
        Real.log ((((n + 1 : Nat) : Real)) + 2) := by
  have hOne :
      (1 : Real) <= TS272.Goldbach.shiftedIntegerHeight n := by
    unfold TS272.Goldbach.shiftedIntegerHeight
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [TS273.Goldbach.logLinearMultiplicityCountEnvelope, max_eq_left hOne]
  rfl

/-- Shifted reciprocal-square weights have their expected closed form. -/
theorem shiftedIntegerReciprocalSquareHeightWeight
    (n : Nat) :
    TS271.Goldbach.reciprocalSquareHeightWeight
        TS272.Goldbach.shiftedIntegerHeight n =
      1 / (((n + 1 : Nat) : Real) ^ 2) := by
  rfl

/-- Height times its reciprocal-square weight is at most one. -/
theorem shiftedIntegerHeight_mul_weight_le_one
    (n : Nat) :
    TS272.Goldbach.shiftedIntegerHeight n *
        TS271.Goldbach.reciprocalSquareHeightWeight
          TS272.Goldbach.shiftedIntegerHeight n <= 1 := by
  rw [shiftedIntegerReciprocalSquareHeightWeight]
  unfold TS272.Goldbach.shiftedIntegerHeight
  have hOne : (1 : Real) <= (((n + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hPos : 0 < (((n + 1 : Nat) : Real)) := lt_of_lt_of_le zero_lt_one hOne
  rw [show
      (((n + 1 : Nat) : Real)) *
          (1 / (((n + 1 : Nat) : Real) ^ 2)) =
        1 / (((n + 1 : Nat) : Real)) by
      field_simp
      ring]
  simpa using one_div_le_one_div_of_le zero_lt_one hOne

/-- Every summand in the shifted Abel sum is controlled by the common
truncation logarithm times a reciprocal square. -/
theorem logLinearShiftedAbelSummand_le
    (C : Real)
    (hC : 0 <= C)
    (X n : Nat)
    (hnLt : n < X - 1) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope C
          (TS272.Goldbach.shiftedIntegerHeight (n + 1)) *
        (TS271.Goldbach.reciprocalSquareHeightWeight
            TS272.Goldbach.shiftedIntegerHeight n -
          TS271.Goldbach.reciprocalSquareHeightWeight
            TS272.Goldbach.shiftedIntegerHeight (n + 1)) <=
      2 * C * Real.log ((X : Real) + 3) *
        (1 / (((n + 1 : Nat) : Real) ^ 2)) := by
  have hnUpper : n + 4 <= X + 3 := by omega
  have hLogPositive :
      0 <= Real.log ((((n + 2 : Nat) : Real)) + 2) := by
    apply Real.log_nonneg
    have hnNonnegative : 0 <= (n : Real) := Nat.cast_nonneg n
    push_cast
    linarith
  have hCommonLogPositive :
      0 <= Real.log ((X : Real) + 3) := by
    apply Real.log_nonneg
    have hXNonnegative : 0 <= (X : Real) := Nat.cast_nonneg X
    linarith
  have hLog :
      Real.log ((((n + 2 : Nat) : Real)) + 2) <=
        Real.log ((X : Real) + 3) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by
        change 0 < (((n + 2 : Nat) : Real)) + 2
        positivity)
      (by
        change 0 < (X : Real) + 3
        positivity)
      (by exact_mod_cast hnUpper)
  have hWeightDifference :
      0 <=
        TS271.Goldbach.reciprocalSquareHeightWeight
            TS272.Goldbach.shiftedIntegerHeight n -
          TS271.Goldbach.reciprocalSquareHeightWeight
            TS272.Goldbach.shiftedIntegerHeight (n + 1) := by
    exact sub_nonneg.mpr
      (TS271.Goldbach.reciprocalSquareHeightWeight_antitone
        TS272.Goldbach.shiftedIntegerHeight
        TS272.Goldbach.shiftedIntegerHeight_positiveMonotone
        (Nat.le_succ n))
  have hCoefficientNonnegative :
      0 <= (((n + 2 : Nat) : Real)) *
        (1 / (((n + 1 : Nat) : Real) ^ 2) -
          1 / (((n + 2 : Nat) : Real) ^ 2)) := by
    apply mul_nonneg (by positivity)
    rw [shiftedIntegerReciprocalSquareHeightWeight,
      shiftedIntegerReciprocalSquareHeightWeight] at hWeightDifference
    norm_num [Nat.cast_add, Nat.cast_one] at hWeightDifference
    ring_nf at hWeightDifference
    push_cast
    ring_nf
    exact sub_nonneg.mpr hWeightDifference
  rw [logLinearEnvelope_shiftedIntegerHeight,
    shiftedIntegerReciprocalSquareHeightWeight,
    shiftedIntegerReciprocalSquareHeightWeight]
  calc
    (C * (((n + 1 + 1 : Nat) : Real)) *
          Real.log ((((n + 1 + 1 : Nat) : Real)) + 2)) *
        (1 / (((n + 1 : Nat) : Real) ^ 2) -
          1 / (((n + 1 + 1 : Nat) : Real) ^ 2)) =
      (C * Real.log ((((n + 2 : Nat) : Real)) + 2)) *
        ((((n + 2 : Nat) : Real)) *
          (1 / (((n + 1 : Nat) : Real) ^ 2) -
            1 / (((n + 2 : Nat) : Real) ^ 2))) := by
        push_cast
        ring_nf
    _ <= (C * Real.log ((X : Real) + 3)) *
        (2 / (((n + 1 : Nat) : Real) ^ 2)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hLog hC)
        (shiftedIntegerAbelCoefficient_le n)
        hCoefficientNonnegative
        (mul_nonneg hC hCommonLogPositive)
    _ = 2 * C * Real.log ((X : Real) + 3) *
        (1 / (((n + 1 : Nat) : Real) ^ 2)) := by
      ring

/-- The terminal term in the finite Abel expression is controlled by one
copy of the common logarithmic budget. -/
theorem logLinearShiftedAbelTerminal_le
    (C : Real)
    (hC : 0 <= C)
    (X : Nat) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope C
          (TS272.Goldbach.shiftedIntegerHeight (X - 1)) *
        TS271.Goldbach.reciprocalSquareHeightWeight
          TS272.Goldbach.shiftedIntegerHeight (X - 1) <=
      C * Real.log ((X : Real) + 3) := by
  have hIndex : X - 1 + 1 + 2 <= X + 3 := by omega
  have hLog :
      Real.log (((((X - 1) + 1 : Nat) : Real)) + 2) <=
        Real.log ((X : Real) + 3) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by
        change 0 < (((((X - 1) + 1 : Nat) : Real)) + 2)
        positivity)
      (by
        change 0 < (X : Real) + 3
        positivity)
      (by exact_mod_cast hIndex)
  have hLogNonnegative :
      0 <= Real.log (((((X - 1) + 1 : Nat) : Real)) + 2) := by
    apply Real.log_nonneg
    have hIndexNonnegative : 0 <= (((X - 1 : Nat) : Real)) := by positivity
    push_cast
    linarith
  have hCommonLogNonnegative :
      0 <= Real.log ((X : Real) + 3) := by
    apply Real.log_nonneg
    have hXNonnegative : 0 <= (X : Real) := Nat.cast_nonneg X
    linarith
  rw [logLinearEnvelope_shiftedIntegerHeight]
  calc
    (C * ((((X - 1) + 1 : Nat) : Real)) *
          Real.log (((((X - 1) + 1 : Nat) : Real)) + 2)) *
        TS271.Goldbach.reciprocalSquareHeightWeight
          TS272.Goldbach.shiftedIntegerHeight (X - 1) =
      (C * Real.log (((((X - 1) + 1 : Nat) : Real)) + 2)) *
        (TS272.Goldbach.shiftedIntegerHeight (X - 1) *
          TS271.Goldbach.reciprocalSquareHeightWeight
            TS272.Goldbach.shiftedIntegerHeight (X - 1)) := by
        unfold TS272.Goldbach.shiftedIntegerHeight
        ring
    _ <= (C * Real.log ((X : Real) + 3)) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hLog hC)
        (shiftedIntegerHeight_mul_weight_le_one (X - 1))
        (mul_nonneg (by
            unfold TS272.Goldbach.shiftedIntegerHeight
            positivity)
          (TS271.Goldbach.reciprocalSquareHeightWeight_nonnegative
            TS272.Goldbach.shiftedIntegerHeight (X - 1)))
        (mul_nonneg hC hCommonLogNonnegative)
    _ = C * Real.log ((X : Real) + 3) := by ring

/-- Closed finite evaluation of the amortized log-linear count expression. -/
theorem shiftedIntegerAmortizedLogLinearCount_le
    (C : Real)
    (hC : 0 <= C)
    (X : Nat) :
    TS272.Goldbach.shiftedIntegerAmortizedCountBound
        (TS273.Goldbach.logLinearMultiplicityCountEnvelope C) X <=
      5 * C * Real.log ((X : Real) + 3) := by
  unfold TS272.Goldbach.shiftedIntegerAmortizedCountBound
  have hTerminal := logLinearShiftedAbelTerminal_le C hC X
  have hSum :
      Finset.sum (Finset.range (X - 1))
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope C
                (TS272.Goldbach.shiftedIntegerHeight (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  TS272.Goldbach.shiftedIntegerHeight n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  TS272.Goldbach.shiftedIntegerHeight (n + 1))) <=
        4 * C * Real.log ((X : Real) + 3) := by
    calc
      Finset.sum (Finset.range (X - 1))
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope C
                (TS272.Goldbach.shiftedIntegerHeight (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  TS272.Goldbach.shiftedIntegerHeight n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  TS272.Goldbach.shiftedIntegerHeight (n + 1))) <=
        Finset.sum (Finset.range (X - 1))
          (fun n =>
            2 * C * Real.log ((X : Real) + 3) *
              (1 / (((n + 1 : Nat) : Real) ^ 2))) := by
                apply Finset.sum_le_sum
                intro n hn
                exact logLinearShiftedAbelSummand_le C hC X n
                  (Finset.mem_range.mp hn)
      _ = (2 * C * Real.log ((X : Real) + 3)) *
          Finset.sum (Finset.range (X - 1))
            (fun n => 1 / (((n + 1 : Nat) : Real) ^ 2)) := by
              rw [Finset.mul_sum]
      _ <= (2 * C * Real.log ((X : Real) + 3)) * 2 := by
        exact mul_le_mul_of_nonneg_left
          (reciprocalSquareRangeSum_le_two (X - 1))
          (mul_nonneg
            (mul_nonneg (by norm_num) hC)
            (Real.log_nonneg (by
              have hXNonnegative : 0 <= (X : Real) := Nat.cast_nonneg X
              linarith)))
      _ = 4 * C * Real.log ((X : Real) + 3) := by ring
  linarith

/-- Closed logarithmic high-residual constant supplied by TS290. -/
noncomputable def xiClosedHighResidualConstant : Real :=
  6 * TS290.Goldbach.xiGlobalLogLinearConstant

theorem xiClosedHighResidualConstant_nonnegative :
    0 <= xiClosedHighResidualConstant := by
  unfold xiClosedHighResidualConstant
  exact mul_nonneg (by norm_num)
    TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative

/-- The frozen height-one count is controlled by the same truncation
logarithm used for the shell sum. -/
theorem xiLogLinearEnvelopeAtOne_le_commonLog
    (X : Nat) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope
        TS290.Goldbach.xiGlobalLogLinearConstant 1 <=
      TS290.Goldbach.xiGlobalLogLinearConstant *
        Real.log ((X : Real) + 3) := by
  have hLog :
      Real.log 3 <= Real.log ((X : Real) + 3) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by
        change 0 < (X : Real) + 3
        positivity)
      (by
        have hXNonnegative : 0 <= (X : Real) := Nat.cast_nonneg X
        linarith)
  rw [TS273.Goldbach.logLinearMultiplicityCountEnvelope]
  norm_num [max_eq_left]
  exact mul_le_mul_of_nonneg_left hLog
    TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative

/-- The exact high residual mass has a closed logarithmic bound. -/
theorem concreteHighImaginaryWeightedResidualMass_le_xiClosed
    (X : Nat) :
    TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X <=
      xiClosedHighResidualConstant * Real.log ((X : Real) + 3) := by
  have hTransport :=
    TS272.Goldbach.concreteHighImaginaryWeightedResidualMass_le_globalCountAmortized
      (TS273.Goldbach.logLinearMultiplicityCountEnvelope
        TS290.Goldbach.xiGlobalLogLinearConstant)
      TS290.Goldbach.xiGlobalMultiplicityCountingBoundContract
      X
  have hBoundary := xiLogLinearEnvelopeAtOne_le_commonLog X
  have hAmortized := shiftedIntegerAmortizedLogLinearCount_le
    TS290.Goldbach.xiGlobalLogLinearConstant
    TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
    X
  calc
    TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X <=
        TS273.Goldbach.logLinearMultiplicityCountEnvelope
            TS290.Goldbach.xiGlobalLogLinearConstant 1 +
          TS272.Goldbach.shiftedIntegerAmortizedCountBound
            (TS273.Goldbach.logLinearMultiplicityCountEnvelope
              TS290.Goldbach.xiGlobalLogLinearConstant) X := hTransport
    _ <=
        TS290.Goldbach.xiGlobalLogLinearConstant *
            Real.log ((X : Real) + 3) +
          5 * TS290.Goldbach.xiGlobalLogLinearConstant *
            Real.log ((X : Real) + 3) :=
      add_le_add hBoundary hAmortized
    _ = xiClosedHighResidualConstant * Real.log ((X : Real) + 3) := by
      unfold xiClosedHighResidualConstant
      ring

/-- The high quadratic mass is explicitly `O(X log X)`. -/
theorem concreteHighImaginaryQuadraticEnvelopeMass_le_xiClosed
    (X : Nat) :
    TS269.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass X <=
      max 1 (X : Real) *
        (xiClosedHighResidualConstant * Real.log ((X : Real) + 3)) := by
  rw [TS270.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass_eq_scale_mul_residualMass]
  exact mul_le_mul_of_nonneg_left
    (concreteHighImaginaryWeightedResidualMass_le_xiClosed X)
    (zero_le_one.trans (le_max_left 1 (X : Real)))

/-- Unconditional closed finite zero-contribution bound from the TS290 global
log-linear count.  The low zone remains exact. -/
theorem concreteFiniteHeightZeroContribution_abs_le_xiClosed
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) *
          (xiClosedHighResidualConstant * Real.log ((X : Real) + 3)) := by
  exact
    (TS269.Goldbach.concreteFiniteHeightZeroContribution_abs_le_low_add_highQuadratic
      X).trans
      (add_le_add_left
        (concreteHighImaginaryQuadraticEnvelopeMass_le_xiClosed X) _)

/-- Natural-height presentation of the same bound above height one. -/
theorem concreteFiniteHeightZeroContribution_abs_le_xiClosed_natScale
    (X : Nat)
    (hX : 1 <= X) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        xiClosedHighResidualConstant * (X : Real) *
          Real.log ((X : Real) + 3) := by
  have hXReal : (1 : Real) <= (X : Real) := by exact_mod_cast hX
  simpa [max_eq_right hXReal, mul_assoc, mul_left_comm, mul_comm] using
    concreteFiniteHeightZeroContribution_abs_le_xiClosed X

/-- TS291 closes the finite TS270--TS273 routing with no additional analytic
contract. -/
structure LogLinearZeroContributionAssemblyLedger where
  ts290_global_count :
    TS270.Goldbach.GlobalMultiplicityCountingBoundContract
      (TS273.Goldbach.logLinearMultiplicityCountEnvelope
        TS290.Goldbach.xiGlobalLogLinearConstant)
  reciprocal_square_partial_sums :
    forall K : Nat,
      Finset.sum (Finset.range K)
          (fun n => 1 / (((n + 1 : Nat) : Real) ^ 2)) <= 2
  high_residual_closed :
    forall X : Nat,
      TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X <=
        xiClosedHighResidualConstant * Real.log ((X : Real) + 3)
  finite_zero_contribution_closed :
    forall X : Nat,
      abs
          (TS257.Goldbach.triangleSplineZeroContributionFunction
            TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
            TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
        TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
          max 1 (X : Real) *
            (xiClosedHighResidualConstant * Real.log ((X : Real) + 3))
  infinite_zero_sum_not_proved : True
  explicit_formula_not_proved : True
  residual_estimate_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def logLinearZeroContributionAssemblyLedger :
    LogLinearZeroContributionAssemblyLedger where
  ts290_global_count :=
    TS290.Goldbach.xiGlobalMultiplicityCountingBoundContract
  reciprocal_square_partial_sums := reciprocalSquareRangeSum_le_two
  high_residual_closed :=
    concreteHighImaginaryWeightedResidualMass_le_xiClosed
  finite_zero_contribution_closed :=
    concreteFiniteHeightZeroContribution_abs_le_xiClosed
  infinite_zero_sum_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  residual_estimate_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def LogLinearZeroContributionAssemblyTarget : Prop :=
  Nonempty LogLinearZeroContributionAssemblyLedger

theorem logLinearZeroContributionAssemblyTarget :
    LogLinearZeroContributionAssemblyTarget :=
  Nonempty.intro logLinearZeroContributionAssemblyLedger

end Goldbach
end TS291
