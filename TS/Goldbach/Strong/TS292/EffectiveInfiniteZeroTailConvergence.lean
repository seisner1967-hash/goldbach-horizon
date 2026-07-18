import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic
import TS.Goldbach.Strong.TS291.LogLinearZeroContributionAssembly

/-!
# TS292 - Effective Infinite Zero-Tail Convergence

TS291 closed the finite zero-contribution bound.  This sprint separates the
arithmetic scale `x` from the spectral truncation height `T` and proves
absolute convergence of the complete triangle-spline zero series.

The proof remains finite until the final `Summable` step.  Starting at height
`T`, the exact shells `(T+n, T+n+1]` are passed through the TS271 Abel
identity.  The logarithmic count is absorbed by the telescoping potential

`(log (t + 3) + 2) / t`.

This gives a bound, uniform in the upper cutoff, of order
`(log (T + 2) + 1) / T`.  The general finite-sum criterion then supplies
absolute summability, a `HasSum`, an infinite contribution, and an effective
tail estimate.

No von Mangoldt identity, explicit formula, contour estimate, Gallagher
estimate, OTSA bridge, or Goldbach statement is proved.
-/

noncomputable section

namespace TS292
namespace Goldbach

open Filter Set
open scoped BigOperators Topology

/-- Shifted integer heights beginning at an arbitrary natural height `T`. -/
noncomputable def tailIntegerHeight
    (T n : Nat) :
    Real :=
  (T + n : Nat)

/-- Positive monotone data for the tail chain `T, T+1, ...`. -/
theorem tailIntegerHeight_positiveMonotone
    (T : Nat)
    (hT : 1 <= T) :
    TS271.Goldbach.PositiveMonotoneHeightChain (tailIntegerHeight T) where
  positive := by
    intro n
    unfold tailIntegerHeight
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one
      (hT.trans (Nat.le_add_right T n))
  monotone := by
    intro m n hmn
    unfold tailIntegerHeight
    exact_mod_cast Nat.add_le_add_left hmn T

/-- Tail shells telescope exactly from `T` to `T+K`. -/
theorem tailIntegerShellMassSum_telescope
    (T K : Nat) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        (tailIntegerHeight T) K =
      TS271.Goldbach.concreteHeightShellReciprocalSquareMass
        (T : Real) ((T + K : Nat) : Real) := by
  induction K with
  | zero =>
      have hEmpty :
          TS271.Goldbach.concreteHeightShell (T : Real) (T : Real) = {} :=
        TS272.Goldbach.concreteHeightShell_eq_empty_of_le le_rfl
      unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass
      simp [hEmpty]
  | succ K hK =>
      unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum at hK
      unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
      rw [Finset.sum_range_succ, hK]
      have hAdd := TS272.Goldbach.concreteHeightShellReciprocalSquareMass_add
        (A := (T : Real))
        (B := ((T + K : Nat) : Real))
        (C := ((T + K + 1 : Nat) : Real))
        (by exact_mod_cast Nat.le_add_right T K)
        (by exact_mod_cast Nat.le_succ (T + K))
      simpa [tailIntegerHeight, Nat.add_assoc] using hAdd.symm

/-- The logarithmic potential whose finite differences absorb Abel weights. -/
noncomputable def logarithmicTailPotential
    (t : Real) :
    Real :=
  (Real.log (t + 3) + 2) / t

/-- Closed target rate for a spectral tail beginning at height `T`. -/
noncomputable def logarithmicTailRate
    (T : Nat) :
    Real :=
  (Real.log ((T : Real) + 2) + 1) / (T : Real)

/-- The logarithm grows by at most the reciprocal tangent increment. -/
theorem log_add_one_sub_log_le_inv
    (x : Real)
    (hx : 0 < x) :
    Real.log (x + 1) - Real.log x <= 1 / x := by
  have hRatio : 0 < (x + 1) / x := div_pos (by linarith) hx
  have hLog := Real.log_le_sub_one_of_pos hRatio
  rw [Real.log_div (by
      exact Not.intro (fun h => by linarith) : Not (x + 1 = 0)) hx.ne'] at hLog
  calc
    Real.log (x + 1) - Real.log x <= (x + 1) / x - 1 := hLog
    _ = 1 / x := by
      field_simp

/-- A real Abel coefficient is at most twice its lower reciprocal square. -/
theorem realAbelCoefficient_le
    (t : Real)
    (ht : 1 <= t) :
    (t + 1) * (1 / t ^ 2 - 1 / (t + 1) ^ 2) <=
      2 / t ^ 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hIdentity :
      (t + 1) * (1 / t ^ 2 - 1 / (t + 1) ^ 2) =
        (2 * t + 1) / (t ^ 2 * (t + 1)) := by
    field_simp
    ring
  rw [hIdentity]
  have hDifference :
      (2 * t + 1) / (t ^ 2 * (t + 1)) =
        2 / t ^ 2 - 1 / (t ^ 2 * (t + 1)) := by
    field_simp
    ring
  rw [hDifference]
  exact sub_le_self _ (by positivity)

/-- One logarithmic reciprocal-square term is a potential difference. -/
theorem logarithmicWeight_le_twice_potentialDrop
    (t : Real)
    (ht : 1 <= t) :
    Real.log (t + 3) / t ^ 2 <=
      2 * (logarithmicTailPotential t -
        logarithmicTailPotential (t + 1)) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hLogNonnegative : 0 <= Real.log (t + 3) := by
    apply Real.log_nonneg
    linarith
  have hIncrement :
      Real.log (t + 4) - Real.log (t + 3) <= 1 / (t + 3) := by
    convert log_add_one_sub_log_le_inv (t + 3) (by linarith) using 1
    ring
  have hMulIncrement :
      t * (Real.log (t + 4) - Real.log (t + 3)) <= t / (t + 3) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hIncrement (le_of_lt ht0)
  have hRatio : t / (t + 3) <= 1 := by
    exact (div_le_one (by linarith : 0 < t + 3)).mpr (by linarith)
  have hNumerator :
      Real.log (t + 3) <=
        Real.log (t + 3) + 2 -
          t * (Real.log (t + 4) - Real.log (t + 3)) := by
    linarith
  have hDrop :
      logarithmicTailPotential t -
          logarithmicTailPotential (t + 1) =
        (Real.log (t + 3) + 2 -
            t * (Real.log (t + 4) - Real.log (t + 3))) /
          (t * (t + 1)) := by
    unfold logarithmicTailPotential
    field_simp
    ring
  rw [hDrop]
  have hDenomLeft : 0 < t ^ 2 := pow_pos ht0 2
  have hDenomRight : 0 < t * (t + 1) := mul_pos ht0 (by linarith)
  rw [show
      2 *
          ((Real.log (t + 3) + 2 -
              t * (Real.log (t + 4) - Real.log (t + 3))) /
            (t * (t + 1))) =
        (2 *
          (Real.log (t + 3) + 2 -
            t * (Real.log (t + 4) - Real.log (t + 3)))) /
          (t * (t + 1)) by ring]
  have hStep : t + 1 <= 2 * t := by linarith
  have hLeft :
      Real.log (t + 3) * (t * (t + 1)) <=
        Real.log (t + 3) * (t * (2 * t)) := by
    gcongr
  have hRight :
      Real.log (t + 3) * (t * (2 * t)) <=
        (2 *
          (Real.log (t + 3) + 2 -
            t * (Real.log (t + 4) - Real.log (t + 3)))) *
          t ^ 2 := by
    have hNumMul :=
      mul_le_mul_of_nonneg_right hNumerator (sq_nonneg t)
    nlinarith
  have hCross := hLeft.trans hRight
  apply le_of_sub_nonneg
  have hDifference :
      (2 *
            (Real.log (t + 3) + 2 -
              t * (Real.log (t + 4) - Real.log (t + 3)))) /
          (t * (t + 1)) -
        Real.log (t + 3) / t ^ 2 =
      ((2 *
            (Real.log (t + 3) + 2 -
              t * (Real.log (t + 4) - Real.log (t + 3)))) *
          t ^ 2 -
        Real.log (t + 3) * (t * (t + 1))) /
        ((t * (t + 1)) * t ^ 2) := by
    field_simp
    ring
  rw [hDifference]
  exact div_nonneg (sub_nonneg.mpr hCross)
    (le_of_lt (mul_pos hDenomRight hDenomLeft))

/-- The logarithmic potential is nonnegative above height one. -/
theorem logarithmicTailPotential_nonnegative
    (t : Real)
    (ht : 1 <= t) :
    0 <= logarithmicTailPotential t := by
  unfold logarithmicTailPotential
  exact div_nonneg
    (add_nonneg
      (Real.log_nonneg (by linarith))
      (by norm_num))
    (by linarith)

/-- The potential decreases along every natural tail chain. -/
theorem logarithmicTailPotential_antitone_nat
    (T : Nat)
    (hT : 1 <= T) :
    Antitone
      (fun n : Nat =>
        logarithmicTailPotential (tailIntegerHeight T n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have ht :
      (1 : Real) <= tailIntegerHeight T n := by
    unfold tailIntegerHeight
    exact_mod_cast hT.trans (Nat.le_add_right T n)
  have hWeight := logarithmicWeight_le_twice_potentialDrop
    (tailIntegerHeight T n) ht
  have hLogNonnegative :
      0 <= Real.log (tailIntegerHeight T n + 3) := by
    apply Real.log_nonneg
    linarith
  have hDrop :
      0 <= logarithmicTailPotential (tailIntegerHeight T n) -
        logarithmicTailPotential (tailIntegerHeight T n + 1) := by
    nlinarith [div_nonneg hLogNonnegative (sq_nonneg (tailIntegerHeight T n))]
  have hHeightSucc :
      tailIntegerHeight T (n + 1) = tailIntegerHeight T n + 1 := by
    unfold tailIntegerHeight
    push_cast
    ring
  rw [hHeightSucc]
  linarith

/-- The safe TS273 envelope has its elementary form on a tail chain. -/
theorem logLinearEnvelope_tailIntegerHeight
    (C : Real)
    (T n : Nat)
    (hT : 1 <= T) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope C
        (tailIntegerHeight T n) =
      C * tailIntegerHeight T n *
        Real.log (tailIntegerHeight T n + 2) := by
  have hOne : (1 : Real) <= tailIntegerHeight T n := by
    unfold tailIntegerHeight
    exact_mod_cast hT.trans (Nat.le_add_right T n)
  rw [TS273.Goldbach.logLinearMultiplicityCountEnvelope, max_eq_left hOne]

/-- Reciprocal-square weights on a tail chain have their literal form. -/
theorem reciprocalSquareHeightWeight_tailIntegerHeight
    (T n : Nat) :
    TS271.Goldbach.reciprocalSquareHeightWeight
        (tailIntegerHeight T) n =
      1 / tailIntegerHeight T n ^ 2 :=
  rfl

/-- Every tail Abel summand is absorbed by four potential differences. -/
theorem logLinearTailAbelSummand_le_potentialDrop
    (C : Real)
    (hC : 0 <= C)
    (T : Nat)
    (hT : 1 <= T)
    (n : Nat) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope C
          (tailIntegerHeight T (n + 1)) *
        (TS271.Goldbach.reciprocalSquareHeightWeight
            (tailIntegerHeight T) n -
          TS271.Goldbach.reciprocalSquareHeightWeight
            (tailIntegerHeight T) (n + 1)) <=
      4 * C *
        (logarithmicTailPotential (tailIntegerHeight T n) -
          logarithmicTailPotential (tailIntegerHeight T (n + 1))) := by
  have ht : (1 : Real) <= tailIntegerHeight T n := by
    unfold tailIntegerHeight
    exact_mod_cast hT.trans (Nat.le_add_right T n)
  have hSucc :
      tailIntegerHeight T (n + 1) = tailIntegerHeight T n + 1 := by
    unfold tailIntegerHeight
    push_cast
    ring
  have hLogNonnegative :
      0 <= Real.log (tailIntegerHeight T n + 3) := by
    apply Real.log_nonneg
    linarith
  have hCoefficientNonnegative :
      0 <=
        (tailIntegerHeight T n + 1) *
          (1 / tailIntegerHeight T n ^ 2 -
            1 / (tailIntegerHeight T n + 1) ^ 2) := by
    have hWeight :
        1 / (tailIntegerHeight T n + 1) ^ 2 <=
          1 / tailIntegerHeight T n ^ 2 := by
      exact one_div_le_one_div_of_le
        (pow_pos (zero_lt_one.trans_le ht) 2)
        (by nlinarith)
    exact mul_nonneg (by linarith) (sub_nonneg.mpr hWeight)
  rw [logLinearEnvelope_tailIntegerHeight C T (n + 1) hT,
    reciprocalSquareHeightWeight_tailIntegerHeight,
    reciprocalSquareHeightWeight_tailIntegerHeight, hSucc]
  calc
    (C * (tailIntegerHeight T n + 1) *
          Real.log (tailIntegerHeight T n + 1 + 2)) *
        (1 / tailIntegerHeight T n ^ 2 -
          1 / (tailIntegerHeight T n + 1) ^ 2) =
      (C * Real.log (tailIntegerHeight T n + 3)) *
        ((tailIntegerHeight T n + 1) *
          (1 / tailIntegerHeight T n ^ 2 -
            1 / (tailIntegerHeight T n + 1) ^ 2)) := by ring
    _ <=
      (C * Real.log (tailIntegerHeight T n + 3)) *
        (2 / tailIntegerHeight T n ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (realAbelCoefficient_le (tailIntegerHeight T n) ht)
        (mul_nonneg hC hLogNonnegative)
    _ <=
      (2 * C) *
        (2 *
          (logarithmicTailPotential (tailIntegerHeight T n) -
            logarithmicTailPotential (tailIntegerHeight T n + 1))) := by
      have hWeight := logarithmicWeight_le_twice_potentialDrop
        (tailIntegerHeight T n) ht
      calc
        (C * Real.log (tailIntegerHeight T n + 3)) *
              (2 / tailIntegerHeight T n ^ 2) =
            (2 * C) *
              (Real.log (tailIntegerHeight T n + 3) /
                tailIntegerHeight T n ^ 2) := by ring
        _ <= (2 * C) *
              (2 *
                (logarithmicTailPotential (tailIntegerHeight T n) -
                  logarithmicTailPotential
                    (tailIntegerHeight T n + 1))) := by
          exact mul_le_mul_of_nonneg_left hWeight
            (mul_nonneg (by norm_num) hC)
    _ =
      4 * C *
        (logarithmicTailPotential (tailIntegerHeight T n) -
          logarithmicTailPotential (tailIntegerHeight T n + 1)) := by ring

/-- The terminal Abel term is at most one initial potential. -/
theorem logLinearTailAbelTerminal_le_potential
    (C : Real)
    (hC : 0 <= C)
    (T : Nat)
    (hT : 1 <= T)
    (K : Nat) :
    TS273.Goldbach.logLinearMultiplicityCountEnvelope C
          (tailIntegerHeight T K) *
        TS271.Goldbach.reciprocalSquareHeightWeight
          (tailIntegerHeight T) K <=
      C * logarithmicTailPotential (T : Real) := by
  have hHeight : (1 : Real) <= tailIntegerHeight T K := by
    unfold tailIntegerHeight
    exact_mod_cast hT.trans (Nat.le_add_right T K)
  rw [logLinearEnvelope_tailIntegerHeight C T K hT,
    reciprocalSquareHeightWeight_tailIntegerHeight]
  have hAtHeight :
      C * tailIntegerHeight T K *
          Real.log (tailIntegerHeight T K + 2) *
          (1 / tailIntegerHeight T K ^ 2) <=
        C * logarithmicTailPotential (tailIntegerHeight T K) := by
    have hLog :
        Real.log (tailIntegerHeight T K + 2) <=
          Real.log (tailIntegerHeight T K + 3) + 2 := by
      have hMono :
          Real.log (tailIntegerHeight T K + 2) <=
            Real.log (tailIntegerHeight T K + 3) := by
        exact Real.strictMonoOn_log.monotoneOn
          (by
            show 0 < tailIntegerHeight T K + 2
            linarith)
          (by
            show 0 < tailIntegerHeight T K + 3
            linarith)
          (by linarith)
      linarith
    unfold logarithmicTailPotential
    have hPos : 0 < tailIntegerHeight T K := zero_lt_one.trans_le hHeight
    calc
      C * tailIntegerHeight T K *
            Real.log (tailIntegerHeight T K + 2) *
            (1 / tailIntegerHeight T K ^ 2) =
          C * (Real.log (tailIntegerHeight T K + 2) /
            tailIntegerHeight T K) := by
              field_simp
              ring
      _ <= C * ((Real.log (tailIntegerHeight T K + 3) + 2) /
            tailIntegerHeight T K) := by
              exact mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hLog (le_of_lt hPos)) hC
  exact hAtHeight.trans
    (mul_le_mul_of_nonneg_left
      (logarithmicTailPotential_antitone_nat T hT (Nat.zero_le K))
      hC)

/-- The initial potential is controlled by three copies of the target rate. -/
theorem logarithmicTailPotential_le_three_rate
    (T : Nat)
    (hT : 1 <= T) :
    logarithmicTailPotential (T : Real) <=
      3 * logarithmicTailRate T := by
  have hTReal : (1 : Real) <= (T : Real) := by exact_mod_cast hT
  have hIncrement :
      Real.log ((T : Real) + 3) - Real.log ((T : Real) + 2) <=
        1 / ((T : Real) + 2) := by
    convert log_add_one_sub_log_le_inv ((T : Real) + 2) (by linarith) using 1
    ring
  have hInv : 1 / ((T : Real) + 2) <= 1 := by
    exact (div_le_one (by linarith : 0 < (T : Real) + 2)).mpr (by linarith)
  have hLogNonnegative : 0 <= Real.log ((T : Real) + 2) := by
    apply Real.log_nonneg
    linarith
  unfold logarithmicTailPotential logarithmicTailRate
  rw [show
      3 * ((Real.log ((T : Real) + 2) + 1) / (T : Real)) =
        (3 * (Real.log ((T : Real) + 2) + 1)) / (T : Real) by ring]
  apply (div_le_div_iff_of_pos_right
    (by linarith : 0 < (T : Real))).mpr
  nlinarith

/-- Uniform tail-shell bound, independent of the upper cutoff. -/
theorem tailIntegerShellMassSum_le_logarithmicRate
    (T K : Nat)
    (hT : 1 <= T) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        (tailIntegerHeight T) K <=
      15 * TS290.Goldbach.xiGlobalLogLinearConstant *
        logarithmicTailRate T := by
  have hTransport :=
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum_le_of_globalCount
      (tailIntegerHeight T)
      (tailIntegerHeight_positiveMonotone T hT)
      (TS273.Goldbach.logLinearMultiplicityCountEnvelope
        TS290.Goldbach.xiGlobalLogLinearConstant)
      TS290.Goldbach.xiGlobalMultiplicityCountingBoundContract
      K
  have hTerminal := logLinearTailAbelTerminal_le_potential
    TS290.Goldbach.xiGlobalLogLinearConstant
    TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
    T hT K
  have hSum :
      Finset.sum (Finset.range K)
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope
                TS290.Goldbach.xiGlobalLogLinearConstant
                (tailIntegerHeight T (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  (tailIntegerHeight T) n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  (tailIntegerHeight T) (n + 1))) <=
        4 * TS290.Goldbach.xiGlobalLogLinearConstant *
          logarithmicTailPotential (T : Real) := by
    calc
      Finset.sum (Finset.range K)
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope
                TS290.Goldbach.xiGlobalLogLinearConstant
                (tailIntegerHeight T (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  (tailIntegerHeight T) n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  (tailIntegerHeight T) (n + 1))) <=
        Finset.sum (Finset.range K)
          (fun n =>
            4 * TS290.Goldbach.xiGlobalLogLinearConstant *
              (logarithmicTailPotential (tailIntegerHeight T n) -
                logarithmicTailPotential
                  (tailIntegerHeight T (n + 1)))) := by
        apply Finset.sum_le_sum
        intro n _
        exact logLinearTailAbelSummand_le_potentialDrop
          TS290.Goldbach.xiGlobalLogLinearConstant
          TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
          T hT n
      _ =
        4 * TS290.Goldbach.xiGlobalLogLinearConstant *
          (logarithmicTailPotential (T : Real) -
            logarithmicTailPotential (tailIntegerHeight T K)) := by
        rw [<- Finset.mul_sum, Finset.sum_range_sub']
        rfl
      _ <=
        4 * TS290.Goldbach.xiGlobalLogLinearConstant *
          logarithmicTailPotential (T : Real) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_self _
            (logarithmicTailPotential_nonnegative
              (tailIntegerHeight T K)
              (by
                unfold tailIntegerHeight
                exact_mod_cast hT.trans (Nat.le_add_right T K))))
          (mul_nonneg (by norm_num)
            TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative)
  have hPotential :=
    logarithmicTailPotential_le_three_rate T hT
  calc
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
          (tailIntegerHeight T) K <=
        TS273.Goldbach.logLinearMultiplicityCountEnvelope
              TS290.Goldbach.xiGlobalLogLinearConstant
              (tailIntegerHeight T K) *
            TS271.Goldbach.reciprocalSquareHeightWeight
              (tailIntegerHeight T) K +
          Finset.sum (Finset.range K)
            (fun n =>
              TS273.Goldbach.logLinearMultiplicityCountEnvelope
                  TS290.Goldbach.xiGlobalLogLinearConstant
                  (tailIntegerHeight T (n + 1)) *
                (TS271.Goldbach.reciprocalSquareHeightWeight
                    (tailIntegerHeight T) n -
                  TS271.Goldbach.reciprocalSquareHeightWeight
                    (tailIntegerHeight T) (n + 1))) := hTransport
    _ <=
        5 * TS290.Goldbach.xiGlobalLogLinearConstant *
          logarithmicTailPotential (T : Real) := by
      nlinarith
    _ <=
        5 * TS290.Goldbach.xiGlobalLogLinearConstant *
          (3 * logarithmicTailRate T) := by
      exact mul_le_mul_of_nonneg_left hPotential
        (mul_nonneg (by norm_num)
          TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative)
    _ =
        15 * TS290.Goldbach.xiGlobalLogLinearConstant *
          logarithmicTailRate T := by ring

/-- Uniform reciprocal-square mass in `(T,U]`, with no dependence on `U`. -/
theorem concreteHeightShellReciprocalSquareMass_le_logarithmicRate
    (T U : Nat)
    (hT : 1 <= T) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMass
        (T : Real) (U : Real) <=
      15 * TS290.Goldbach.xiGlobalLogLinearConstant *
        logarithmicTailRate T := by
  by_cases hUT : U <= T
  case pos =>
    have hEmpty :
        TS271.Goldbach.concreteHeightShell (T : Real) (U : Real) = {} :=
      TS272.Goldbach.concreteHeightShell_eq_empty_of_le (by exact_mod_cast hUT)
    unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMass
    rw [hEmpty]
    simp only [Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative)
      (div_nonneg
        (add_nonneg
          (Real.log_nonneg (by
            have hTReal : (1 : Real) <= (T : Real) := by exact_mod_cast hT
            linarith))
          (by norm_num))
        (by positivity))
  case neg =>
    have hTU : T <= U := Nat.le_of_lt (lt_of_not_ge hUT)
    have hEq :
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass
            (T : Real) (U : Real) =
          TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
            (tailIntegerHeight T) (U - T) := by
      rw [tailIntegerShellMassSum_telescope]
      simp [Nat.add_sub_of_le hTU]
    rw [hEq]
    exact tailIntegerShellMassSum_le_logarithmicRate T (U - T) hT

/-- The global index type of concrete nontrivial zeta zeros. -/
abbrev ConcreteNontrivialZero :=
  {rho : Complex // TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho}

/-- Exact concrete zeros of the global subtype below height `T`. -/
noncomputable def concreteZerosUpToHeightSubtype
    (T : Nat) :
    Finset ConcreteNontrivialZero :=
  (TS265.Goldbach.zerosUpToHeight (T : Real)).preimage
    Subtype.val Subtype.val_injective.injOn

/-- Membership in the subtype truncation is exactly the height inequality. -/
theorem mem_concreteZerosUpToHeightSubtype_iff
    (T : Nat)
    (rho : ConcreteNontrivialZero) :
    Iff (Membership.mem (concreteZerosUpToHeightSubtype T) rho)
      (abs rho.1.im <= (T : Real)) := by
  rw [concreteZerosUpToHeightSubtype, Finset.mem_preimage,
    TS265.Goldbach.mem_zerosUpToHeight_iff]
  simp [rho.property]

/-- The multiplicity-weighted triangle-spline term on the global zero type. -/
noncomputable def infiniteZeroSpectralTerm
    (x : Nat)
    (rho : ConcreteNontrivialZero) :
    Complex :=
  TS266.Goldbach.concreteFiniteHeightZeroTerm x rho.1

/-- The explicit constant in the reciprocal-square zero tail. -/
noncomputable def infiniteZeroResidualTailConstant : Real :=
  15 * TS290.Goldbach.xiGlobalLogLinearConstant

theorem infiniteZeroResidualTailConstant_nonnegative :
    0 <= infiniteZeroResidualTailConstant := by
  unfold infiniteZeroResidualTailConstant
  exact mul_nonneg (by norm_num)
    TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative

/-- A global zero term above height one has the expected scale-residual bound. -/
theorem infiniteZeroSpectralTerm_norm_le_scale_mul_residual
    (x : Nat)
    (rho : ConcreteNontrivialZero)
    (hHigh : 1 <= abs rho.1.im) :
    norm (infiniteZeroSpectralTerm x rho) <=
      max 1 (x : Real) *
        TS269.Goldbach.highImaginaryResidualEnvelope rho.1 := by
  unfold infiniteZeroSpectralTerm
  change
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm x rho.1) <=
      max 1 (x : Real) *
        TS269.Goldbach.highImaginaryResidualEnvelope rho.1
  rw [TS268.Goldbach.concreteFiniteHeightZeroTerm_abs_eq_scale_mul_factor]
  exact mul_le_mul
    (TS268.Goldbach.naturalScaleComplexPower_abs_le_max_one
      x rho.1 rho.property)
    (TS269.Goldbach.concreteMultiplicityDenominatorFactor_abs_le_highEnvelope
      rho.1 hHigh)
    (Complex.abs.nonneg _)
    (zero_le_one.trans (le_max_left 1 (x : Real)))

/-- Every finite residual tail is bounded independently of its upper height. -/
theorem finiteInfiniteZeroResidualTail_sum_le
    (T : Nat)
    (hT : 1 <= T)
    (s : Finset
      {rho : ConcreteNontrivialZero //
        Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)}) :
    Finset.sum s
        (fun rho =>
          TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) <=
      infiniteZeroResidualTailConstant * logarithmicTailRate T := by
  classical
  let U : Nat :=
    max T (s.sup (fun rho => Nat.ceil (abs rho.1.1.im)))
  let values : Finset Complex := s.image (fun rho => rho.1.1)
  have hSubset :
      values <= TS271.Goldbach.concreteHeightShell (T : Real) (U : Real) := by
    intro rho hRho
    have hExists := Finset.mem_image.mp hRho
    choose z hz hValue using hExists
    subst rho
    have hNotLower :
        Not (abs z.1.1.im <= (T : Real)) := by
      intro hLower
      exact z.property
        ((mem_concreteZerosUpToHeightSubtype_iff T z.1).mpr hLower)
    have hCeil :
        abs z.1.1.im <= ((Nat.ceil (abs z.1.1.im) : Nat) : Real) :=
      Nat.le_ceil _
    have hSup :
        Nat.ceil (abs z.1.1.im) <=
          s.sup (fun w => Nat.ceil (abs w.1.1.im)) :=
      Finset.le_sup (f := fun w => Nat.ceil (abs w.1.1.im)) hz
    have hUpperNat :
        Nat.ceil (abs z.1.1.im) <= U :=
      hSup.trans (le_max_right _ _)
    have hUpper : abs z.1.1.im <= (U : Real) :=
      hCeil.trans (by exact_mod_cast hUpperNat)
    exact (TS271.Goldbach.mem_concreteHeightShell_iff
      (T : Real) (U : Real) z.1.1).mpr
        (And.intro z.1.property
          (And.intro (lt_of_not_ge hNotLower) hUpper))
  have hImageSum :
      Finset.sum values TS269.Goldbach.highImaginaryResidualEnvelope =
        Finset.sum s
          (fun rho =>
            TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) := by
    exact Finset.sum_image
      (fun a _ b _ hab => by
        exact Subtype.ext (Subtype.ext hab))
  rw [<- hImageSum]
  calc
    Finset.sum values TS269.Goldbach.highImaginaryResidualEnvelope <=
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass
          (T : Real) (U : Real) := by
      unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun rho _ _ =>
          TS269.Goldbach.highImaginaryResidualEnvelope_nonnegative rho)
    _ <= 15 * TS290.Goldbach.xiGlobalLogLinearConstant *
          logarithmicTailRate T :=
      concreteHeightShellReciprocalSquareMass_le_logarithmicRate T U hT
    _ = infiniteZeroResidualTailConstant * logarithmicTailRate T := rfl

/-- Uniform finite norm-tail bound with independent arithmetic scale `x`. -/
theorem finiteInfiniteZeroSpectralTail_norm_sum_le
    (x T : Nat)
    (hT : 1 <= T)
    (s : Finset
      {rho : ConcreteNontrivialZero //
        Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)}) :
    Finset.sum s (fun rho => norm (infiniteZeroSpectralTerm x rho.1)) <=
      max 1 (x : Real) *
        (infiniteZeroResidualTailConstant * logarithmicTailRate T) := by
  have hPointwise :
      forall rho :
          {rho : ConcreteNontrivialZero //
            Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)},
        norm (infiniteZeroSpectralTerm x rho.1) <=
          max 1 (x : Real) *
            TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1 := by
    intro rho
    have hNotLe :
        Not (abs rho.1.1.im <= (T : Real)) := by
      intro hLe
      exact rho.property
        ((mem_concreteZerosUpToHeightSubtype_iff T rho.1).mpr hLe)
    have hHigh :
        1 <= abs rho.1.1.im := by
      have hTReal : (1 : Real) <= (T : Real) := by exact_mod_cast hT
      exact hTReal.trans (le_of_lt (lt_of_not_ge hNotLe))
    exact infiniteZeroSpectralTerm_norm_le_scale_mul_residual
      x rho.1 hHigh
  calc
    Finset.sum s (fun rho => norm (infiniteZeroSpectralTerm x rho.1)) <=
        Finset.sum s
          (fun rho =>
            max 1 (x : Real) *
              TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) := by
      apply Finset.sum_le_sum
      intro rho _
      exact hPointwise rho
    _ =
        max 1 (x : Real) *
          Finset.sum s
            (fun rho =>
              TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) := by
      rw [Finset.mul_sum]
    _ <=
        max 1 (x : Real) *
          (infiniteZeroResidualTailConstant * logarithmicTailRate T) := by
      exact mul_le_mul_of_nonneg_left
        (finiteInfiniteZeroResidualTail_sum_le T hT s)
        (zero_le_one.trans (le_max_left 1 (x : Real)))

/-- Absolute summability of every spectral tail above a positive height. -/
theorem infiniteZeroSpectralTail_norm_summable
    (x T : Nat)
    (hT : 1 <= T) :
    Summable
      (fun rho :
        {rho : ConcreteNontrivialZero //
          Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)} =>
        norm (infiniteZeroSpectralTerm x rho.1)) :=
  summable_of_sum_le
    (fun _ => norm_nonneg _)
    (finiteInfiniteZeroSpectralTail_norm_sum_le x T hT)

/-- Complex summability of every spectral tail. -/
theorem infiniteZeroSpectralTail_summable
    (x T : Nat)
    (hT : 1 <= T) :
    Summable
      (fun rho :
        {rho : ConcreteNontrivialZero //
          Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)} =>
        infiniteZeroSpectralTerm x rho.1) :=
  (infiniteZeroSpectralTail_norm_summable x T hT).of_norm

/-- The complete concrete zero series is absolutely summable. -/
theorem infiniteZeroSpectralTerm_norm_summable
    (x : Nat) :
    Summable (fun rho : ConcreteNontrivialZero =>
      norm (infiniteZeroSpectralTerm x rho)) := by
  let tailSet : Set ConcreteNontrivialZero :=
    {rho | Not (Membership.mem (concreteZerosUpToHeightSubtype 1) rho)}
  have hTail :
      Summable
        ((fun rho : ConcreteNontrivialZero =>
          norm (infiniteZeroSpectralTerm x rho)).comp
            (fun rho : tailSet => rho.1)) := by
    simpa [tailSet, Function.comp_def] using
      infiniteZeroSpectralTail_norm_summable x 1 (by norm_num)
  have hFiniteComplement :
      (Set.compl tailSet).Finite := by
    have hEq :
        Set.compl tailSet =
          (concreteZerosUpToHeightSubtype 1 : Set ConcreteNontrivialZero) := by
      ext rho
      change Iff
        (Not (Not (Membership.mem
          (concreteZerosUpToHeightSubtype 1) rho)))
        (Membership.mem (concreteZerosUpToHeightSubtype 1) rho)
      simp only [not_not]
    rw [hEq]
    exact Finset.finite_toSet _
  letI : Finite (Set.compl tailSet) :=
    hFiniteComplement.to_subtype
  have hLow :
      Summable
        ((fun rho : ConcreteNontrivialZero =>
          norm (infiniteZeroSpectralTerm x rho)).comp
            (fun rho : Set.compl tailSet => rho.1)) :=
    Summable.of_finite
  exact Summable.add_compl (s := tailSet) hTail hLow

/-- Absolute convergence implies convergence of the complex zero series. -/
theorem infiniteZeroSpectralTerm_summable
    (x : Nat) :
    Summable (infiniteZeroSpectralTerm x) :=
  (infiniteZeroSpectralTerm_norm_summable x).of_norm

/-- The complete infinite triangle-spline zero contribution. -/
noncomputable def infiniteZeroContribution
    (x : Nat) :
    Complex :=
  tsum (fun rho : ConcreteNontrivialZero => infiniteZeroSpectralTerm x rho)

/-- The complete zero series has the canonical `HasSum`. -/
theorem infiniteZeroSpectralTerm_hasSum
    (x : Nat) :
    HasSum (infiniteZeroSpectralTerm x) (infiniteZeroContribution x) :=
  (infiniteZeroSpectralTerm_summable x).hasSum

/-- Two-parameter finite contribution: arithmetic scale `x`, height `T`. -/
noncomputable def truncatedInfiniteZeroContribution
    (x T : Nat) :
    Complex :=
  Finset.sum (concreteZerosUpToHeightSubtype T)
    (infiniteZeroSpectralTerm x)

/-- The infinite tail beyond exact height `T`. -/
noncomputable def infiniteZeroContributionTail
    (x T : Nat) :
    Complex :=
  tsum (fun rho :
      {rho : ConcreteNontrivialZero //
        Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)} =>
    infiniteZeroSpectralTerm x rho.1)

/-- Exact finite/infinite decomposition at every natural height. -/
theorem truncated_add_infiniteZeroContributionTail
    (x T : Nat) :
    truncatedInfiniteZeroContribution x T +
        infiniteZeroContributionTail x T =
      infiniteZeroContribution x := by
  unfold truncatedInfiniteZeroContribution
    infiniteZeroContributionTail infiniteZeroContribution
  exact sum_add_tsum_subtype_compl
    (infiniteZeroSpectralTerm_summable x)
    (concreteZerosUpToHeightSubtype T)

/-- Effective norm bound for the complete tail beyond height `T`. -/
theorem infiniteZeroContributionTail_norm_le
    (x T : Nat)
    (hT : 1 <= T) :
    norm (infiniteZeroContributionTail x T) <=
      max 1 (x : Real) *
        (infiniteZeroResidualTailConstant * logarithmicTailRate T) := by
  have hNormSummable :=
    infiniteZeroSpectralTail_norm_summable x T hT
  calc
    norm (infiniteZeroContributionTail x T) <=
        tsum (fun rho :
          {rho : ConcreteNontrivialZero //
            Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)} =>
          norm (infiniteZeroSpectralTerm x rho.1)) :=
      norm_tsum_le_tsum_norm hNormSummable
    _ <= max 1 (x : Real) *
        (infiniteZeroResidualTailConstant * logarithmicTailRate T) :=
      tsum_le_of_sum_le hNormSummable
        (finiteInfiniteZeroSpectralTail_norm_sum_le x T hT)

/-- Effective difference between the infinite and finite contributions. -/
theorem infiniteZeroContribution_sub_truncated_norm_le
    (x T : Nat)
    (hT : 1 <= T) :
    norm
        (infiniteZeroContribution x -
          truncatedInfiniteZeroContribution x T) <=
      max 1 (x : Real) *
        (infiniteZeroResidualTailConstant * logarithmicTailRate T) := by
  have hSplit := truncated_add_infiniteZeroContributionTail x T
  have hEq :
      infiniteZeroContribution x -
          truncatedInfiniteZeroContribution x T =
        infiniteZeroContributionTail x T := by
    rw [<- hSplit]
    abel
  rw [hEq]
  exact infiniteZeroContributionTail_norm_le x T hT

/-- The exact subtype truncations exhaust the global zero index type. -/
theorem concreteZerosUpToHeightSubtype_tendsto_atTop :
    Tendsto concreteZerosUpToHeightSubtype atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  next =>
    intro T U hTU rho hRho
    apply (mem_concreteZerosUpToHeightSubtype_iff U rho).mpr
    exact (mem_concreteZerosUpToHeightSubtype_iff T rho).mp hRho |>.trans
      (by exact_mod_cast hTU)
  next =>
    intro rho
    refine Exists.intro (Nat.ceil (abs rho.1.im)) ?_
    exact (mem_concreteZerosUpToHeightSubtype_iff _ rho).mpr (Nat.le_ceil _)

/-- The concrete finite trunctions converge to the infinite zero contribution. -/
theorem truncatedInfiniteZeroContribution_tendsto
    (x : Nat) :
    Tendsto
      (fun T => truncatedInfiniteZeroContribution x T)
      atTop
      (nhds (infiniteZeroContribution x)) := by
  exact (infiniteZeroSpectralTerm_hasSum x).comp
    concreteZerosUpToHeightSubtype_tendsto_atTop

/-- In particular, the finite spectral truncations form a Cauchy sequence. -/
theorem truncatedInfiniteZeroContribution_cauchySeq
    (x : Nat) :
    CauchySeq (fun T => truncatedInfiniteZeroContribution x T) :=
  (truncatedInfiniteZeroContribution_tendsto x).cauchySeq

/-- The effective spectral remainder itself tends to zero. -/
theorem infiniteZeroContributionTail_tendsto_zero
    (x : Nat) :
    Tendsto
      (fun T => infiniteZeroContributionTail x T)
      atTop
      (nhds 0) := by
  have hDifference :
      (fun T =>
          infiniteZeroContribution x -
            truncatedInfiniteZeroContribution x T) =
        (fun T => infiniteZeroContributionTail x T) := by
    funext T
    have hSplit := truncated_add_infiniteZeroContributionTail x T
    rw [<- hSplit]
    abel
  rw [<- hDifference]
  have hConst :
      Tendsto
        (fun _ : Nat => infiniteZeroContribution x)
        atTop
        (nhds (infiniteZeroContribution x)) :=
    tendsto_const_nhds
  simpa using
    (hConst.sub (truncatedInfiniteZeroContribution_tendsto x))

/-- The historical TS257 truncation is the diagonal `x = T`. -/
theorem truncatedInfiniteZeroContribution_diagonal_eq_TS257
    (X : Nat) :
    truncatedInfiniteZeroContribution X X =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
        TS265.Goldbach.concreteFiniteHeightTruncationData X := by
  unfold truncatedInfiniteZeroContribution
    concreteZerosUpToHeightSubtype infiniteZeroSpectralTerm
  rw [Finset.sum_preimage]
  next =>
    exact (TS266.Goldbach.concreteFiniteHeightZeroTruncatedComplexSum_eq_sum X).symm
  next =>
    intro rho hRho hNotRange
    have hZero :=
      (TS265.Goldbach.mem_concreteFiniteHeightTruncation_iff X rho).mp hRho |>.1
    exfalso
    exact hNotRange (Exists.intro
      (Subtype.mk rho hZero)
      rfl)

/-- TS292 closes absolute convergence and the finite-to-infinite spectral
passage, but deliberately does not claim an explicit formula. -/
structure EffectiveInfiniteZeroTailConvergenceLedger where
  ts291_finite_zero_bound :
    TS291.Goldbach.LogLinearZeroContributionAssemblyLedger
  residual_tail_constant : Real
  residual_tail_constant_nonnegative :
    0 <= residual_tail_constant
  uniform_finite_tail :
    forall (T : Nat), 1 <= T ->
      forall s : Finset
        {rho : ConcreteNontrivialZero //
          Not (Membership.mem (concreteZerosUpToHeightSubtype T) rho)},
        Finset.sum s
            (fun rho =>
              TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) <=
          residual_tail_constant * logarithmicTailRate T
  absolute_summability :
    forall x : Nat, Summable (fun rho : ConcreteNontrivialZero =>
      norm (infiniteZeroSpectralTerm x rho))
  infinite_hasSum :
    forall x : Nat,
      HasSum (infiniteZeroSpectralTerm x) (infiniteZeroContribution x)
  effective_tail :
    forall (x T : Nat), 1 <= T ->
      norm
          (infiniteZeroContribution x -
            truncatedInfiniteZeroContribution x T) <=
        max 1 (x : Real) *
          (residual_tail_constant * logarithmicTailRate T)
  truncations_cauchy :
    forall x : Nat,
      CauchySeq (fun T => truncatedInfiniteZeroContribution x T)
  explicit_formula_not_proved : True
  contour_residual_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def effectiveInfiniteZeroTailConvergenceLedger :
    EffectiveInfiniteZeroTailConvergenceLedger where
  ts291_finite_zero_bound :=
    TS291.Goldbach.logLinearZeroContributionAssemblyLedger
  residual_tail_constant :=
    infiniteZeroResidualTailConstant
  residual_tail_constant_nonnegative :=
    infiniteZeroResidualTailConstant_nonnegative
  uniform_finite_tail :=
    finiteInfiniteZeroResidualTail_sum_le
  absolute_summability :=
    infiniteZeroSpectralTerm_norm_summable
  infinite_hasSum :=
    infiniteZeroSpectralTerm_hasSum
  effective_tail :=
    infiniteZeroContribution_sub_truncated_norm_le
  truncations_cauchy :=
    truncatedInfiniteZeroContribution_cauchySeq
  explicit_formula_not_proved := True.intro
  contour_residual_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def EffectiveInfiniteZeroTailConvergenceTarget : Prop :=
  Nonempty EffectiveInfiniteZeroTailConvergenceLedger

theorem effectiveInfiniteZeroTailConvergenceTarget :
    EffectiveInfiniteZeroTailConvergenceTarget :=
  Nonempty.intro effectiveInfiniteZeroTailConvergenceLedger

end Goldbach
end TS292
