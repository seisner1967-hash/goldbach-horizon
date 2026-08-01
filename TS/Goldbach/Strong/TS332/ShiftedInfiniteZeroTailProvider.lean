import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic
import TS.Goldbach.Strong.TS290.RiemannXiLogLinearZeroCounting
import TS.Goldbach.Strong.TS292.EffectiveInfiniteZeroTailConvergence
import TS.Goldbach.Strong.TS322.FiniteCoreEffectiveTail

namespace TS332
namespace Goldbach

noncomputable section

/-!
# TS332: shifted infinite-zero tail provider

This additive module retains the shifted Jensen envelope from TS290 until the
tail chain begins.  Above height two, the shifted envelope costs a factor two
instead of TS290's historical global factor four.  Replaying the existing
TS292 Abel transport therefore halves the residual constant without changing
the legacy TS290, TS292, or TS322 APIs.

No finite-zero payload, rational finite-core cap, or trace-budget certificate
is constructed here.
-/

/-! ## Shifted counting envelope -/

/-- The concrete count retains the shifted Jensen envelope before TS290's
global replacement by `4 * T * log (T + 2)`. -/
theorem concreteMultiplicityCountUpToHeight_le_shifted
    (T : Real)
    (hT : 0 <= T) :
    (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
      TS290.Goldbach.xiDyadicLogLinearConstant * (T + 1) *
        Real.log (T + 3) := by
  let hPos : 0 < T + 1 := by linarith
  have hNat :=
    TS290.Goldbach.concreteMultiplicityCountUpToHeight_le_xiDyadicCount
      T hT
  have hNatReal :
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
        (TS274.Goldbach.finiteJensenMultiplicityCount
          (TS290.Goldbach.xiDyadicDiskData (T + 1) hPos) : Real) := by
    exact_mod_cast hNat
  have hXi := TS290.Goldbach.xiDyadicMultiplicityCount_le_logLinear
    (T + 1) hPos (by linarith)
  exact hNatReal.trans (by
    simpa [show T + 1 + 2 = T + 3 by ring] using hXi)

/-- Above height two, the shifted envelope costs only a factor two relative
to the unshifted log-linear shape.  This estimate is uniform in `T`. -/
theorem shiftedLogProduct_le_two_logLinear
    (T : Real)
    (hT : 2 <= T) :
    (T + 1) * Real.log (T + 3) <=
      2 * T * Real.log (T + 2) := by
  have hT2Pos : 0 < T + 2 := by linarith
  have hLogNonnegative : 0 <= Real.log (T + 2) := by
    exact Real.log_nonneg (by linarith)
  have hLogThreeNonnegative : 0 <= Real.log (T + 3) := by
    exact Real.log_nonneg (by linarith)
  have hIncrement :
      Real.log (T + 3) - Real.log (T + 2) <= 1 / (T + 2) := by
    simpa only [show T + 2 + 1 = T + 3 by ring] using
      TS292.Goldbach.log_add_one_sub_log_le_inv (T + 2) hT2Pos
  have hInvQuarter : 1 / (T + 2) <= (1 : Real) / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hLogFour : Real.log 4 <= Real.log (T + 2) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num) hT2Pos (by linarith)
  have hLogFourEq : Real.log (4 : Real) = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hLogLower : (3 : Real) / 4 <= Real.log (T + 2) := by
    have hLogTwoLower : (0.6931471803 : Real) < Real.log 2 :=
      Real.log_two_gt_d9
    rw [hLogFourEq] at hLogFour
    linarith
  have hInvThirdLog :
      1 / (T + 2) <= Real.log (T + 2) / 3 := by
    linarith
  have hLogFactor :
      Real.log (T + 3) <= (4 : Real) / 3 * Real.log (T + 2) := by
    linarith
  have hLinearFactor : T + 1 <= (3 : Real) / 2 * T := by
    linarith
  calc
    (T + 1) * Real.log (T + 3) <=
        ((3 : Real) / 2 * T) *
          ((4 : Real) / 3 * Real.log (T + 2)) := by
      exact mul_le_mul hLinearFactor hLogFactor
        hLogThreeNonnegative (by positivity)
    _ = 2 * T * Real.log (T + 2) := by ring

/-- The concrete count has a local factor-two log-linear bound at every
height at least two. -/
theorem concreteMultiplicityCountUpToHeight_le_two_logLinear
    (T : Real)
    (hT : 2 <= T) :
    (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
      (2 * TS290.Goldbach.xiDyadicLogLinearConstant) * T *
        Real.log (T + 2) := by
  calc
    (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
        TS290.Goldbach.xiDyadicLogLinearConstant * (T + 1) *
          Real.log (T + 3) :=
      concreteMultiplicityCountUpToHeight_le_shifted T (by linarith)
    _ <= TS290.Goldbach.xiDyadicLogLinearConstant *
          (2 * T * Real.log (T + 2)) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left
          (shiftedLogProduct_le_two_logLinear T hT)
          TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
    _ = (2 * TS290.Goldbach.xiDyadicLogLinearConstant) * T *
          Real.log (T + 2) := by ring

/-! ## Uniform Abel transport -/

/-- Abel transport using the factor-two count only on the actual tail chain. -/
theorem tailIntegerShellMassSum_le_of_localTwoLogLinear
    (T K : Nat)
    (hT : 2 <= T) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        (TS292.Goldbach.tailIntegerHeight T) K <=
      TS273.Goldbach.logLinearMultiplicityCountEnvelope
            (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
            (TS292.Goldbach.tailIntegerHeight T K) *
          TS271.Goldbach.reciprocalSquareHeightWeight
            (TS292.Goldbach.tailIntegerHeight T) K +
        Finset.sum (Finset.range K)
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope
                (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
                (TS292.Goldbach.tailIntegerHeight T (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  (TS292.Goldbach.tailIntegerHeight T) n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  (TS292.Goldbach.tailIntegerHeight T) (n + 1))) := by
  have hTOne : 1 <= T := by omega
  have hHeight := TS292.Goldbach.tailIntegerHeight_positiveMonotone T hTOne
  apply le_trans
    (TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum_le_weightedCountSum
      (TS292.Goldbach.tailIntegerHeight T) hHeight K)
  rw [TS271.Goldbach.concreteHeightShellMultiplicityWeightedSum_eq_countDifferences
    (TS292.Goldbach.tailIntegerHeight T) hHeight K]
  exact TS271.Goldbach.finitePartialSummationBound
    (fun n =>
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight
        (TS292.Goldbach.tailIntegerHeight T n) : Real))
    (fun n =>
      TS273.Goldbach.logLinearMultiplicityCountEnvelope
        (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
        (TS292.Goldbach.tailIntegerHeight T n))
    (TS271.Goldbach.reciprocalSquareHeightWeight
      (TS292.Goldbach.tailIntegerHeight T))
    (fun _ => Nat.cast_nonneg _)
    (fun n => by
      change
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight
            (TS292.Goldbach.tailIntegerHeight T n) : Real) <=
          TS273.Goldbach.logLinearMultiplicityCountEnvelope
            (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
            (TS292.Goldbach.tailIntegerHeight T n)
      rw [TS292.Goldbach.logLinearEnvelope_tailIntegerHeight
        (2 * TS290.Goldbach.xiDyadicLogLinearConstant) T n hTOne]
      exact concreteMultiplicityCountUpToHeight_le_two_logLinear
        (TS292.Goldbach.tailIntegerHeight T n) (by
          unfold TS292.Goldbach.tailIntegerHeight
          exact_mod_cast hT.trans (Nat.le_add_right T n)))
    (TS271.Goldbach.reciprocalSquareHeightWeight_nonnegative
      (TS292.Goldbach.tailIntegerHeight T))
    (TS271.Goldbach.reciprocalSquareHeightWeight_antitone
      (TS292.Goldbach.tailIntegerHeight T) hHeight)
    K

/-- The shifted TS290 route halves the current TS292 residual constant,
uniformly in the finite upper cutoff. -/
theorem shiftedTailIntegerShellMassSum_le_logarithmicRate
    (T K : Nat)
    (hT : 2 <= T) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        (TS292.Goldbach.tailIntegerHeight T) K <=
      30 * TS290.Goldbach.xiDyadicLogLinearConstant *
        TS292.Goldbach.logarithmicTailRate T := by
  have hTOne : 1 <= T := by omega
  have hC :
      0 <= 2 * TS290.Goldbach.xiDyadicLogLinearConstant :=
    mul_nonneg (by norm_num)
      TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
  have hTransport :=
    tailIntegerShellMassSum_le_of_localTwoLogLinear T K hT
  have hTerminal := TS292.Goldbach.logLinearTailAbelTerminal_le_potential
    (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
    hC T hTOne K
  have hSum :
      Finset.sum (Finset.range K)
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope
                (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
                (TS292.Goldbach.tailIntegerHeight T (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  (TS292.Goldbach.tailIntegerHeight T) n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  (TS292.Goldbach.tailIntegerHeight T) (n + 1))) <=
        8 * TS290.Goldbach.xiDyadicLogLinearConstant *
          TS292.Goldbach.logarithmicTailPotential (T : Real) := by
    calc
      Finset.sum (Finset.range K)
          (fun n =>
            TS273.Goldbach.logLinearMultiplicityCountEnvelope
                (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
                (TS292.Goldbach.tailIntegerHeight T (n + 1)) *
              (TS271.Goldbach.reciprocalSquareHeightWeight
                  (TS292.Goldbach.tailIntegerHeight T) n -
                TS271.Goldbach.reciprocalSquareHeightWeight
                  (TS292.Goldbach.tailIntegerHeight T) (n + 1))) <=
        Finset.sum (Finset.range K)
          (fun n =>
            4 * (2 * TS290.Goldbach.xiDyadicLogLinearConstant) *
              (TS292.Goldbach.logarithmicTailPotential
                  (TS292.Goldbach.tailIntegerHeight T n) -
                TS292.Goldbach.logarithmicTailPotential
                  (TS292.Goldbach.tailIntegerHeight T (n + 1)))) := by
        apply Finset.sum_le_sum
        intro n _
        exact TS292.Goldbach.logLinearTailAbelSummand_le_potentialDrop
          (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
          hC T hTOne n
      _ = 8 * TS290.Goldbach.xiDyadicLogLinearConstant *
          (TS292.Goldbach.logarithmicTailPotential (T : Real) -
            TS292.Goldbach.logarithmicTailPotential
              (TS292.Goldbach.tailIntegerHeight T K)) := by
        rw [<- Finset.mul_sum, Finset.sum_range_sub']
        have hZero :
            TS292.Goldbach.tailIntegerHeight T 0 = (T : Real) := by
          simp [TS292.Goldbach.tailIntegerHeight]
        rw [hZero]
        ring
      _ <= 8 * TS290.Goldbach.xiDyadicLogLinearConstant *
          TS292.Goldbach.logarithmicTailPotential (T : Real) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_self _
            (TS292.Goldbach.logarithmicTailPotential_nonnegative
              (TS292.Goldbach.tailIntegerHeight T K) (by
                unfold TS292.Goldbach.tailIntegerHeight
                exact_mod_cast hTOne.trans (Nat.le_add_right T K))))
          (mul_nonneg (by norm_num)
            TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative)
  have hPotential :=
    TS292.Goldbach.logarithmicTailPotential_le_three_rate T hTOne
  calc
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
          (TS292.Goldbach.tailIntegerHeight T) K <=
        TS273.Goldbach.logLinearMultiplicityCountEnvelope
              (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
              (TS292.Goldbach.tailIntegerHeight T K) *
            TS271.Goldbach.reciprocalSquareHeightWeight
              (TS292.Goldbach.tailIntegerHeight T) K +
          Finset.sum (Finset.range K)
            (fun n =>
              TS273.Goldbach.logLinearMultiplicityCountEnvelope
                  (2 * TS290.Goldbach.xiDyadicLogLinearConstant)
                  (TS292.Goldbach.tailIntegerHeight T (n + 1)) *
                (TS271.Goldbach.reciprocalSquareHeightWeight
                    (TS292.Goldbach.tailIntegerHeight T) n -
                  TS271.Goldbach.reciprocalSquareHeightWeight
                    (TS292.Goldbach.tailIntegerHeight T) (n + 1))) := hTransport
    _ <= 10 * TS290.Goldbach.xiDyadicLogLinearConstant *
          TS292.Goldbach.logarithmicTailPotential (T : Real) := by
      nlinarith
    _ <= 10 * TS290.Goldbach.xiDyadicLogLinearConstant *
          (3 * TS292.Goldbach.logarithmicTailRate T) := by
      exact mul_le_mul_of_nonneg_left hPotential
        (mul_nonneg (by norm_num)
          TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative)
    _ = 30 * TS290.Goldbach.xiDyadicLogLinearConstant *
          TS292.Goldbach.logarithmicTailRate T := by ring

/-- Shifted shell bound for an arbitrary natural upper height. -/
theorem concreteHeightShellReciprocalSquareMass_le_shiftedRate
    (T U : Nat)
    (hT : 2 <= T) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMass
        (T : Real) (U : Real) <=
      30 * TS290.Goldbach.xiDyadicLogLinearConstant *
        TS292.Goldbach.logarithmicTailRate T := by
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
        TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative)
      (div_nonneg
        (add_nonneg
          (Real.log_nonneg (by
            have hTReal : (1 : Real) <= (T : Real) := by
              exact_mod_cast (show 1 <= T by omega)
            linarith))
          (by norm_num))
        (by positivity))
  case neg =>
    have hTU : T <= U := Nat.le_of_lt (lt_of_not_ge hUT)
    have hEq :
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass
            (T : Real) (U : Real) =
          TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
            (TS292.Goldbach.tailIntegerHeight T) (U - T) := by
      rw [TS292.Goldbach.tailIntegerShellMassSum_telescope]
      simp [Nat.add_sub_of_le hTU]
    rw [hEq]
    exact shiftedTailIntegerShellMassSum_le_logarithmicRate T (U - T) hT

/-! ## Shifted infinite residual family -/

/-- Explicit shifted residual constant. -/
noncomputable def shiftedInfiniteZeroResidualTailConstant : Real :=
  30 * TS290.Goldbach.xiDyadicLogLinearConstant

theorem shiftedInfiniteZeroResidualTailConstant_nonnegative :
    0 <= shiftedInfiniteZeroResidualTailConstant := by
  unfold shiftedInfiniteZeroResidualTailConstant
  exact mul_nonneg (by norm_num)
    TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative

/-- Every finite residual tail has the shifted bound, independently of its
upper height. -/
theorem finiteInfiniteZeroResidualTail_sum_le_shifted
    (T : Nat)
    (hT : 2 <= T)
    (s : Finset
      {rho : TS292.Goldbach.ConcreteNontrivialZero //
        Not (Membership.mem
          (TS292.Goldbach.concreteZerosUpToHeightSubtype T) rho)}) :
    Finset.sum s
        (fun rho =>
          TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) <=
      shiftedInfiniteZeroResidualTailConstant *
        TS292.Goldbach.logarithmicTailRate T := by
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
        ((TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff T z.1).mpr
          hLower)
    have hCeil :
        abs z.1.1.im <= ((Nat.ceil (abs z.1.1.im) : Nat) : Real) :=
      Nat.le_ceil _
    have hSup :
        Nat.ceil (abs z.1.1.im) <=
          s.sup (fun w => Nat.ceil (abs w.1.1.im)) :=
      Finset.le_sup (f := fun w => Nat.ceil (abs w.1.1.im)) hz
    have hUpperNat : Nat.ceil (abs z.1.1.im) <= U :=
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
          (fun rho => TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) := by
    exact Finset.sum_image
      (fun a _ b _ hab => by exact Subtype.ext (Subtype.ext hab))
  rw [<- hImageSum]
  calc
    Finset.sum values TS269.Goldbach.highImaginaryResidualEnvelope <=
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass
          (T : Real) (U : Real) := by
      unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun rho _ _ =>
          TS269.Goldbach.highImaginaryResidualEnvelope_nonnegative rho)
    _ <= 30 * TS290.Goldbach.xiDyadicLogLinearConstant *
          TS292.Goldbach.logarithmicTailRate T :=
      concreteHeightShellReciprocalSquareMass_le_shiftedRate T U hT
    _ = shiftedInfiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate T := rfl

/-- The shifted residual family is summable above every height at least two. -/
theorem shiftedInfiniteZeroResidualTail_summable
    (T : Nat)
    (hT : 2 <= T) :
    Summable
      (fun rho :
        {rho : TS292.Goldbach.ConcreteNontrivialZero //
          Not (Membership.mem
            (TS292.Goldbach.concreteZerosUpToHeightSubtype T) rho)} =>
        TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) :=
  summable_of_sum_le
    (fun rho =>
      TS269.Goldbach.highImaginaryResidualEnvelope_nonnegative rho.1.1)
    (finiteInfiniteZeroResidualTail_sum_le_shifted T hT)

/-- Full infinite residual mass under the shifted route. -/
theorem shiftedInfiniteZeroResidualTail_tsum_le
    (T : Nat)
    (hT : 2 <= T) :
    tsum
        (fun rho :
          {rho : TS292.Goldbach.ConcreteNontrivialZero //
            Not (Membership.mem
              (TS292.Goldbach.concreteZerosUpToHeightSubtype T) rho)} =>
          TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) <=
      shiftedInfiniteZeroResidualTailConstant *
        TS292.Goldbach.logarithmicTailRate T :=
  tsum_le_of_sum_le
    (shiftedInfiniteZeroResidualTail_summable T hT)
    (finiteInfiniteZeroResidualTail_sum_le_shifted T hT)

/-! ## Public TS322 coefficient-tail provider -/

/-- Uniform finite norm-tail bound with independent arithmetic scale `x`. -/
theorem finiteInfiniteZeroSpectralTail_norm_sum_le_shifted
    (x T : Nat)
    (hT : 2 <= T)
    (s : Finset
      {rho : TS292.Goldbach.ConcreteNontrivialZero //
        Not (Membership.mem
          (TS292.Goldbach.concreteZerosUpToHeightSubtype T) rho)}) :
    Finset.sum s
        (fun rho =>
          norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho.1)) <=
      max 1 (x : Real) *
        (shiftedInfiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate T) := by
  have hPointwise :
      forall rho :
          {rho : TS292.Goldbach.ConcreteNontrivialZero //
            Not (Membership.mem
              (TS292.Goldbach.concreteZerosUpToHeightSubtype T) rho)},
        norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho.1) <=
          max 1 (x : Real) *
            TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1 := by
    intro rho
    have hNotLe :
        Not (abs rho.1.1.im <= (T : Real)) := by
      intro hLe
      exact rho.property
        ((TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff T rho.1).mpr
          hLe)
    have hHigh : 1 <= abs rho.1.1.im := by
      have hTReal : (1 : Real) <= (T : Real) := by
        exact_mod_cast (show 1 <= T by omega)
      exact hTReal.trans (le_of_lt (lt_of_not_ge hNotLe))
    exact TS292.Goldbach.infiniteZeroSpectralTerm_norm_le_scale_mul_residual
      x rho.1 hHigh
  calc
    Finset.sum s
          (fun rho =>
            norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho.1)) <=
        Finset.sum s
          (fun rho =>
            max 1 (x : Real) *
              TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) := by
      apply Finset.sum_le_sum
      intro rho _
      exact hPointwise rho
    _ = max 1 (x : Real) *
          Finset.sum s
            (fun rho =>
              TS269.Goldbach.highImaginaryResidualEnvelope rho.1.1) := by
      rw [Finset.mul_sum]
    _ <= max 1 (x : Real) *
          (shiftedInfiniteZeroResidualTailConstant *
            TS292.Goldbach.logarithmicTailRate T) := by
      exact mul_le_mul_of_nonneg_left
        (finiteInfiniteZeroResidualTail_sum_le_shifted T hT s)
        (zero_le_one.trans (le_max_left 1 (x : Real)))

/-- TS322's exact coefficient tail inherits the shifted explicit bound. -/
theorem linearCoefficientTailMass_le_shifted
    (H : Nat)
    (hH : 2 <= H) :
    TS322.Goldbach.linearCoefficientTailMass H <=
      shiftedInfiniteZeroResidualTailConstant *
        TS292.Goldbach.logarithmicTailRate H := by
  have hSummable := TS322.Goldbach.linearCoefficientTailMass_summable H
  apply tsum_le_of_sum_le hSummable
  intro s
  have hTail :=
    finiteInfiniteZeroSpectralTail_norm_sum_le_shifted 1 H hH s
  simpa [TS322.Goldbach.CoefficientTailIndex,
    TS315.Goldbach.truncatedZeroSet,
    TS316.Goldbach.zeroCoefficientMagnitude] using hTail

/-- The robust TS322 error also inherits the shifted coefficient-tail bound. -/
theorem effectiveWeightedTailError_le_shifted
    (H : Nat)
    (hH : 2 <= H) :
    TS322.Goldbach.effectiveWeightedTailError H <=
      2 * TS316.Goldbach.globalLinearSpectralMass *
        (shiftedInfiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate H) := by
  unfold TS322.Goldbach.effectiveWeightedTailError
  exact mul_le_mul_of_nonneg_left
    (linearCoefficientTailMass_le_shifted H hH)
    (mul_nonneg (by norm_num)
      TS316.Goldbach.globalLinearSpectralMass_nonnegative)

/-! ## Exact rational specialization at the reference height -/

/-- A compact exact lower bound for `exp 3`. -/
theorem twenty_lt_exp_three : (20 : Real) < Real.exp 3 := by
  let d : Real := 2.7182818283
  have hdPos : 0 <= d := by norm_num [d]
  have hd : d < Real.exp 1 := by
    simpa [d] using Real.exp_one_gt_d9
  have hPow : d ^ 3 < Real.exp 1 ^ 3 := by
    gcongr
  have hExact : (20 : Real) < d ^ 3 := by norm_num [d]
  have hExp : Real.exp 3 = Real.exp 1 ^ 3 := by
    convert Real.exp_nat_mul (1 : Real) 3 using 1
    norm_num
  rw [hExp]
  exact hExact.trans hPow

/-- Rational outer bound for the theta geometric constant. -/
theorem completedZetaThetaTailConstant_le_forty_div_nineteen :
    TS289.Goldbach.completedZetaThetaTailConstant <= (40 : Real) / 19 := by
  have hExpNegThree : Real.exp (-3) < (1 : Real) / 20 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      one_div_lt_one_div_of_lt (by norm_num) twenty_lt_exp_three
  have hExpNegPi : Real.exp (-Real.pi) < (1 : Real) / 20 := by
    have hArg : -Real.pi < (-3 : Real) := by
      linarith [Real.pi_gt_three]
    exact (Real.exp_lt_exp.mpr hArg).trans hExpNegThree
  have hDenPos : 0 < 1 - Real.exp (-Real.pi) := by linarith
  unfold TS289.Goldbach.completedZetaThetaTailConstant
  apply (mul_le_mul_right hDenPos).mp
  field_simp
  nlinarith

theorem xiDyadicLogLinearConstant_le_six_ninety_two_div_nineteen :
    TS290.Goldbach.xiDyadicLogLinearConstant <= (692 : Real) / 19 := by
  unfold TS290.Goldbach.xiDyadicLogLinearConstant
  nlinarith [completedZetaThetaTailConstant_le_forty_div_nineteen]

theorem shiftedInfiniteZeroResidualTailConstant_le :
    shiftedInfiniteZeroResidualTailConstant <= (20760 : Real) / 19 := by
  unfold shiftedInfiniteZeroResidualTailConstant
  nlinarith [xiDyadicLogLinearConstant_le_six_ninety_two_div_nineteen]

/-- Exact lower bound for `exp 14`, sufficient at the reference height. -/
theorem height_plus_two_lt_exp_fourteen :
    (1132492 : Real) < Real.exp 14 := by
  let d : Real := 2.7182818283
  have hdPos : 0 <= d := by norm_num [d]
  have hd : d < Real.exp 1 := by
    simpa [d] using Real.exp_one_gt_d9
  have hPow : d ^ 14 < Real.exp 1 ^ 14 := by
    gcongr
  have hExact : (1132492 : Real) < d ^ 14 := by norm_num [d]
  have hExp : Real.exp 14 = Real.exp 1 ^ 14 := by
    convert Real.exp_nat_mul (1 : Real) 14 using 1
    norm_num
  rw [hExp]
  exact hExact.trans hPow

theorem log_height_plus_two_lt_fourteen :
    Real.log (1132492 : Real) < 14 := by
  exact (Real.log_lt_iff_lt_exp (by norm_num)).2
    height_plus_two_lt_exp_fourteen

/-- Rational residual bound at `H = 1132490`. -/
theorem shiftedResidualAtReferenceHeight_le :
    shiftedInfiniteZeroResidualTailConstant *
        TS292.Goldbach.logarithmicTailRate 1132490 <=
      (31140 : Real) / 2151731 := by
  have hRate :
      TS292.Goldbach.logarithmicTailRate 1132490 <=
        (15 : Real) / 1132490 := by
    unfold TS292.Goldbach.logarithmicTailRate
    norm_num only [Nat.cast_ofNat]
    rw [show (3 : Real) / 226498 = 15 / 1132490 by norm_num]
    exact div_le_div_of_nonneg_right
      (by linarith [log_height_plus_two_lt_fourteen]) (by norm_num)
  calc
    shiftedInfiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate 1132490 <=
        ((20760 : Real) / 19) * ((15 : Real) / 1132490) := by
      exact mul_le_mul shiftedInfiniteZeroResidualTailConstant_le hRate
        (by
          unfold TS292.Goldbach.logarithmicTailRate
          positivity)
        (by positivity)
    _ = (31140 : Real) / 2151731 := by norm_num

/-- Exact TS322 coefficient-tail specialization at `H = 1132490`. -/
theorem linearCoefficientTailMass_referenceHeight_le :
    TS322.Goldbach.linearCoefficientTailMass 1132490 <=
      (31140 : Real) / 2151731 := by
  exact (linearCoefficientTailMass_le_shifted 1132490 (by norm_num)).trans
    shiftedResidualAtReferenceHeight_le

end

end Goldbach
end TS332
