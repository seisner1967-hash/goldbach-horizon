import Mathlib.Tactic
import TS.Goldbach.Strong.TS301.AnchoredMacroscopicXiQuotient

/-!
# TS302 - Finite Macroscopic Correction Decay

TS301 expressed the logarithmic derivative of the historical height quotient
as the logarithmic derivative of an anchored macroscopic quotient plus the
difference of two finite rational zero sums.  This sprint identifies that
difference with the sum over an explicit finite set of additional zeros.

The nearby height zeros are first embedded into the macroscopic factor set,
with exact multiplicity compatibility.  Every additional zero then has
ordinate strictly above `T + 2`, while the TS299 contour height lies below
`T + 1`.  Consequently every additional denominator on either horizontal
side has norm greater than one.  The correction is bounded by its total
macroscopic multiplicity, which is in turn injected into a larger TS290
dyadic disk and bounded by a closed log-linear envelope.

After division by the quadratic Mellin kernel scale, this envelope tends to
zero.  No local zero-density estimate, RH, infinite product, or macroscopic
quotient-envelope rate is used.
-/

noncomputable section

namespace TS302
namespace Goldbach

open Complex Filter Metric Set Topology
open scoped BigOperators Topology

/-! ## Exact finite reindexing -/

/-- Complex values of the nearby height-zero finset used by TS295. -/
noncomputable def heightZeroValues (T : Nat) : Finset Complex :=
  (TS295.Goldbach.nearbyConcreteZeros T).image Subtype.val

theorem mem_heightZeroValues_iff
    (T : Nat)
    (z : Complex) :
    Iff (Membership.mem (heightZeroValues T) z)
      (Exists fun rho : TS292.Goldbach.ConcreteNontrivialZero =>
        Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho /\
          rho.1 = z) := by
  classical
  simp [heightZeroValues]

/-- Every nearby height zero is selected by the macroscopic factorization. -/
theorem nearbyConcreteZero_mem_macroscopicFactorZeros
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    Membership.mem (TS301.Goldbach.xiMacroscopicSpec T).factorZeros rho.1 := by
  apply (TS301.Goldbach.xiMacroscopicSpec T).innerZeros_subset_factorZeros
  change Membership.mem
    (TS283.Goldbach.riemannXiCandidateZerosInClosedBall
      (TS301.Goldbach.xiMacroscopicInnerRadius T)) rho.1
  rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
  have hHeight : _root_.abs rho.1.im <= (T : Real) + 2 := by
    simpa using
      ((TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff (T + 2) rho).mp
        hRho)
  have hTruncated :
      TS265.Goldbach.heightTruncatedZeroSet ((T : Real) + 2) rho.1 :=
    And.intro rho.property (by simpa using hHeight)
  have hCompact :=
    TS265.Goldbach.heightTruncatedZeroSet_subset_compact_inter
      ((T : Real) + 2) hTruncated
  have hNorm : Complex.abs rho.1 <= ((T : Real) + 2) + 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hCompact.1
  have hRadius : ((T : Real) + 2) + 1 <
      TS301.Goldbach.xiMacroscopicInnerRadius T := by
    unfold TS301.Goldbach.xiMacroscopicInnerRadius
    nlinarith [(Nat.cast_nonneg T : (0 : Real) <= (T : Real))]
  have hXi : TS282.Goldbach.riemannXiCandidate rho.1 = 0 := by
    exact TS290.Goldbach.concreteNontrivialRiemannZetaZero_is_xi_zero rho.property
  exact And.intro (hNorm.trans hRadius.le) hXi

theorem heightZeroValues_subset_macroscopicFactorZeros
    (T : Nat) :
    heightZeroValues T <= (TS301.Goldbach.xiMacroscopicSpec T).factorZeros := by
  intro z hz
  let rho := Classical.choose ((mem_heightZeroValues_iff T z).mp hz)
  have hRho := Classical.choose_spec ((mem_heightZeroValues_iff T z).mp hz)
  rw [<- hRho.2]
  exact nearbyConcreteZero_mem_macroscopicFactorZeros T rho hRho.1

/-- The two finite families use exactly the same analytic multiplicity. -/
theorem macroscopicMultiplicity_eq_concreteZeroMultiplicity
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho.1 =
      TS295.Goldbach.concreteZeroMultiplicity rho := by
  change TS284.Goldbach.riemannXiCandidateMultiplicity rho.1 =
    TS264.Goldbach.concreteRiemannZetaMultiplicity rho.1
  exact
    (TS290.Goldbach.concreteRiemannZetaMultiplicity_eq_riemannXiCandidateMultiplicity
      rho.property).symm

/-- The historical height sum rewritten on its complex-valued image. -/
theorem finiteZeroLogDerivativeSum_eq_sum_heightZeroValues
    (T : Nat)
    (s : Complex) :
    TS295.Goldbach.finiteZeroLogDerivativeSum T s =
      Finset.sum (heightZeroValues T)
        (fun rho =>
          (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
            (s - rho)) := by
  classical
  unfold TS295.Goldbach.finiteZeroLogDerivativeSum
    TS295.Goldbach.finiteZeroLogDerivativeTerm
  have hImageSum :
      Finset.sum (heightZeroValues T)
          (fun rho =>
            (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
              (s - rho)) =
        Finset.sum (TS295.Goldbach.nearbyConcreteZeros T)
          (fun rho =>
            (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho.1 /
              (s - rho.1)) := by
    unfold heightZeroValues
    exact Finset.sum_image
      (fun a _ b _ hab => Subtype.val_injective hab)
  rw [hImageSum]
  apply Finset.sum_congr rfl
  intro rho _
  rw [macroscopicMultiplicity_eq_concreteZeroMultiplicity]

/-- Zeros selected macroscopically but absent from the height truncation. -/
noncomputable def xiMacroscopicExtraZeros (T : Nat) : Finset Complex :=
  (TS301.Goldbach.xiMacroscopicSpec T).factorZeros \ heightZeroValues T

/-- The TS301 finite correction is exactly the rational sum over extra zeros. -/
theorem xiMacroscopicHeightFiniteCorrection_eq_sum_extraZeros
    (T : Nat)
    (s : Complex) :
    TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s =
      Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
            (s - rho)) := by
  classical
  unfold TS301.Goldbach.xiMacroscopicHeightFiniteCorrection
    TS301.Goldbach.xiMacroscopicFiniteZeroLogDerivativeSum
    xiMacroscopicExtraZeros
  rw [finiteZeroLogDerivativeSum_eq_sum_heightZeroValues]
  rw [<- Finset.sum_sdiff (heightZeroValues_subset_macroscopicFactorZeros T)]
  ring

/-! ## Extra-zero separation from the Perron height -/

theorem mem_xiMacroscopicExtraZeros_iff
    (T : Nat)
    (rho : Complex) :
    Iff (Membership.mem (xiMacroscopicExtraZeros T) rho)
      (Membership.mem (TS301.Goldbach.xiMacroscopicSpec T).factorZeros rho /\
        Not (Membership.mem (heightZeroValues T) rho)) := by
  classical
  simp [xiMacroscopicExtraZeros]

/-- Every additional macroscopic root lies strictly above height `T + 2`. -/
theorem xiMacroscopicExtraZero_abs_im_gt
    (T : Nat)
    (rho : Complex)
    (hRho : Membership.mem (xiMacroscopicExtraZeros T) rho) :
    (T : Real) + 2 < _root_.abs rho.im := by
  have hParts := (mem_xiMacroscopicExtraZeros_iff T rho).mp hRho
  have hXiZero :=
    (TS301.Goldbach.xiMacroscopicSpec T).factor_zero_is_xi_zero rho hParts.1
  have hConcrete := TS296.Goldbach.riemannXiCandidate_zero_is_concrete hXiZero
  let rhoC : TS292.Goldbach.ConcreteNontrivialZero :=
    { val := rho
      property := hConcrete }
  by_contra hNot
  have hHeight : _root_.abs rhoC.1.im <= ((T + 2 : Nat) : Real) := by
    dsimp [rhoC]
    push_neg at hNot
    simpa using hNot
  have hNearby : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rhoC := by
    exact
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff (T + 2) rhoC).mpr
        hHeight
  apply hParts.2
  exact (mem_heightZeroValues_iff T rho).mpr
    (Exists.intro rhoC (And.intro hNearby rfl))

theorem xiMacroscopicExtraZero_gap_gt_one
    (T : Nat)
    (rho : Complex)
    (hRho : Membership.mem (xiMacroscopicExtraZeros T) rho) :
    1 < _root_.abs
      (TS299.Goldbach.finiteGridStrongTau T - _root_.abs rho.im) := by
  have hHeight := xiMacroscopicExtraZero_abs_im_gt T rho hRho
  have hTau := TS299.Goldbach.finiteGridStrongTau_lt T
  have hDiff :
      TS299.Goldbach.finiteGridStrongTau T - _root_.abs rho.im < -1 := by
    linarith
  rw [_root_.abs_of_neg (hDiff.trans (by norm_num))]
  linarith

theorem xiMacroscopicExtraZero_denominator_norm_gt_one_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (rho : Complex)
    (hRho : Membership.mem (xiMacroscopicExtraZeros T) rho) :
    1 < norm (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma - rho) := by
  have hParts := (mem_xiMacroscopicExtraZeros_iff T rho).mp hRho
  have hXiZero :=
    (TS301.Goldbach.xiMacroscopicSpec T).factor_zero_is_xi_zero rho hParts.1
  let rhoC : TS292.Goldbach.ConcreteNontrivialZero :=
    { val := rho
      property := TS296.Goldbach.riemannXiCandidate_zero_is_concrete hXiZero }
  have hGap := xiMacroscopicExtraZero_gap_gt_one T rho hRho
  have hNorm := TS295.Goldbach.symmetricZeroHeightGap_le_norm_top
    sigma (TS299.Goldbach.finiteGridStrongTau T)
    (TS299.Goldbach.finiteGridStrongTau_pos hT).le rhoC
  unfold TS295.Goldbach.symmetricZeroHeightGap at hNorm
  simpa [rhoC, TS300.Goldbach.finiteGridTopHorizontalPoint] using
    hGap.trans_le hNorm

theorem xiMacroscopicExtraZero_denominator_norm_gt_one_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (rho : Complex)
    (hRho : Membership.mem (xiMacroscopicExtraZeros T) rho) :
    1 < norm (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma - rho) := by
  have hParts := (mem_xiMacroscopicExtraZeros_iff T rho).mp hRho
  have hXiZero :=
    (TS301.Goldbach.xiMacroscopicSpec T).factor_zero_is_xi_zero rho hParts.1
  let rhoC : TS292.Goldbach.ConcreteNontrivialZero :=
    { val := rho
      property := TS296.Goldbach.riemannXiCandidate_zero_is_concrete hXiZero }
  have hGap := xiMacroscopicExtraZero_gap_gt_one T rho hRho
  have hNorm := TS295.Goldbach.symmetricZeroHeightGap_le_norm_bottom
    sigma (TS299.Goldbach.finiteGridStrongTau T)
    (TS299.Goldbach.finiteGridStrongTau_pos hT).le rhoC
  unfold TS295.Goldbach.symmetricZeroHeightGap at hNorm
  simpa [rhoC, TS300.Goldbach.finiteGridBottomHorizontalPoint] using
    hGap.trans_le hNorm

/-- Total analytic multiplicity selected by the macroscopic factor set. -/
noncomputable def xiMacroscopicFactorMultiplicityCount (T : Nat) : Nat :=
  Finset.sum (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
    (TS301.Goldbach.xiMacroscopicSpec T).multiplicity

theorem xiMacroscopicHeightFiniteCorrection_norm_le_count_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      (xiMacroscopicFactorMultiplicityCount T : Real) := by
  classical
  rw [xiMacroscopicHeightFiniteCorrection_eq_sum_extraZeros]
  calc
    norm (Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
            (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma - rho))) <=
      Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          norm
            ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
              (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma - rho))) :=
        norm_sum_le _ _
    _ <= Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real)) := by
      apply Finset.sum_le_sum
      intro rho hRho
      rw [norm_div]
      simp only [Complex.norm_natCast]
      have hDen :=
        (xiMacroscopicExtraZero_denominator_norm_gt_one_top
          T hT sigma rho hRho).le
      calc
        ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real) /
              norm (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma - rho) <=
            ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real) / 1 :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hDen
        _ = ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real) := by
          ring
    _ <= Finset.sum (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        (fun rho =>
          ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro rho hRho
          exact (Finset.mem_sdiff.mp hRho).1)
      intro rho _ _
      exact Nat.cast_nonneg _
    _ = (xiMacroscopicFactorMultiplicityCount T : Real) := by
      simp [xiMacroscopicFactorMultiplicityCount]

theorem xiMacroscopicHeightFiniteCorrection_norm_le_count_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      (xiMacroscopicFactorMultiplicityCount T : Real) := by
  classical
  rw [xiMacroscopicHeightFiniteCorrection_eq_sum_extraZeros]
  calc
    norm (Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
            (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma - rho))) <=
      Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          norm
            ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho /
              (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma - rho))) :=
        norm_sum_le _ _
    _ <= Finset.sum (xiMacroscopicExtraZeros T)
        (fun rho =>
          ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real)) := by
      apply Finset.sum_le_sum
      intro rho hRho
      rw [norm_div]
      simp only [Complex.norm_natCast]
      have hDen :=
        (xiMacroscopicExtraZero_denominator_norm_gt_one_bottom
          T hT sigma rho hRho).le
      calc
        ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real) /
              norm (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma - rho) <=
            ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real) / 1 :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hDen
        _ = ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real) := by
          ring
    _ <= Finset.sum (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        (fun rho =>
          ((TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho : Real)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro rho hRho
          exact (Finset.mem_sdiff.mp hRho).1)
      intro rho _ _
      exact Nat.cast_nonneg _
    _ = (xiMacroscopicFactorMultiplicityCount T : Real) := by
      simp [xiMacroscopicFactorMultiplicityCount]

/-! ## Closed TS290 multiplicity envelope -/

/-- A second dyadic radius containing every macroscopic factor root. -/
noncomputable def xiMacroscopicCorrectionCountingRadius (T : Nat) : Real :=
  4 * TS301.Goldbach.xiMacroscopicInnerRadius T

theorem xiMacroscopicCorrectionCountingRadius_pos (T : Nat) :
    0 < xiMacroscopicCorrectionCountingRadius T := by
  unfold xiMacroscopicCorrectionCountingRadius
    TS301.Goldbach.xiMacroscopicInnerRadius
  positivity

theorem xiDyadicAnalyticRadius_lt_four_mul
    (r : Real)
    (hr : 0 < r) :
    (TS290.Goldbach.xiDyadicFiniteZeroGeometryData r hr).config.analyticRadius <
      4 * r := by
  change
    (TS283.Goldbach.xiZeroRadiusBarrier r (4 * r) + 2 * (4 * r)) / 3 <
      4 * r
  have hrFour : r < 4 * r := by linarith
  have hBarrier := TS283.Goldbach.xiZeroRadiusBarrier_lt hrFour
  linarith

theorem xiMacroscopicSpec_analyticRadius_lt_countingRadius
    (T : Nat) :
    (TS301.Goldbach.xiMacroscopicSpec T).config.analyticRadius <
      xiMacroscopicCorrectionCountingRadius T := by
  change
    (TS290.Goldbach.xiDyadicFiniteZeroGeometryData
      (TS301.Goldbach.xiMacroscopicInnerRadius T)
      (TS301.Goldbach.xiMacroscopicInnerRadius_pos T)).config.analyticRadius <
        4 * TS301.Goldbach.xiMacroscopicInnerRadius T
  exact xiDyadicAnalyticRadius_lt_four_mul
    (TS301.Goldbach.xiMacroscopicInnerRadius T)
    (TS301.Goldbach.xiMacroscopicInnerRadius_pos T)

theorem macroscopicFactorZeros_subset_countingDiskZeros
    (T : Nat) :
    (TS301.Goldbach.xiMacroscopicSpec T).factorZeros <=
      (TS290.Goldbach.xiDyadicDiskData
        (xiMacroscopicCorrectionCountingRadius T)
        (xiMacroscopicCorrectionCountingRadius_pos T)).zeros := by
  intro rho hRho
  rw [TS290.Goldbach.xiDyadicDiskData_zeros]
  rw [TS283.Goldbach.mem_riemannXiCandidateZerosInClosedBall_iff]
  have hOpen :=
    (TS301.Goldbach.xiMacroscopicSpec T).factor_zero_mem_open_disk rho hRho
  rw [(TS301.Goldbach.xiMacroscopicSpec T).center_eq_zero] at hOpen
  have hAbs : Complex.abs rho <
      (TS301.Goldbach.xiMacroscopicSpec T).config.averagingRadius := by
    simpa [Metric.mem_ball, dist_zero_right, Complex.norm_eq_abs] using hOpen
  have hAbsCount : Complex.abs rho < xiMacroscopicCorrectionCountingRadius T :=
    (hAbs.trans
      (TS301.Goldbach.xiMacroscopicSpec T).config.averagingRadius_lt_analyticRadius).trans
        (xiMacroscopicSpec_analyticRadius_lt_countingRadius T)
  exact And.intro hAbsCount.le
    ((TS301.Goldbach.xiMacroscopicSpec T).factor_zero_is_xi_zero rho hRho)

theorem xiMacroscopicFactorMultiplicityCount_le_dyadicCount
    (T : Nat) :
    xiMacroscopicFactorMultiplicityCount T <=
      TS274.Goldbach.finiteJensenMultiplicityCount
        (TS290.Goldbach.xiDyadicDiskData
          (xiMacroscopicCorrectionCountingRadius T)
          (xiMacroscopicCorrectionCountingRadius_pos T)) := by
  unfold xiMacroscopicFactorMultiplicityCount
    TS274.Goldbach.finiteJensenMultiplicityCount
  rw [TS290.Goldbach.xiDyadicDiskData_multiplicity]
  change
    Finset.sum (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        TS284.Goldbach.riemannXiCandidateMultiplicity <=
      Finset.sum
        (TS290.Goldbach.xiDyadicDiskData
          (xiMacroscopicCorrectionCountingRadius T)
          (xiMacroscopicCorrectionCountingRadius_pos T)).zeros
        TS284.Goldbach.riemannXiCandidateMultiplicity
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (macroscopicFactorZeros_subset_countingDiskZeros T)
  intro rho _ _
  exact Nat.zero_le _

/-- Closed log-linear mass envelope for the additional macroscopic roots. -/
noncomputable def xiMacroscopicCorrectionCountEnvelope (T : Nat) : Real :=
  TS290.Goldbach.xiDyadicLogLinearConstant *
    xiMacroscopicCorrectionCountingRadius T *
      Real.log (xiMacroscopicCorrectionCountingRadius T + 2)

theorem xiMacroscopicCorrectionCountingRadius_ge_one (T : Nat) :
    1 <= xiMacroscopicCorrectionCountingRadius T := by
  unfold xiMacroscopicCorrectionCountingRadius
    TS301.Goldbach.xiMacroscopicInnerRadius
  have hT : 0 <= (T : Real) := Nat.cast_nonneg T
  nlinarith

theorem xiMacroscopicFactorMultiplicityCount_le_closedEnvelope
    (T : Nat) :
    (xiMacroscopicFactorMultiplicityCount T : Real) <=
      xiMacroscopicCorrectionCountEnvelope T := by
  have hNat := xiMacroscopicFactorMultiplicityCount_le_dyadicCount T
  have hCast :
      (xiMacroscopicFactorMultiplicityCount T : Real) <=
        (TS274.Goldbach.finiteJensenMultiplicityCount
          (TS290.Goldbach.xiDyadicDiskData
            (xiMacroscopicCorrectionCountingRadius T)
            (xiMacroscopicCorrectionCountingRadius_pos T)) : Real) := by
    exact_mod_cast hNat
  calc
    (xiMacroscopicFactorMultiplicityCount T : Real) <=
        (TS274.Goldbach.finiteJensenMultiplicityCount
          (TS290.Goldbach.xiDyadicDiskData
            (xiMacroscopicCorrectionCountingRadius T)
            (xiMacroscopicCorrectionCountingRadius_pos T)) : Real) := hCast
    _ <= TS290.Goldbach.xiDyadicLogLinearConstant *
        xiMacroscopicCorrectionCountingRadius T *
          Real.log (xiMacroscopicCorrectionCountingRadius T + 2) := by
      exact TS290.Goldbach.xiDyadicMultiplicityCount_le_logLinear
        (xiMacroscopicCorrectionCountingRadius T)
        (xiMacroscopicCorrectionCountingRadius_pos T)
        (xiMacroscopicCorrectionCountingRadius_ge_one T)
    _ = xiMacroscopicCorrectionCountEnvelope T := rfl

theorem xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      xiMacroscopicCorrectionCountEnvelope T :=
  (xiMacroscopicHeightFiniteCorrection_norm_le_count_top T hT sigma).trans
    (xiMacroscopicFactorMultiplicityCount_le_closedEnvelope T)

theorem xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      xiMacroscopicCorrectionCountEnvelope T :=
  (xiMacroscopicHeightFiniteCorrection_norm_le_count_bottom T hT sigma).trans
    (xiMacroscopicFactorMultiplicityCount_le_closedEnvelope T)

/-! ## Quadratically normalized decay -/

noncomputable def xiMacroscopicCorrectionLogConstant : Real :=
  Real.log 258

theorem xiMacroscopicCorrectionLogConstant_nonnegative :
    0 <= xiMacroscopicCorrectionLogConstant := by
  unfold xiMacroscopicCorrectionLogConstant
  exact Real.log_nonneg (by norm_num)

/-- Transparent `log(T)/T` envelope for the normalized correction mass. -/
noncomputable def xiMacroscopicCorrectionDecayEnvelope (T : Nat) : Real :=
  1280 * TS290.Goldbach.xiDyadicLogLinearConstant *
    ((xiMacroscopicCorrectionLogConstant +
      Real.log ((T : Real) + 4)) / (T : Real))

theorem xiMacroscopicCorrectionCountEnvelope_nonnegative (T : Nat) :
    0 <= xiMacroscopicCorrectionCountEnvelope T := by
  unfold xiMacroscopicCorrectionCountEnvelope
  exact mul_nonneg
    (mul_nonneg TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
      (xiMacroscopicCorrectionCountingRadius_pos T).le)
    (Real.log_nonneg (by
      have hR := xiMacroscopicCorrectionCountingRadius_ge_one T
      linarith))

theorem xiMacroscopicCorrectionDecayEnvelope_nonnegative
    (T : Nat)
    (hT : 1 <= T) :
    0 <= xiMacroscopicCorrectionDecayEnvelope T := by
  unfold xiMacroscopicCorrectionDecayEnvelope
  have hTR : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hC := TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
  have hLog : 0 <= Real.log ((T : Real) + 4) := by
    apply Real.log_nonneg
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  exact mul_nonneg
    (mul_nonneg (by norm_num) hC)
    (div_nonneg
      (add_nonneg xiMacroscopicCorrectionLogConstant_nonnegative hLog) hTR.le)

theorem xiMacroscopicCorrection_log_le
    (T : Nat) :
    Real.log (xiMacroscopicCorrectionCountingRadius T + 2) <=
      xiMacroscopicCorrectionLogConstant + Real.log ((T : Real) + 4) := by
  let Y : Real := (T : Real) + 4
  have hY : 1 <= Y := by
    dsimp [Y]
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hArgPos : 0 < xiMacroscopicCorrectionCountingRadius T + 2 := by
    linarith [xiMacroscopicCorrectionCountingRadius_pos T]
  have hTargetPos : 0 < 258 * Y := by positivity
  have hArgLe : xiMacroscopicCorrectionCountingRadius T + 2 <= 258 * Y := by
    unfold xiMacroscopicCorrectionCountingRadius
      TS301.Goldbach.xiMacroscopicInnerRadius
    dsimp [Y]
    nlinarith
  calc
    Real.log (xiMacroscopicCorrectionCountingRadius T + 2) <=
        Real.log (258 * Y) := Real.log_le_log hArgPos hArgLe
    _ = Real.log 258 + Real.log Y := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    _ = xiMacroscopicCorrectionLogConstant + Real.log ((T : Real) + 4) := rfl

theorem xiMacroscopicCorrectionCountEnvelope_div_sq_le_decayEnvelope
    (T : Nat)
    (hT : 1 <= T) :
    xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2 <=
      xiMacroscopicCorrectionDecayEnvelope T := by
  let C : Real := TS290.Goldbach.xiDyadicLogLinearConstant
  let K : Real := xiMacroscopicCorrectionLogConstant
  let L : Real := Real.log ((T : Real) + 4)
  have hTR : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hC : 0 <= C := TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
  have hK : 0 <= K := xiMacroscopicCorrectionLogConstant_nonnegative
  have hL : 0 <= L := by
    dsimp [L]
    apply Real.log_nonneg
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hLog := xiMacroscopicCorrection_log_le T
  have hCountRadius :
      xiMacroscopicCorrectionCountingRadius T = 256 * ((T : Real) + 4) := by
    unfold xiMacroscopicCorrectionCountingRadius
      TS301.Goldbach.xiMacroscopicInnerRadius
    ring
  have hRatio : ((T : Real) + 4) / (T : Real) ^ 2 <= 5 / (T : Real) := by
    have hTone : 1 <= (T : Real) := by exact_mod_cast hT
    have hNumerator : ((T : Real) + 4) / (T : Real) <= 5 := by
      calc
        ((T : Real) + 4) / (T : Real) <=
            (5 * (T : Real)) / (T : Real) :=
          div_le_div_of_nonneg_right (by nlinarith) hTR.le
        _ = 5 := by field_simp [hTR.ne']
    rw [show (T : Real) ^ 2 = (T : Real) * (T : Real) by ring]
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hNumerator hTR.le
  have hClosed :
      xiMacroscopicCorrectionCountEnvelope T <=
        256 * C * ((T : Real) + 4) * (K + L) := by
    unfold xiMacroscopicCorrectionCountEnvelope
    rw [hCountRadius]
    have hPrefix : 0 <= 256 * C * ((T : Real) + 4) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity)
    calc
      TS290.Goldbach.xiDyadicLogLinearConstant *
            (256 * ((T : Real) + 4)) *
              Real.log (256 * ((T : Real) + 4) + 2) =
          256 * C * ((T : Real) + 4) *
            Real.log (xiMacroscopicCorrectionCountingRadius T + 2) := by
              dsimp [C]
              rw [hCountRadius]
              ring
      _ <= 256 * C * ((T : Real) + 4) * (K + L) :=
        mul_le_mul_of_nonneg_left hLog hPrefix
  calc
    xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2 <=
        (256 * C * ((T : Real) + 4) * (K + L)) / (T : Real) ^ 2 :=
      div_le_div_of_nonneg_right hClosed (sq_nonneg (T : Real))
    _ = 256 * C * (K + L) *
          (((T : Real) + 4) / (T : Real) ^ 2) := by ring
    _ <= 256 * C * (K + L) * (5 / (T : Real)) := by
      gcongr
    _ = xiMacroscopicCorrectionDecayEnvelope T := by
      unfold xiMacroscopicCorrectionDecayEnvelope
      dsimp [C, K, L]
      ring

theorem xiMacroscopicCorrectionDecayEnvelope_tendsto_zero :
    Tendsto xiMacroscopicCorrectionDecayEnvelope atTop (nhds 0) := by
  have hInv := tendsto_one_div_atTop_nhds_zero_nat.const_mul
    xiMacroscopicCorrectionLogConstant
  have hLog := TS300.Goldbach.tendsto_log_shift_div_nat
  have hInside := hInv.add hLog
  have hTotal := hInside.const_mul
    (1280 * TS290.Goldbach.xiDyadicLogLinearConstant)
  convert hTotal using 1
  case h.e'_3 =>
    funext T
    unfold xiMacroscopicCorrectionDecayEnvelope
    ring
  case h.e'_5 => ring

theorem xiMacroscopicCorrectionCountEnvelope_div_sq_tendsto_zero :
    Tendsto
      (fun T : Nat =>
        xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ xiMacroscopicCorrectionDecayEnvelope_tendsto_zero
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg
      (xiMacroscopicCorrectionCountEnvelope_nonnegative T)
      (sq_nonneg (T : Real))
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact xiMacroscopicCorrectionCountEnvelope_div_sq_le_decayEnvelope T hT

/-! ## Horizontal Perron routing at fixed arithmetic scale -/

noncomputable def xiMacroscopicCorrectionTopPointwise
    (x T : Nat)
    (sigma : Real) : Real :=
  norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
    norm ((x : Complex) ^ (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
      norm (TS257.Goldbach.triangleSplineMellinKernel
        (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma))

noncomputable def xiMacroscopicCorrectionBottomPointwise
    (x T : Nat)
    (sigma : Real) : Real :=
  norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
    norm ((x : Complex) ^ (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
      norm (TS257.Goldbach.triangleSplineMellinKernel
        (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma))

/-- Fixed-width envelope for the integrated macroscopic correction. -/
noncomputable def xiMacroscopicCorrectionHorizontalComponent
    (x T : Nat) : Real :=
  (7 / 2 : Real) * TS298.Goldbach.rightLineScale x *
    (xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2)

theorem xiMacroscopicCorrectionTopPointwise_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    xiMacroscopicCorrectionTopPointwise x T sigma <=
      TS298.Goldbach.rightLineScale x *
        (xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hInv :
      1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
        1 / (T : Real) ^ 2 := by
    have hTauPos : 0 < TS299.Goldbach.finiteGridStrongTau T :=
      TS299.Goldbach.finiteGridStrongTau_pos hT
    have hSq :
        (T : Real) ^ 2 <= (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
    exact one_div_le_one_div_of_le (sq_pos_of_pos hTPos) hSq
  have hEnvelope0 := xiMacroscopicCorrectionCountEnvelope_nonnegative T
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold xiMacroscopicCorrectionTopPointwise
  calc
    norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
        norm ((x : Complex) ^
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
        norm (TS257.Goldbach.triangleSplineMellinKernel
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      xiMacroscopicCorrectionCountEnvelope T *
        TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst :
          norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
                (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
              norm ((x : Complex) ^
                (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
            xiMacroscopicCorrectionCountEnvelope T *
              TS298.Goldbach.rightLineScale x :=
        mul_le_mul
          (xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_top
            T hT sigma)
          (TS300.Goldbach.nat_cpow_finiteGridTop_norm_le_rightLineScale
            x T hT sigma hSigma)
          (norm_nonneg _) hEnvelope0
      exact mul_le_mul hFirst
        (TS300.Goldbach.triangleSplineMellinKernel_finiteGridTop_norm_le
          T hT sigma)
        (norm_nonneg _) (mul_nonneg hEnvelope0 hScale0)
    _ <= xiMacroscopicCorrectionCountEnvelope T *
        TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hInv (mul_nonneg hEnvelope0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
        (xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2) := by
      ring

theorem xiMacroscopicCorrectionBottomPointwise_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    xiMacroscopicCorrectionBottomPointwise x T sigma <=
      TS298.Goldbach.rightLineScale x *
        (xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hInv :
      1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
        1 / (T : Real) ^ 2 := by
    have hTauPos : 0 < TS299.Goldbach.finiteGridStrongTau T :=
      TS299.Goldbach.finiteGridStrongTau_pos hT
    have hSq :
        (T : Real) ^ 2 <= (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
    exact one_div_le_one_div_of_le (sq_pos_of_pos hTPos) hSq
  have hEnvelope0 := xiMacroscopicCorrectionCountEnvelope_nonnegative T
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold xiMacroscopicCorrectionBottomPointwise
  calc
    norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
        norm ((x : Complex) ^
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
        norm (TS257.Goldbach.triangleSplineMellinKernel
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      xiMacroscopicCorrectionCountEnvelope T *
        TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst :
          norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T
                (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
              norm ((x : Complex) ^
                (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
            xiMacroscopicCorrectionCountEnvelope T *
              TS298.Goldbach.rightLineScale x :=
        mul_le_mul
          (xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_bottom
            T hT sigma)
          (TS300.Goldbach.nat_cpow_finiteGridBottom_norm_le_rightLineScale
            x T hT sigma hSigma)
          (norm_nonneg _) hEnvelope0
      exact mul_le_mul hFirst
        (TS300.Goldbach.triangleSplineMellinKernel_finiteGridBottom_norm_le
          T hT sigma)
        (norm_nonneg _) (mul_nonneg hEnvelope0 hScale0)
    _ <= xiMacroscopicCorrectionCountEnvelope T *
        TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hInv (mul_nonneg hEnvelope0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
        (xiMacroscopicCorrectionCountEnvelope T / (T : Real) ^ 2) := by
      ring

theorem xiMacroscopicCorrectionTop_integratedWidth_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    (7 / 2 : Real) * xiMacroscopicCorrectionTopPointwise x T sigma <=
      xiMacroscopicCorrectionHorizontalComponent x T := by
  unfold xiMacroscopicCorrectionHorizontalComponent
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (xiMacroscopicCorrectionTopPointwise_le x T hT sigma hSigma)
    (by norm_num : (0 : Real) <= 7 / 2)

theorem xiMacroscopicCorrectionBottom_integratedWidth_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : sigma <= TS294.Goldbach.fixedPerronRight) :
    (7 / 2 : Real) * xiMacroscopicCorrectionBottomPointwise x T sigma <=
      xiMacroscopicCorrectionHorizontalComponent x T := by
  unfold xiMacroscopicCorrectionHorizontalComponent
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (xiMacroscopicCorrectionBottomPointwise_le x T hT sigma hSigma)
    (by norm_num : (0 : Real) <= 7 / 2)

theorem xiMacroscopicCorrectionHorizontalComponent_tendsto_zero
    (x : Nat) :
    Tendsto (xiMacroscopicCorrectionHorizontalComponent x) atTop (nhds 0) := by
  unfold xiMacroscopicCorrectionHorizontalComponent
  simpa using
    xiMacroscopicCorrectionCountEnvelope_div_sq_tendsto_zero.const_mul
      ((7 / 2 : Real) * TS298.Goldbach.rightLineScale x)

theorem heightMacroscopicLogDerivativeDifference_norm_le_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm
      (deriv (TS296.Goldbach.heightXiQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
            TS296.Goldbach.heightXiQuotient T
              (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) -
        deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
            TS301.Goldbach.xiMacroscopicQuotient T
              (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      xiMacroscopicCorrectionCountEnvelope T := by
  rw [TS301.Goldbach.heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection_top
    T hT sigma hSigma]
  ring_nf
  exact xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_top T hT sigma

theorem heightMacroscopicLogDerivativeDifference_norm_le_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm
      (deriv (TS296.Goldbach.heightXiQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
            TS296.Goldbach.heightXiQuotient T
              (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) -
        deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
            TS301.Goldbach.xiMacroscopicQuotient T
              (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      xiMacroscopicCorrectionCountEnvelope T := by
  rw [TS301.Goldbach.heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection_bottom
    T hT sigma hSigma]
  ring_nf
  exact xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_bottom T hT sigma

/-! ## Audit ledger -/

structure FiniteMacroscopicCorrectionDecayLedger where
  height_zeros_subset_macroscopic_factors_proved : Prop
  multiplicity_compatibility_proved : Prop
  correction_reindexed_as_extra_zero_sum : Prop
  extra_zero_height_gap_proved : Prop
  top_bottom_denominator_bounds_proved : Prop
  macroscopic_mass_injected_into_dyadic_count : Prop
  closed_log_linear_envelope_proved : Prop
  normalized_correction_decay_proved : Prop
  fixed_scale_horizontal_decay_proved : Prop
  exact_TS301_bridge_reinjected : Prop
  local_zero_density_not_used : Prop
  riemann_hypothesis_not_used : Prop
  infinite_hadamard_product_not_used : Prop
  anchored_envelope_rate_not_proved : Prop
  completion_correction_rate_not_proved : Prop
  full_horizontal_decay_not_proved : Prop
  fixed_left_boundary_not_proved : Prop
  exceptional_residues_not_completed : Prop
  perron_inversion_not_proved : Prop
  meromorphic_residue_theorem_not_proved : Prop
  infinite_explicit_formula_not_proved : Prop
  gallagher_not_proved : Prop
  otsa_not_proved : Prop
  goldbach_not_claimed : Prop

def finiteMacroscopicCorrectionDecayLedger :
    FiniteMacroscopicCorrectionDecayLedger where
  height_zeros_subset_macroscopic_factors_proved := True
  multiplicity_compatibility_proved := True
  correction_reindexed_as_extra_zero_sum := True
  extra_zero_height_gap_proved := True
  top_bottom_denominator_bounds_proved := True
  macroscopic_mass_injected_into_dyadic_count := True
  closed_log_linear_envelope_proved := True
  normalized_correction_decay_proved := True
  fixed_scale_horizontal_decay_proved := True
  exact_TS301_bridge_reinjected := True
  local_zero_density_not_used := True
  riemann_hypothesis_not_used := True
  infinite_hadamard_product_not_used := True
  anchored_envelope_rate_not_proved := True
  completion_correction_rate_not_proved := True
  full_horizontal_decay_not_proved := True
  fixed_left_boundary_not_proved := True
  exceptional_residues_not_completed := True
  perron_inversion_not_proved := True
  meromorphic_residue_theorem_not_proved := True
  infinite_explicit_formula_not_proved := True
  gallagher_not_proved := True
  otsa_not_proved := True
  goldbach_not_claimed := True

end Goldbach
end TS302
