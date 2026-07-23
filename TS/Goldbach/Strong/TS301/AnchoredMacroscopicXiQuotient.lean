import Mathlib.Tactic
import TS.Goldbach.Strong.TS300.CenteredBorelCaratheodoryAndClosedLoadDecay

/-!
# TS301 - Anchored Macroscopic Xi Quotient

TS300 isolated the missing horizontal input as a centered real-part bound for
the logarithm of a finite xi quotient.  A local zero-free disk around a moving
horizontal point cannot supply such a bound: nonvanishing alone gives no
quantitative lower bound at the center.

This sprint replaces that circular route by a concrete macroscopic quotient.
For height `T` it reuses the TS290 dyadic finite factorization at radius
`64 * (T + 4)`.  Its quotient is entire and nonzero on a disk much larger than
the Perron horizontal segment.  The TS279 logarithm is normalized at the fixed
anchor `2`, where xi is unconditionally nonzero.  A compact, branch-independent
real-part envelope then gives a genuine Borel-Caratheodory/Cauchy bound for the
macroscopic quotient at every point of the finite-grid horizontal segment.

The module also records the exact finite bridge to the historical height
quotient.  The correction is the difference between two named finite
logarithmic-derivative sums; it is not hidden in an anonymous remainder.  The
closed asymptotic rate for the anchored envelope and the resulting full
horizontal decay remain separate obligations.
-/

noncomputable section

namespace TS301
namespace Goldbach

open Complex Filter Metric Set Topology
open scoped Topology

/-! ## Macroscopic quotient and fixed anchor -/

/-- The fixed normalization point for the macroscopic quotient. -/
def xiMacroscopicAnchor : Complex := 2

/-- A scale much larger than the finite-grid Perron height. -/
noncomputable def xiMacroscopicInnerRadius (T : Nat) : Real :=
  64 * ((T : Real) + 4)

theorem xiMacroscopicInnerRadius_pos (T : Nat) :
    0 < xiMacroscopicInnerRadius T := by
  unfold xiMacroscopicInnerRadius
  positivity

/-- The TS290 finite-zero specification used at macroscopic scale. -/
noncomputable def xiMacroscopicSpec (T : Nat) :
    TS282.Goldbach.XiFiniteZeroFactorizationSpec :=
  TS290.Goldbach.xiDyadicFiniteZeroFactorizationSpec
    (xiMacroscopicInnerRadius T) (xiMacroscopicInnerRadius_pos T)

/-- The corresponding entire quotient with all selected singularities filled. -/
noncomputable def xiMacroscopicQuotient (T : Nat) : Complex -> Complex :=
  TS285.Goldbach.riemannXiFiniteQuotient (xiMacroscopicSpec T)

/-- Buffered data carrying analyticity and nonvanishing on the macroscopic disk. -/
noncomputable def xiMacroscopicBufferedData (T : Nat) :
    TS275.Goldbach.BufferedJensenFactorizationData :=
  TS290.Goldbach.xiDyadicBufferedData
    (xiMacroscopicInnerRadius T) (xiMacroscopicInnerRadius_pos T)

@[simp]
theorem xiMacroscopicBufferedData_g (T : Nat) :
    (xiMacroscopicBufferedData T).g = xiMacroscopicQuotient T := rfl

@[simp]
theorem xiMacroscopicBufferedData_center (T : Nat) :
    (xiMacroscopicBufferedData T).zeroData.config.center = 0 := rfl

/-- Radius of the anchored control disk. -/
noncomputable def xiMacroscopicControlRadius (T : Nat) : Real :=
  16 * ((T : Real) + 4)

theorem xiMacroscopicControlRadius_pos (T : Nat) :
    0 < xiMacroscopicControlRadius T := by
  unfold xiMacroscopicControlRadius
  positivity

/-- Cauchy radius around each finite-grid horizontal point. -/
noncomputable def xiMacroscopicLocalRadius (T : Nat) : Real :=
  2 * ((T : Real) + 4)

theorem xiMacroscopicLocalRadius_pos (T : Nat) :
    0 < xiMacroscopicLocalRadius T := by
  unfold xiMacroscopicLocalRadius
  positivity

theorem xiMacroscopicInnerRadius_lt_analyticRadius (T : Nat) :
    xiMacroscopicInnerRadius T <
      (xiMacroscopicBufferedData T).zeroData.config.analyticRadius := by
  exact
    (xiMacroscopicBufferedData T).zeroData.config.innerRadius_lt_averagingRadius.trans
      (xiMacroscopicBufferedData T).zeroData.config.averagingRadius_lt_analyticRadius

theorem anchoredControlClosedBall_subset_analyticClosedBall (T : Nat) :
    Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T) <=
      Metric.closedBall
        (xiMacroscopicBufferedData T).zeroData.config.center
        (xiMacroscopicBufferedData T).zeroData.config.analyticRadius := by
  intro z hz
  rw [Metric.mem_closedBall] at hz
  rw [Metric.mem_closedBall, xiMacroscopicBufferedData_center, dist_zero_right]
  have hAnchorNorm : norm xiMacroscopicAnchor = 2 := by
    norm_num [xiMacroscopicAnchor]
  have hzNorm : norm z <= xiMacroscopicControlRadius T + 2 := by
    calc
      norm z <= norm (z - xiMacroscopicAnchor) + norm xiMacroscopicAnchor := by
        simpa using norm_add_le (z - xiMacroscopicAnchor) xiMacroscopicAnchor
      _ = dist z xiMacroscopicAnchor + 2 := by
        rw [dist_eq, hAnchorNorm, Complex.norm_eq_abs]
      _ <= xiMacroscopicControlRadius T + 2 := by linarith
  have hControlLtInner :
      xiMacroscopicControlRadius T + 2 < xiMacroscopicInnerRadius T := by
    change (16 : Real) * ((T : Real) + 4) + 2 <
      (64 : Real) * ((T : Real) + 4)
    nlinarith [(Nat.cast_nonneg T : (0 : Real) <= (T : Real))]
  exact hzNorm.trans (hControlLtInner.trans (xiMacroscopicInnerRadius_lt_analyticRadius T)).le

theorem xiMacroscopicQuotient_nonzero_on_controlBall
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem (Metric.closedBall xiMacroscopicAnchor
      (xiMacroscopicControlRadius T)) z) :
    Not (xiMacroscopicQuotient T z = 0) := by
  exact (xiMacroscopicBufferedData T).g_nonzero z
    (anchoredControlClosedBall_subset_analyticClosedBall T hz)

theorem xiMacroscopicQuotient_analyticOnNhd_controlBall (T : Nat) :
    AnalyticOnNhd Complex (xiMacroscopicQuotient T)
      (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) := by
  intro z hz
  exact (xiMacroscopicBufferedData T).g_analytic z
    (anchoredControlClosedBall_subset_analyticClosedBall T hz)

theorem riemannXiCandidate_ne_zero_at_macroscopicAnchor :
    Not (TS282.Goldbach.riemannXiCandidate xiMacroscopicAnchor = 0) := by
  apply TS296.Goldbach.riemannXiCandidate_ne_zero_of_one_le_re
  norm_num [xiMacroscopicAnchor]

theorem xiMacroscopicQuotient_ne_zero_at_anchor (T : Nat) :
    Not (xiMacroscopicQuotient T xiMacroscopicAnchor = 0) := by
  apply xiMacroscopicQuotient_nonzero_on_controlBall T
  exact Metric.mem_closedBall_self (xiMacroscopicControlRadius_pos T).le

/-! ## Global logarithm normalized at the anchor -/

/-- The TS279 logarithm of the concrete macroscopic quotient. -/
noncomputable def xiMacroscopicLogData (T : Nat) :
    TS277.Goldbach.BufferedQuotientHolomorphicLogData
      (xiMacroscopicBufferedData T) :=
  TS279.Goldbach.bufferedQuotientHolomorphicLogData
    (xiMacroscopicBufferedData T)

/-- The logarithm centered at the fixed anchor `2`. -/
noncomputable def anchoredXiMacroscopicLog (T : Nat) : Complex -> Complex :=
  fun z =>
    (xiMacroscopicLogData T).logarithm z -
      (xiMacroscopicLogData T).logarithm xiMacroscopicAnchor

/-- The quotient normalized to have value one at the anchor. -/
noncomputable def normalizedXiMacroscopicQuotient
    (T : Nat) : Complex -> Complex :=
  fun z => xiMacroscopicQuotient T z /
    xiMacroscopicQuotient T xiMacroscopicAnchor

@[simp]
theorem anchoredXiMacroscopicLog_anchor (T : Nat) :
    anchoredXiMacroscopicLog T xiMacroscopicAnchor = 0 := by
  simp [anchoredXiMacroscopicLog]

theorem anchoredXiMacroscopicLog_analyticOnNhd_controlBall (T : Nat) :
    AnalyticOnNhd Complex (anchoredXiMacroscopicLog T)
      (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) := by
  intro z hz
  have hzMacro := anchoredControlClosedBall_subset_analyticClosedBall T hz
  exact ((xiMacroscopicLogData T).logarithm_analytic z hzMacro).sub analyticAt_const

theorem exp_anchoredXiMacroscopicLog_eq_normalized
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem (Metric.closedBall xiMacroscopicAnchor
      (xiMacroscopicControlRadius T)) z) :
    Complex.exp (anchoredXiMacroscopicLog T z) =
      normalizedXiMacroscopicQuotient T z := by
  have hzMacro := anchoredControlClosedBall_subset_analyticClosedBall T hz
  have hAnchorControl : Membership.mem
      (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T))
      xiMacroscopicAnchor :=
    Metric.mem_closedBall_self (xiMacroscopicControlRadius_pos T).le
  have hAnchorMacro := anchoredControlClosedBall_subset_analyticClosedBall T hAnchorControl
  rw [anchoredXiMacroscopicLog, Complex.exp_sub,
    (xiMacroscopicLogData T).exp_logarithm_eq_g z hzMacro,
    (xiMacroscopicLogData T).exp_logarithm_eq_g xiMacroscopicAnchor hAnchorMacro]
  rfl

/-! ## A concrete compact anchored envelope -/

def anchoredXiMacroscopicRealPartValues (T : Nat) : Set Real :=
  (fun z : Complex => (anchoredXiMacroscopicLog T z).re) ''
    Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)

noncomputable def anchoredXiMacroscopicRealPartSup (T : Nat) : Real :=
  sSup (anchoredXiMacroscopicRealPartValues T)

/-- Strict positive envelope used by the Schwarz-transform theorem. -/
noncomputable def anchoredXiMacroscopicRealPartEnvelope (T : Nat) : Real :=
  max 1 (anchoredXiMacroscopicRealPartSup T + 1)

theorem anchoredXiMacroscopicLog_continuousOn_controlBall (T : Nat) :
    ContinuousOn (anchoredXiMacroscopicLog T)
      (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) := by
  intro z hz
  exact (anchoredXiMacroscopicLog_analyticOnNhd_controlBall T z hz).continuousAt.continuousWithinAt

theorem anchoredXiMacroscopicRealPartValues_compact (T : Nat) :
    IsCompact (anchoredXiMacroscopicRealPartValues T) := by
  unfold anchoredXiMacroscopicRealPartValues
  exact
    (isCompact_closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)).image_of_continuousOn
      (Complex.continuous_re.comp_continuousOn
        (anchoredXiMacroscopicLog_continuousOn_controlBall T))

theorem anchoredXiMacroscopicRealPartEnvelope_pos (T : Nat) :
    0 < anchoredXiMacroscopicRealPartEnvelope T := by
  unfold anchoredXiMacroscopicRealPartEnvelope
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem anchoredXiMacroscopicLog_re_lt_envelope
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem (Metric.closedBall xiMacroscopicAnchor
      (xiMacroscopicControlRadius T)) z) :
    (anchoredXiMacroscopicLog T z).re <
      anchoredXiMacroscopicRealPartEnvelope T := by
  have hMem : Membership.mem (anchoredXiMacroscopicRealPartValues T)
      (anchoredXiMacroscopicLog T z).re :=
    Exists.intro z (And.intro hz rfl)
  have hLe : (anchoredXiMacroscopicLog T z).re <=
      anchoredXiMacroscopicRealPartSup T := by
    exact le_csSup (anchoredXiMacroscopicRealPartValues_compact T).bddAbove hMem
  have hLt : (anchoredXiMacroscopicLog T z).re <
      anchoredXiMacroscopicRealPartSup T + 1 := by linarith
  exact hLt.trans_le (le_max_right _ _)

/-! ## Borel-Caratheodory control throughout the macroscopic interior -/

theorem anchoredXiMacroscopicLog_norm_le
    (T : Nat)
    (z : Complex)
    (hz : dist z xiMacroscopicAnchor < xiMacroscopicControlRadius T) :
    norm (anchoredXiMacroscopicLog T z) <=
      2 * anchoredXiMacroscopicRealPartEnvelope T *
          dist z xiMacroscopicAnchor /
        (xiMacroscopicControlRadius T - dist z xiMacroscopicAnchor) := by
  let f : Complex -> Complex := fun w =>
    anchoredXiMacroscopicLog T (xiMacroscopicAnchor + w)
  have hfDiff : DifferentiableOn Complex f
      (Metric.ball 0 (xiMacroscopicControlRadius T)) := by
    intro w hw
    have hwDist : dist (xiMacroscopicAnchor + w) xiMacroscopicAnchor <
        xiMacroscopicControlRadius T := by
      simpa [dist_eq] using hw
    have hwClosed : Membership.mem
        (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T))
        (xiMacroscopicAnchor + w) :=
      Metric.mem_closedBall.mpr hwDist.le
    have hOuter :=
      (anchoredXiMacroscopicLog_analyticOnNhd_controlBall T _ hwClosed).differentiableAt
    have hInner : DifferentiableAt Complex (fun u : Complex => xiMacroscopicAnchor + u) w :=
      differentiableAt_const xiMacroscopicAnchor |>.add differentiableAt_id
    exact (hOuter.comp w hInner).differentiableWithinAt
  have hfZero : f 0 = 0 := by
    simp [f, anchoredXiMacroscopicLog_anchor]
  have hfRe : forall w, Membership.mem
      (Metric.ball 0 (xiMacroscopicControlRadius T)) w ->
      (f w).re < anchoredXiMacroscopicRealPartEnvelope T := by
    intro w hw
    apply anchoredXiMacroscopicLog_re_lt_envelope T
    rw [Metric.mem_closedBall]
    simpa [dist_eq] using (Metric.mem_ball.mp hw).le
  have hw : Membership.mem (Metric.ball 0 (xiMacroscopicControlRadius T))
      (z - xiMacroscopicAnchor) := by
    simpa [Metric.mem_ball, dist_eq] using hz
  have hMaps : MapsTo f (Metric.ball 0 (xiMacroscopicControlRadius T))
      {u : Complex | u.re < anchoredXiMacroscopicRealPartEnvelope T} := hfRe
  have hBC := TS300.Goldbach.centered_borelCaratheodory_zero
    (anchoredXiMacroscopicRealPartEnvelope_pos T)
    hfDiff hMaps (xiMacroscopicControlRadius_pos T) hw hfZero
  simpa [f, dist_eq, sub_add_cancel] using hBC

/-! ## Uniform local Cauchy data on the finite-grid horizontal segment -/

theorem finiteGridHorizontalPoint_dist_anchor_le
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    dist (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)
        xiMacroscopicAnchor <= (T : Real) + 5 := by
    rw [dist_eq]
    calc
    Complex.abs (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma -
        xiMacroscopicAnchor) <=
      |sigma - 2| + |TS299.Goldbach.finiteGridStrongTau T| := by
        calc
          _ <=
              |(TS300.Goldbach.finiteGridTopHorizontalPoint T sigma -
                xiMacroscopicAnchor).re| +
              |(TS300.Goldbach.finiteGridTopHorizontalPoint T sigma -
                xiMacroscopicAnchor).im| :=
            Complex.abs_le_abs_re_add_abs_im _
          _ = _ := by
            simp [TS300.Goldbach.finiteGridTopHorizontalPoint,
              xiMacroscopicAnchor]
    _ <= (7 / 2 : Real) + ((T : Real) + 1) := by
      have hSigmaAbs : |sigma - 2| <= (7 / 2 : Real) := by
        rw [abs_le]
        norm_num [TS294.Goldbach.fixedPerronLeft,
          TS294.Goldbach.fixedPerronRight] at hSigma
        constructor <;> linarith
      have hTauPos : 0 <= TS299.Goldbach.finiteGridStrongTau T :=
        (Nat.cast_nonneg T).trans
          (TS299.Goldbach.finiteGridStrongTau_gt T).le
      rw [_root_.abs_of_nonneg hTauPos]
      linarith [TS299.Goldbach.finiteGridStrongTau_lt T]
    _ <= (T : Real) + 5 := by linarith

theorem finiteGridBottomHorizontalPoint_dist_anchor_le
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    dist (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)
        xiMacroscopicAnchor <= (T : Real) + 5 := by
  rw [dist_eq]
  calc
    Complex.abs (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma -
        xiMacroscopicAnchor) <=
      |sigma - 2| + |-TS299.Goldbach.finiteGridStrongTau T| := by
        calc
          _ <=
              |(TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma -
                xiMacroscopicAnchor).re| +
              |(TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma -
                xiMacroscopicAnchor).im| :=
            Complex.abs_le_abs_re_add_abs_im _
          _ = _ := by
            simp [TS300.Goldbach.finiteGridBottomHorizontalPoint,
              xiMacroscopicAnchor]
    _ <= (7 / 2 : Real) + ((T : Real) + 1) := by
      have hSigmaAbs : |sigma - 2| <= (7 / 2 : Real) := by
        rw [abs_le]
        norm_num [TS294.Goldbach.fixedPerronLeft,
          TS294.Goldbach.fixedPerronRight] at hSigma
        constructor <;> linarith
      rw [abs_neg]
      have hTauPos : 0 <= TS299.Goldbach.finiteGridStrongTau T :=
        (Nat.cast_nonneg T).trans
          (TS299.Goldbach.finiteGridStrongTau_gt T).le
      rw [_root_.abs_of_nonneg hTauPos]
      linarith [TS299.Goldbach.finiteGridStrongTau_lt T]
    _ <= (T : Real) + 5 := by linarith

theorem localSphere_subset_controlBall
    (T : Nat)
    {center z : Complex}
    (hCenter : dist center xiMacroscopicAnchor <= (T : Real) + 5)
    (hz : Membership.mem
      (Metric.sphere center (xiMacroscopicLocalRadius T)) z) :
    dist z xiMacroscopicAnchor <= xiMacroscopicControlRadius T / 2 := by
  have hTriangle := dist_triangle z center xiMacroscopicAnchor
  have hzDist : dist z center = xiMacroscopicLocalRadius T :=
    Metric.mem_sphere.mp hz
  rw [hzDist] at hTriangle
  have hLocal : xiMacroscopicLocalRadius T = 2 * ((T : Real) + 4) := rfl
  have hControl : xiMacroscopicControlRadius T = 16 * ((T : Real) + 4) := rfl
  rw [hLocal] at hTriangle
  rw [hControl]
  norm_num
  linarith

theorem anchoredXiMacroscopicLog_norm_le_two_envelope
    (T : Nat)
    (z : Complex)
    (hz : dist z xiMacroscopicAnchor <= xiMacroscopicControlRadius T / 2) :
    norm (anchoredXiMacroscopicLog T z) <=
      2 * anchoredXiMacroscopicRealPartEnvelope T := by
  have hRPos := xiMacroscopicControlRadius_pos T
  have hzLt : dist z xiMacroscopicAnchor < xiMacroscopicControlRadius T := by
    linarith
  have hBase := anchoredXiMacroscopicLog_norm_le T z hzLt
  have hDistNonnegative : 0 <= dist z xiMacroscopicAnchor := dist_nonneg
  have hMNonnegative : 0 <= anchoredXiMacroscopicRealPartEnvelope T :=
    (anchoredXiMacroscopicRealPartEnvelope_pos T).le
  have hDenPos : 0 < xiMacroscopicControlRadius T - dist z xiMacroscopicAnchor :=
    sub_pos.mpr hzLt
  apply hBase.trans
  have hNumerator :
      2 * anchoredXiMacroscopicRealPartEnvelope T *
          dist z xiMacroscopicAnchor <=
        (2 * anchoredXiMacroscopicRealPartEnvelope T) *
          (xiMacroscopicControlRadius T - dist z xiMacroscopicAnchor) := by
    nlinarith
  calc
    2 * anchoredXiMacroscopicRealPartEnvelope T *
          dist z xiMacroscopicAnchor /
        (xiMacroscopicControlRadius T - dist z xiMacroscopicAnchor) <=
      ((2 * anchoredXiMacroscopicRealPartEnvelope T) *
          (xiMacroscopicControlRadius T - dist z xiMacroscopicAnchor)) /
        (xiMacroscopicControlRadius T - dist z xiMacroscopicAnchor) :=
      div_le_div_of_nonneg_right hNumerator hDenPos.le
    _ = 2 * anchoredXiMacroscopicRealPartEnvelope T := by
      field_simp

noncomputable def finiteGridTopMacroscopicLocalLogData
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (normalizedXiMacroscopicQuotient T)
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) where
  radius := xiMacroscopicLocalRadius T
  radius_pos := xiMacroscopicLocalRadius_pos T
  logarithm := anchoredXiMacroscopicLog T
  logarithm_diffContOnCl := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hzSphere : dist z
        (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) <=
        xiMacroscopicLocalRadius T := by
      exact Metric.mem_closedBall.mp
        (Metric.closure_ball_subset_closedBall hz)
    have hControl : Membership.mem
        (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) z := by
      rw [Metric.mem_closedBall]
      have hTriangle := dist_triangle z
        (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)
        xiMacroscopicAnchor
      have hCenter := finiteGridHorizontalPoint_dist_anchor_le T sigma hSigma
      rw [show xiMacroscopicLocalRadius T = 2 * ((T : Real) + 4) from rfl] at hzSphere
      rw [show xiMacroscopicControlRadius T = 16 * ((T : Real) + 4) from rfl]
      norm_num
      linarith
    exact (anchoredXiMacroscopicLog_analyticOnNhd_controlBall T z hControl).differentiableAt
      |>.differentiableWithinAt
  exp_logarithm_eq := by
    intro z hz
    apply exp_anchoredXiMacroscopicLog_eq_normalized
    rw [Metric.mem_closedBall]
    have hTriangle := dist_triangle z
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)
      xiMacroscopicAnchor
    have hCenter := finiteGridHorizontalPoint_dist_anchor_le T sigma hSigma
    have hzDist := (Metric.mem_ball.mp hz)
    rw [show xiMacroscopicLocalRadius T = 2 * ((T : Real) + 4) from rfl] at hzDist
    rw [show xiMacroscopicControlRadius T = 16 * ((T : Real) + 4) from rfl]
    norm_num
    linarith
  sphereBound := 2 * anchoredXiMacroscopicRealPartEnvelope T
  logarithm_norm_le := by
    intro z hz
    apply anchoredXiMacroscopicLog_norm_le_two_envelope
    exact localSphere_subset_controlBall T
      (finiteGridHorizontalPoint_dist_anchor_le T sigma hSigma) hz

noncomputable def finiteGridBottomMacroscopicLocalLogData
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (normalizedXiMacroscopicQuotient T)
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) where
  radius := xiMacroscopicLocalRadius T
  radius_pos := xiMacroscopicLocalRadius_pos T
  logarithm := anchoredXiMacroscopicLog T
  logarithm_diffContOnCl := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hzSphere : dist z
        (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) <=
        xiMacroscopicLocalRadius T := by
      exact Metric.mem_closedBall.mp
        (Metric.closure_ball_subset_closedBall hz)
    have hControl : Membership.mem
        (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) z := by
      rw [Metric.mem_closedBall]
      have hTriangle := dist_triangle z
        (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)
        xiMacroscopicAnchor
      have hCenter := finiteGridBottomHorizontalPoint_dist_anchor_le T sigma hSigma
      rw [show xiMacroscopicLocalRadius T = 2 * ((T : Real) + 4) from rfl] at hzSphere
      rw [show xiMacroscopicControlRadius T = 16 * ((T : Real) + 4) from rfl]
      norm_num
      linarith
    exact (anchoredXiMacroscopicLog_analyticOnNhd_controlBall T z hControl).differentiableAt
      |>.differentiableWithinAt
  exp_logarithm_eq := by
    intro z hz
    apply exp_anchoredXiMacroscopicLog_eq_normalized
    rw [Metric.mem_closedBall]
    have hTriangle := dist_triangle z
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)
      xiMacroscopicAnchor
    have hCenter := finiteGridBottomHorizontalPoint_dist_anchor_le T sigma hSigma
    have hzDist := (Metric.mem_ball.mp hz)
    rw [show xiMacroscopicLocalRadius T = 2 * ((T : Real) + 4) from rfl] at hzDist
    rw [show xiMacroscopicControlRadius T = 16 * ((T : Real) + 4) from rfl]
    norm_num
    linarith
  sphereBound := 2 * anchoredXiMacroscopicRealPartEnvelope T
  logarithm_norm_le := by
    intro z hz
    apply anchoredXiMacroscopicLog_norm_le_two_envelope
    exact localSphere_subset_controlBall T
      (finiteGridBottomHorizontalPoint_dist_anchor_le T sigma hSigma) hz

theorem normalizedXiMacroscopicQuotient_logDeriv_eq
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem (Metric.closedBall xiMacroscopicAnchor
      (xiMacroscopicControlRadius T)) z) :
    deriv (normalizedXiMacroscopicQuotient T) z /
        normalizedXiMacroscopicQuotient T z =
      deriv (xiMacroscopicQuotient T) z / xiMacroscopicQuotient T z := by
  have hAnchorNe := xiMacroscopicQuotient_ne_zero_at_anchor T
  have hzNe := xiMacroscopicQuotient_nonzero_on_controlBall T z hz
  have hDiff : DifferentiableAt Complex (xiMacroscopicQuotient T) z :=
    (xiMacroscopicQuotient_analyticOnNhd_controlBall T z hz).differentiableAt
  have hDeriv : deriv (normalizedXiMacroscopicQuotient T) z =
      deriv (xiMacroscopicQuotient T) z /
        xiMacroscopicQuotient T xiMacroscopicAnchor := by
    exact (hDiff.hasDerivAt.div_const
      (xiMacroscopicQuotient T xiMacroscopicAnchor)).deriv
  rw [hDeriv]
  unfold normalizedXiMacroscopicQuotient
  field_simp [hAnchorNe, hzNe]

theorem xiMacroscopicQuotient_logDerivative_norm_le_top
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    norm (deriv (xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      (2 * anchoredXiMacroscopicRealPartEnvelope T) /
        xiMacroscopicLocalRadius T := by
  let c := TS300.Goldbach.finiteGridTopHorizontalPoint T sigma
  have hcControl : Membership.mem
      (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) c := by
    rw [Metric.mem_closedBall]
    have hBound : (T : Real) + 5 <= xiMacroscopicControlRadius T := by
      change (T : Real) + 5 <= (16 : Real) * ((T : Real) + 4)
      nlinarith [(Nat.cast_nonneg T : (0 : Real) <= (T : Real))]
    exact (finiteGridHorizontalPoint_dist_anchor_le T sigma hSigma).trans hBound
  rw [<- normalizedXiMacroscopicQuotient_logDeriv_eq T c hcControl]
  exact (finiteGridTopMacroscopicLocalLogData T sigma hSigma).logDerivative_norm_le

theorem xiMacroscopicQuotient_logDerivative_norm_le_bottom
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    norm (deriv (xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      (2 * anchoredXiMacroscopicRealPartEnvelope T) /
        xiMacroscopicLocalRadius T := by
  let c := TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma
  have hcControl : Membership.mem
      (Metric.closedBall xiMacroscopicAnchor (xiMacroscopicControlRadius T)) c := by
    rw [Metric.mem_closedBall]
    have hBound : (T : Real) + 5 <= xiMacroscopicControlRadius T := by
      change (T : Real) + 5 <= (16 : Real) * ((T : Real) + 4)
      nlinarith [(Nat.cast_nonneg T : (0 : Real) <= (T : Real))]
    exact (finiteGridBottomHorizontalPoint_dist_anchor_le T sigma hSigma).trans hBound
  rw [<- normalizedXiMacroscopicQuotient_logDeriv_eq T c hcControl]
  exact (finiteGridBottomMacroscopicLocalLogData T sigma hSigma).logDerivative_norm_le

/-! ## Exact finite bridge to the height quotient -/

/-- Rational logarithmic derivative of the macroscopic zero polynomial. -/
noncomputable def xiMacroscopicFiniteZeroLogDerivativeSum
    (T : Nat)
    (s : Complex) : Complex :=
  Finset.sum (xiMacroscopicSpec T).factorZeros
    (fun rho =>
      (xiMacroscopicSpec T).multiplicity rho / (s - rho))

/-- Explicit finite correction between macroscopic and height selections. -/
noncomputable def xiMacroscopicHeightFiniteCorrection
    (T : Nat)
    (s : Complex) : Complex :=
  xiMacroscopicFiniteZeroLogDerivativeSum T s -
    TS295.Goldbach.finiteZeroLogDerivativeSum T s

theorem xiMacroscopicZeroPolynomial_logDeriv
    (T : Nat)
    (s : Complex)
    (hAvoid : forall rho : Complex,
      Membership.mem (xiMacroscopicSpec T).factorZeros rho -> Not (s = rho)) :
    deriv
        (TS275.Goldbach.finiteJensenZeroPolynomial
          (xiMacroscopicSpec T).toJensenFactorZeroData) s /
      TS275.Goldbach.finiteJensenZeroPolynomial
          (xiMacroscopicSpec T).toJensenFactorZeroData s =
        xiMacroscopicFiniteZeroLogDerivativeSum T s := by
  classical
  change logDeriv
      (fun z : Complex => Finset.prod (xiMacroscopicSpec T).factorZeros
        (fun rho => (z - rho) ^ (xiMacroscopicSpec T).multiplicity rho)) s =
    xiMacroscopicFiniteZeroLogDerivativeSum T s
  unfold xiMacroscopicFiniteZeroLogDerivativeSum
  rw [logDeriv_prod]
  next =>
    apply Finset.sum_congr rfl
    intro rho hRho
    calc
      logDeriv
          (fun z : Complex =>
            (z - rho) ^ (xiMacroscopicSpec T).multiplicity rho) s =
        ((xiMacroscopicSpec T).multiplicity rho : Complex) *
          logDeriv (fun z : Complex => z - rho) s := by
            simpa using
              (logDeriv_fun_pow
                (differentiableAt_id.sub_const rho)
                ((xiMacroscopicSpec T).multiplicity rho))
      _ = ((xiMacroscopicSpec T).multiplicity rho : Complex) /
          (s - rho) := by
            simp [logDeriv_apply, hAvoid rho hRho, div_eq_mul_inv]
  next =>
    intro rho hRho
    exact pow_ne_zero _ (sub_ne_zero.mpr (hAvoid rho hRho))
  next =>
    intro rho _
    exact (differentiableAt_id.sub_const rho).pow _

theorem xiMacroscopicQuotient_logDerivative_identity
    (T : Nat)
    (s : Complex)
    (hXi : Not (TS282.Goldbach.riemannXiCandidate s = 0))
    (hAvoid : forall rho : Complex,
      Membership.mem (xiMacroscopicSpec T).factorZeros rho -> Not (s = rho)) :
    deriv TS282.Goldbach.riemannXiCandidate s /
        TS282.Goldbach.riemannXiCandidate s =
      xiMacroscopicFiniteZeroLogDerivativeSum T s +
        deriv (xiMacroscopicQuotient T) s /
          xiMacroscopicQuotient T s := by
  have hPolyNe :
      Not (TS275.Goldbach.finiteJensenZeroPolynomial
          (xiMacroscopicSpec T).toJensenFactorZeroData s = 0) := by
    exact TS275.Goldbach.finiteJensenZeroPolynomial_ne_zero_of_avoids_roots
      (xiMacroscopicSpec T).toJensenFactorZeroData s hAvoid
  have hXiDiff : DifferentiableAt Complex
      TS282.Goldbach.riemannXiCandidate s :=
    TS282.Goldbach.riemannXiCandidate_entire.differentiableAt
  have hPolyDiff :=
    (TS275.Goldbach.finiteJensenZeroPolynomial_analyticAt
      (xiMacroscopicSpec T).toJensenFactorZeroData s).differentiableAt
  have hDiv := logDeriv_div s hXi hPolyNe hXiDiff hPolyDiff
  change logDeriv TS282.Goldbach.riemannXiCandidate s =
    xiMacroscopicFiniteZeroLogDerivativeSum T s +
      logDeriv (xiMacroscopicQuotient T) s
  rw [<- xiMacroscopicZeroPolynomial_logDeriv T s hAvoid]
  have hQuotientEq : Filter.EventuallyEq (nhds s)
      (xiMacroscopicQuotient T)
      (fun z => TS282.Goldbach.riemannXiCandidate z /
        TS275.Goldbach.finiteJensenZeroPolynomial
          (xiMacroscopicSpec T).toJensenFactorZeroData z) := by
    have hAvoidRoots : Filter.Eventually
        (fun z => Not (Membership.mem (xiMacroscopicSpec T).factorZeros z))
        (nhds s) :=
      (xiMacroscopicSpec T).factorZeros.isClosed.isOpen_compl.mem_nhds (by
        intro hs
        exact hAvoid s hs rfl)
    filter_upwards [hAvoidRoots] with z hz
    simp [xiMacroscopicQuotient, TS285.Goldbach.riemannXiFiniteQuotient, hz]
  have hLogDerivEq : logDeriv (xiMacroscopicQuotient T) s =
      logDeriv
        (fun z => TS282.Goldbach.riemannXiCandidate z /
          TS275.Goldbach.finiteJensenZeroPolynomial
            (xiMacroscopicSpec T).toJensenFactorZeroData z) s := by
    simp only [logDeriv_apply]
    rw [hQuotientEq.deriv_eq, hQuotientEq.eq_of_nhds]
  rw [hLogDerivEq]
  simp only [logDeriv_apply] at hDiv
  simp only [logDeriv_apply]
  linear_combination -hDiv

theorem heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection
    (T : Nat)
    (s : Complex)
    (hXi : Not (TS282.Goldbach.riemannXiCandidate s = 0))
    (hHeightPolynomial : Not (TS296.Goldbach.heightZeroPolynomial T s = 0))
    (hHeightAvoid : forall rho : TS292.Goldbach.ConcreteNontrivialZero,
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho -> Not (s = rho.1))
    (hMacroAvoid : forall rho : Complex,
      Membership.mem (xiMacroscopicSpec T).factorZeros rho -> Not (s = rho)) :
    deriv (TS296.Goldbach.heightXiQuotient T) s /
        TS296.Goldbach.heightXiQuotient T s =
      deriv (xiMacroscopicQuotient T) s /
          xiMacroscopicQuotient T s +
        xiMacroscopicHeightFiniteCorrection T s := by
  have hHeight := TS296.Goldbach.heightXiQuotient_logDerivative_identity
    T s hXi hHeightPolynomial hHeightAvoid
  have hMacro := xiMacroscopicQuotient_logDerivative_identity
    T s hXi hMacroAvoid
  unfold xiMacroscopicHeightFiniteCorrection
  linear_combination hMacro - hHeight

theorem riemannXiCandidate_ne_zero_at_finiteGridTop
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    Not (TS282.Goldbach.riemannXiCandidate
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) = 0) := by
  let s := TS300.Goldbach.finiteGridTopHorizontalPoint T sigma
  have hIm : Not (s.im = 0) := by
    dsimp [s]
    simp [TS300.Goldbach.finiteGridTopHorizontalPoint,
      ne_of_gt (TS299.Goldbach.finiteGridStrongTau_pos hT)]
  have hZeta : Not (riemannZeta s = 0) := by
    exact TS299.Goldbach.riemannZeta_ne_zero_on_finiteGridStrong_top
      T hT sigma hSigma.1 hSigma.2
  rw [TS297.Goldbach.riemannXiCandidate_eq_localMultiplier_mul_riemannZeta_of_im_ne_zero
    hIm]
  exact mul_ne_zero
    (TS297.Goldbach.xiZetaLocalMultiplier_ne_zero_of_im_ne_zero hIm) hZeta

theorem riemannXiCandidate_ne_zero_at_finiteGridBottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    Not (TS282.Goldbach.riemannXiCandidate
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) = 0) := by
  let s := TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma
  have hIm : Not (s.im = 0) := by
    dsimp [s]
    simp [TS300.Goldbach.finiteGridBottomHorizontalPoint,
      ne_of_gt (TS299.Goldbach.finiteGridStrongTau_pos hT)]
  have hZeta : Not (riemannZeta s = 0) := by
    exact TS299.Goldbach.riemannZeta_ne_zero_on_finiteGridStrong_bottom
      T hT sigma hSigma.1 hSigma.2
  rw [TS297.Goldbach.riemannXiCandidate_eq_localMultiplier_mul_riemannZeta_of_im_ne_zero
    hIm]
  exact mul_ne_zero
    (TS297.Goldbach.xiZetaLocalMultiplier_ne_zero_of_im_ne_zero hIm) hZeta

theorem finiteGridTop_avoids_heightZeros
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    forall rho : TS292.Goldbach.ConcreteNontrivialZero,
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho ->
        Not (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma = rho.1) := by
  intro rho hRho hEq
  apply TS299.Goldbach.finiteGridStrong_gap_ne_zero T rho hRho
  have hIm := congrArg Complex.im hEq
  have hRhoIm : rho.1.im = TS299.Goldbach.finiteGridStrongTau T := by
    simpa [TS300.Goldbach.finiteGridTopHorizontalPoint] using hIm.symm
  rw [TS295.Goldbach.symmetricZeroHeightGap, hRhoIm,
    abs_of_pos (TS299.Goldbach.finiteGridStrongTau_pos hT)]
  simp

theorem finiteGridBottom_avoids_heightZeros
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    forall rho : TS292.Goldbach.ConcreteNontrivialZero,
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho ->
        Not (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma = rho.1) := by
  intro rho hRho hEq
  apply TS299.Goldbach.finiteGridStrong_gap_ne_zero T rho hRho
  have hIm := congrArg Complex.im hEq
  have hRhoIm : rho.1.im = -TS299.Goldbach.finiteGridStrongTau T := by
    simpa [TS300.Goldbach.finiteGridBottomHorizontalPoint] using hIm.symm
  rw [TS295.Goldbach.symmetricZeroHeightGap, hRhoIm, abs_neg,
    abs_of_pos (TS299.Goldbach.finiteGridStrongTau_pos hT)]
  simp

theorem heightZeroPolynomial_ne_zero_at_finiteGridTop
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Not (TS296.Goldbach.heightZeroPolynomial T
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) = 0) := by
  classical
  unfold TS296.Goldbach.heightZeroPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro rho hRho
  exact pow_ne_zero _ (sub_ne_zero.mpr
    (finiteGridTop_avoids_heightZeros T hT sigma rho hRho))

theorem heightZeroPolynomial_ne_zero_at_finiteGridBottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Not (TS296.Goldbach.heightZeroPolynomial T
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) = 0) := by
  classical
  unfold TS296.Goldbach.heightZeroPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro rho hRho
  exact pow_ne_zero _ (sub_ne_zero.mpr
    (finiteGridBottom_avoids_heightZeros T hT sigma rho hRho))

theorem finiteGridTop_avoids_macroscopicZeros
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    forall rho : Complex,
      Membership.mem (xiMacroscopicSpec T).factorZeros rho ->
        Not (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma = rho) := by
  intro rho hRho hEq
  apply riemannXiCandidate_ne_zero_at_finiteGridTop T hT sigma hSigma
  rw [hEq]
  exact (xiMacroscopicSpec T).factor_zero_is_xi_zero rho hRho

theorem finiteGridBottom_avoids_macroscopicZeros
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    forall rho : Complex,
      Membership.mem (xiMacroscopicSpec T).factorZeros rho ->
        Not (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma = rho) := by
  intro rho hRho hEq
  apply riemannXiCandidate_ne_zero_at_finiteGridBottom T hT sigma hSigma
  rw [hEq]
  exact (xiMacroscopicSpec T).factor_zero_is_xi_zero rho hRho

theorem heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    deriv (TS296.Goldbach.heightXiQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        TS296.Goldbach.heightXiQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) =
      deriv (xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) +
      xiMacroscopicHeightFiniteCorrection T
        (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) := by
  exact heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection
    T _
    (riemannXiCandidate_ne_zero_at_finiteGridTop T hT sigma hSigma)
    (heightZeroPolynomial_ne_zero_at_finiteGridTop T hT sigma)
    (finiteGridTop_avoids_heightZeros T hT sigma)
    (finiteGridTop_avoids_macroscopicZeros T hT sigma hSigma)

theorem heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem (Set.Icc TS294.Goldbach.fixedPerronLeft
      TS294.Goldbach.fixedPerronRight) sigma) :
    deriv (TS296.Goldbach.heightXiQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        TS296.Goldbach.heightXiQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) =
      deriv (xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) +
      xiMacroscopicHeightFiniteCorrection T
        (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) := by
  exact heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection
    T _
    (riemannXiCandidate_ne_zero_at_finiteGridBottom T hT sigma hSigma)
    (heightZeroPolynomial_ne_zero_at_finiteGridBottom T hT sigma)
    (finiteGridBottom_avoids_heightZeros T hT sigma)
    (finiteGridBottom_avoids_macroscopicZeros T hT sigma hSigma)

/-! ## Audit ledger -/

structure AnchoredMacroscopicXiQuotientLedger where
  fixed_anchor_nonzero_proved : Prop
  macroscopic_finite_quotient_constructed : Prop
  quotient_analytic_nonzero_on_control_ball : Prop
  anchored_logarithm_constructed : Prop
  branch_independent_compact_envelope_constructed : Prop
  borel_caratheodory_control_proved : Prop
  finite_grid_local_cauchy_data_constructed : Prop
  exact_height_macroscopic_bridge_proved : Prop
  local_mobile_minimum_modulus_not_used : Prop
  infinite_hadamard_product_not_used : Prop
  closed_anchored_envelope_rate_not_proved : Prop
  extra_finite_correction_decay_not_proved : Prop
  full_horizontal_decay_not_proved : Prop
  completion_correction_rate_not_proved : Prop
  fixed_left_boundary_not_proved : Prop
  exceptional_residues_not_completed : Prop
  perron_inversion_not_proved : Prop
  meromorphic_residue_theorem_not_proved : Prop
  infinite_explicit_formula_not_proved : Prop
  gallagher_not_proved : Prop
  otsa_not_proved : Prop
  goldbach_not_claimed : Prop

def anchoredMacroscopicXiQuotientLedger :
    AnchoredMacroscopicXiQuotientLedger where
  fixed_anchor_nonzero_proved := True
  macroscopic_finite_quotient_constructed := True
  quotient_analytic_nonzero_on_control_ball := True
  anchored_logarithm_constructed := True
  branch_independent_compact_envelope_constructed := True
  borel_caratheodory_control_proved := True
  finite_grid_local_cauchy_data_constructed := True
  exact_height_macroscopic_bridge_proved := True
  local_mobile_minimum_modulus_not_used := True
  infinite_hadamard_product_not_used := True
  closed_anchored_envelope_rate_not_proved := True
  extra_finite_correction_decay_not_proved := True
  full_horizontal_decay_not_proved := True
  completion_correction_rate_not_proved := True
  fixed_left_boundary_not_proved := True
  exceptional_residues_not_completed := True
  perron_inversion_not_proved := True
  meromorphic_residue_theorem_not_proved := True
  infinite_explicit_formula_not_proved := True
  gallagher_not_proved := True
  otsa_not_proved := True
  goldbach_not_claimed := True

end Goldbach
end TS301
