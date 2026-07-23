import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic
import TS.Goldbach.Strong.TS302.FiniteMacroscopicCorrectionDecay

/-!
# TS303 - Closed Anchored Macroscopic Envelope

TS301 replaced the moving minimum-modulus problem by an entire finite quotient
normalized at the fixed point `2`.  Its compact real-part envelope was genuine
but had no closed rate.  This sprint closes that rate on a new quantitative
outer circle.

For `r = 64 * (T + 4)`, every selected factor root has norm below `4 * r`.
The circle of radius `8 * r` is therefore separated from every factor root by
at least `4 * r`.  On that circle the finite polynomial ratio is controlled by
`(1 + 1 / (2 * r))` to the total selected multiplicity.  The closed xi growth
bound of TS289 and the multiplicity estimate of TS290 then give an explicit
quadratic envelope for the normalized quotient.

The maximum-modulus principle transports the boundary bound to the TS301
control ball.  The centered Borel-Caratheodory theorem from TS300 consequently
gives a closed logarithmic-derivative bound for the macroscopic quotient and a
vanishing horizontal contribution at every fixed arithmetic scale.

No minimum-modulus estimate at a moving point, infinite Hadamard product,
local zero-density estimate, Perron inversion, or residue theorem is used.
-/

noncomputable section

namespace TS303
namespace Goldbach

open Complex Filter Metric Set Topology
open scoped Topology

/-! ## Quantitative outer circle -/

/-- The outer radius is eight times the TS301 macroscopic factor radius. -/
noncomputable def xiMacroscopicOuterRadius (T : Nat) : Real :=
  8 * TS301.Goldbach.xiMacroscopicInnerRadius T

theorem xiMacroscopicOuterRadius_pos (T : Nat) :
    0 < xiMacroscopicOuterRadius T := by
  unfold xiMacroscopicOuterRadius
  exact mul_pos (by norm_num) (TS301.Goldbach.xiMacroscopicInnerRadius_pos T)

theorem xiMacroscopicOuterRadius_ge_two (T : Nat) :
    2 <= xiMacroscopicOuterRadius T := by
  unfold xiMacroscopicOuterRadius TS301.Goldbach.xiMacroscopicInnerRadius
  have hT : 0 <= (T : Real) := Nat.cast_nonneg T
  nlinarith

theorem macroscopicFactorRoot_norm_lt_four_inner
    (T : Nat)
    (rho : Complex)
    (hRho : Membership.mem (TS301.Goldbach.xiMacroscopicSpec T).factorZeros rho) :
    norm rho < 4 * TS301.Goldbach.xiMacroscopicInnerRadius T := by
  have hOpen :=
    (TS301.Goldbach.xiMacroscopicSpec T).factor_zero_mem_open_disk rho hRho
  rw [(TS301.Goldbach.xiMacroscopicSpec T).center_eq_zero] at hOpen
  have hAbs : Complex.abs rho <
      (TS301.Goldbach.xiMacroscopicSpec T).config.averagingRadius := by
    simpa [Metric.mem_ball, dist_zero_right, Complex.norm_eq_abs] using hOpen
  have hAnalytic :=
    TS302.Goldbach.xiMacroscopicSpec_analyticRadius_lt_countingRadius T
  have hRadius : Complex.abs rho <
      4 * TS301.Goldbach.xiMacroscopicInnerRadius T :=
    (hAbs.trans
      (TS301.Goldbach.xiMacroscopicSpec T).config.averagingRadius_lt_analyticRadius).trans
        hAnalytic
  simpa [Complex.norm_eq_abs] using hRadius

theorem macroscopicFactorRoot_anchor_dist_le
    (T : Nat)
    (rho : Complex)
    (hRho : Membership.mem (TS301.Goldbach.xiMacroscopicSpec T).factorZeros rho) :
    norm (TS301.Goldbach.xiMacroscopicAnchor - rho) <=
      4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2 := by
  have hRoot := (macroscopicFactorRoot_norm_lt_four_inner T rho hRho).le
  have hAnchor : norm TS301.Goldbach.xiMacroscopicAnchor = 2 := by
    norm_num [TS301.Goldbach.xiMacroscopicAnchor]
  calc
    norm (TS301.Goldbach.xiMacroscopicAnchor - rho) <=
        norm TS301.Goldbach.xiMacroscopicAnchor + norm rho := norm_sub_le _ _
    _ <= 2 + 4 * TS301.Goldbach.xiMacroscopicInnerRadius T := by
      rw [hAnchor]
      linarith
    _ = 4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2 := by ring

theorem macroscopicFactorRoot_outer_dist_ge
    (T : Nat)
    (z rho : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T)
    (hRho : Membership.mem (TS301.Goldbach.xiMacroscopicSpec T).factorZeros rho) :
    4 * TS301.Goldbach.xiMacroscopicInnerRadius T <= norm (z - rho) := by
  have hRoot := macroscopicFactorRoot_norm_lt_four_inner T rho hRho
  have hReverse : norm z - norm rho <= norm (z - rho) := by
    linarith [norm_sub_norm_le z rho]
  rw [hz, xiMacroscopicOuterRadius] at hReverse
  linarith

/-! ## Finite polynomial bounds -/

/-- The finite polynomial selected by the TS301 macroscopic specification. -/
noncomputable def xiMacroscopicZeroPolynomial (T : Nat) : Complex -> Complex :=
  TS275.Goldbach.finiteJensenZeroPolynomial
    (TS301.Goldbach.xiMacroscopicSpec T).toJensenFactorZeroData

theorem xiMacroscopicZeroPolynomial_anchor_norm_le
    (T : Nat) :
    norm (xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor) <=
      (4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2) ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
  classical
  unfold xiMacroscopicZeroPolynomial
    TS275.Goldbach.finiteJensenZeroPolynomial
  simp only [norm_prod, norm_pow]
  calc
    Finset.prod (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        (fun rho =>
          norm (TS301.Goldbach.xiMacroscopicAnchor - rho) ^
            (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho) <=
      Finset.prod (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        (fun rho =>
          (4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2) ^
            (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho) := by
      refine Finset.prod_le_prod (fun rho hRho => pow_nonneg (norm_nonneg _) _) ?_
      intro rho hRho
      exact pow_le_pow_left (norm_nonneg _)
        (macroscopicFactorRoot_anchor_dist_le T rho hRho) _
    _ = (4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2) ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
      simpa [TS302.Goldbach.xiMacroscopicFactorMultiplicityCount] using
        (Finset.prod_pow_eq_pow_sum
          (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
          (TS301.Goldbach.xiMacroscopicSpec T).multiplicity
          (4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2))

theorem xiMacroscopicZeroPolynomial_outer_norm_ge
    (T : Nat)
    (z : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T) :
    (4 * TS301.Goldbach.xiMacroscopicInnerRadius T) ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T <=
      norm (xiMacroscopicZeroPolynomial T z) := by
  classical
  have hFourInnerNonnegative :
      0 <= 4 * TS301.Goldbach.xiMacroscopicInnerRadius T :=
    (mul_pos (by norm_num) (TS301.Goldbach.xiMacroscopicInnerRadius_pos T)).le
  unfold xiMacroscopicZeroPolynomial
    TS275.Goldbach.finiteJensenZeroPolynomial
  simp only [norm_prod, norm_pow]
  calc
    (4 * TS301.Goldbach.xiMacroscopicInnerRadius T) ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T =
      Finset.prod (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        (fun rho =>
          (4 * TS301.Goldbach.xiMacroscopicInnerRadius T) ^
            (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho) := by
      simpa [TS302.Goldbach.xiMacroscopicFactorMultiplicityCount] using
        (Finset.prod_pow_eq_pow_sum
          (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
          (TS301.Goldbach.xiMacroscopicSpec T).multiplicity
          (4 * TS301.Goldbach.xiMacroscopicInnerRadius T)).symm
    _ <= Finset.prod (TS301.Goldbach.xiMacroscopicSpec T).factorZeros
        (fun rho =>
          norm (z - rho) ^
            (TS301.Goldbach.xiMacroscopicSpec T).multiplicity rho) := by
      refine Finset.prod_le_prod
        (fun rho hRho => pow_nonneg hFourInnerNonnegative _) ?_
      intro rho hRho
      exact pow_le_pow_left hFourInnerNonnegative
        (macroscopicFactorRoot_outer_dist_ge T z rho hz hRho) _

theorem xiMacroscopicZeroPolynomial_outer_ne_zero
    (T : Nat)
    (z : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T) :
    Not (xiMacroscopicZeroPolynomial T z = 0) := by
  have hBase : 0 < 4 * TS301.Goldbach.xiMacroscopicInnerRadius T := by
    exact mul_pos (by norm_num) (TS301.Goldbach.xiMacroscopicInnerRadius_pos T)
  have hLower := xiMacroscopicZeroPolynomial_outer_norm_ge T z hz
  have hPower : 0 <
      (4 * TS301.Goldbach.xiMacroscopicInnerRadius T) ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
    positivity
  exact norm_ne_zero_iff.mp (by linarith)

theorem xiMacroscopicZeroPolynomial_anchor_ne_zero (T : Nat) :
    Not (xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor = 0) := by
  intro hZero
  have hFactor := TS285.Goldbach.riemannXiFiniteQuotient_factorization
    (TS301.Goldbach.xiMacroscopicSpec T) TS301.Goldbach.xiMacroscopicAnchor
  change TS282.Goldbach.riemannXiCandidate TS301.Goldbach.xiMacroscopicAnchor =
      xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor *
        TS301.Goldbach.xiMacroscopicQuotient T TS301.Goldbach.xiMacroscopicAnchor at hFactor
  rw [hZero, zero_mul] at hFactor
  exact TS301.Goldbach.riemannXiCandidate_ne_zero_at_macroscopicAnchor hFactor

/-- Per-root polynomial ratio base on the quantitative outer circle. -/
noncomputable def xiMacroscopicPolynomialRatioBase (T : Nat) : Real :=
  1 + 1 / (2 * TS301.Goldbach.xiMacroscopicInnerRadius T)

theorem xiMacroscopicPolynomialRatioBase_pos (T : Nat) :
    0 < xiMacroscopicPolynomialRatioBase T := by
  unfold xiMacroscopicPolynomialRatioBase
  have hInner := TS301.Goldbach.xiMacroscopicInnerRadius_pos T
  positivity

theorem xiMacroscopicZeroPolynomial_ratio_norm_le
    (T : Nat)
    (z : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T) :
    norm (xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor /
        xiMacroscopicZeroPolynomial T z) <=
      xiMacroscopicPolynomialRatioBase T ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
  rw [norm_div]
  have hUpper := xiMacroscopicZeroPolynomial_anchor_norm_le T
  have hLower := xiMacroscopicZeroPolynomial_outer_norm_ge T z hz
  have hDenPos : 0 < norm (xiMacroscopicZeroPolynomial T z) :=
    norm_pos_iff.mpr (xiMacroscopicZeroPolynomial_outer_ne_zero T z hz)
  have hBasePos : 0 < 4 * TS301.Goldbach.xiMacroscopicInnerRadius T := by
    exact mul_pos (by norm_num) (TS301.Goldbach.xiMacroscopicInnerRadius_pos T)
  calc
    norm (xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor) /
        norm (xiMacroscopicZeroPolynomial T z) <=
      (4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2) ^
          TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T /
        (4 * TS301.Goldbach.xiMacroscopicInnerRadius T) ^
          TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
      exact div_le_div (by positivity) hUpper (by positivity) hLower
    _ = ((4 * TS301.Goldbach.xiMacroscopicInnerRadius T + 2) /
          (4 * TS301.Goldbach.xiMacroscopicInnerRadius T)) ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
      rw [div_pow]
    _ = xiMacroscopicPolynomialRatioBase T ^
        TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T := by
      congr 1
      unfold xiMacroscopicPolynomialRatioBase
      field_simp [TS301.Goldbach.xiMacroscopicInnerRadius_pos T |>.ne']
      ring

/-! ## Closed boundary bound for the normalized quotient -/

/-- TS289's closed xi majorant evaluated on the quantitative outer circle. -/
noncomputable def xiMacroscopicOuterXiMajorant (T : Nat) : Real :=
  TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
    TS289.Goldbach.completedZetaThetaClosedMajorant
    (xiMacroscopicOuterRadius T)

theorem xiMacroscopicOuterXiMajorant_pos (T : Nat) :
    0 < xiMacroscopicOuterXiMajorant T := by
  exact TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta_positive _ _

theorem riemannXiCandidate_norm_le_outerXiMajorant
    (T : Nat)
    (z : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T) :
    norm (TS282.Goldbach.riemannXiCandidate z) <=
      xiMacroscopicOuterXiMajorant T := by
  have h := TS287.Goldbach.xi_abs_le_boundaryMajorantFromCompletedZeta
    TS289.Goldbach.completedZetaThetaClosedCircleGrowth
    (xiMacroscopicOuterRadius T)
    (xiMacroscopicOuterRadius_ge_two T)
    z
    (by simpa [Complex.norm_eq_abs] using hz)
  simpa [TS.Goldbach.MasterAPI.xi, Complex.norm_eq_abs,
    xiMacroscopicOuterXiMajorant] using h

/-- Fixed positive norm at the normalization point `2`. -/
noncomputable def xiMacroscopicAnchorNorm : Real :=
  norm (TS282.Goldbach.riemannXiCandidate TS301.Goldbach.xiMacroscopicAnchor)

theorem xiMacroscopicAnchorNorm_pos : 0 < xiMacroscopicAnchorNorm := by
  unfold xiMacroscopicAnchorNorm
  exact norm_pos_iff.mpr
    TS301.Goldbach.riemannXiCandidate_ne_zero_at_macroscopicAnchor

/-- Closed boundary module bound for `Q_T(z) / Q_T(2)`. -/
noncomputable def xiMacroscopicNormalizedBoundaryMajorant (T : Nat) : Real :=
  xiMacroscopicOuterXiMajorant T / xiMacroscopicAnchorNorm *
    xiMacroscopicPolynomialRatioBase T ^
      TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T

theorem xiMacroscopicNormalizedBoundaryMajorant_pos (T : Nat) :
    0 < xiMacroscopicNormalizedBoundaryMajorant T := by
  unfold xiMacroscopicNormalizedBoundaryMajorant
  exact mul_pos
    (div_pos (xiMacroscopicOuterXiMajorant_pos T) xiMacroscopicAnchorNorm_pos)
    (pow_pos (xiMacroscopicPolynomialRatioBase_pos T) _)

theorem normalizedXiMacroscopicQuotient_eq_xi_mul_polynomial_ratio
    (T : Nat)
    (z : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T) :
    TS301.Goldbach.normalizedXiMacroscopicQuotient T z =
      (TS282.Goldbach.riemannXiCandidate z /
          TS282.Goldbach.riemannXiCandidate TS301.Goldbach.xiMacroscopicAnchor) *
        (xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor /
          xiMacroscopicZeroPolynomial T z) := by
  have hPz := xiMacroscopicZeroPolynomial_outer_ne_zero T z hz
  have hPa := xiMacroscopicZeroPolynomial_anchor_ne_zero T
  have hQa := TS301.Goldbach.xiMacroscopicQuotient_ne_zero_at_anchor T
  have hXiA := TS301.Goldbach.riemannXiCandidate_ne_zero_at_macroscopicAnchor
  have hFactorZ := TS285.Goldbach.riemannXiFiniteQuotient_factorization
    (TS301.Goldbach.xiMacroscopicSpec T) z
  have hFactorA := TS285.Goldbach.riemannXiFiniteQuotient_factorization
    (TS301.Goldbach.xiMacroscopicSpec T) TS301.Goldbach.xiMacroscopicAnchor
  change TS282.Goldbach.riemannXiCandidate z =
      xiMacroscopicZeroPolynomial T z *
        TS301.Goldbach.xiMacroscopicQuotient T z at hFactorZ
  change TS282.Goldbach.riemannXiCandidate TS301.Goldbach.xiMacroscopicAnchor =
      xiMacroscopicZeroPolynomial T TS301.Goldbach.xiMacroscopicAnchor *
        TS301.Goldbach.xiMacroscopicQuotient T TS301.Goldbach.xiMacroscopicAnchor at hFactorA
  unfold TS301.Goldbach.normalizedXiMacroscopicQuotient
  rw [hFactorZ, hFactorA]
  field_simp [hPz, hPa, hQa, hXiA]
  ring

theorem normalizedXiMacroscopicQuotient_norm_le_boundary
    (T : Nat)
    (z : Complex)
    (hz : norm z = xiMacroscopicOuterRadius T) :
    norm (TS301.Goldbach.normalizedXiMacroscopicQuotient T z) <=
      xiMacroscopicNormalizedBoundaryMajorant T := by
  rw [normalizedXiMacroscopicQuotient_eq_xi_mul_polynomial_ratio T z hz]
  rw [norm_mul]
  have hXi := riemannXiCandidate_norm_le_outerXiMajorant T z hz
  have hPolynomial := xiMacroscopicZeroPolynomial_ratio_norm_le T z hz
  have hXiRatio :
      norm
          (TS282.Goldbach.riemannXiCandidate z /
            TS282.Goldbach.riemannXiCandidate TS301.Goldbach.xiMacroscopicAnchor) <=
        xiMacroscopicOuterXiMajorant T / xiMacroscopicAnchorNorm := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right hXi xiMacroscopicAnchorNorm_pos.le
  unfold xiMacroscopicNormalizedBoundaryMajorant
  exact mul_le_mul hXiRatio hPolynomial (norm_nonneg _)
    (div_nonneg (xiMacroscopicOuterXiMajorant_pos T).le
      xiMacroscopicAnchorNorm_pos.le)

/-! ## Maximum-modulus transport -/

theorem normalizedXiMacroscopicQuotient_analyticAt
    (T : Nat)
    (z : Complex) :
    AnalyticAt Complex (TS301.Goldbach.normalizedXiMacroscopicQuotient T) z := by
  unfold TS301.Goldbach.normalizedXiMacroscopicQuotient
  exact (TS285.Goldbach.riemannXiFiniteQuotient_analyticAt
    (TS301.Goldbach.xiMacroscopicSpec T) z).div analyticAt_const
      (TS301.Goldbach.xiMacroscopicQuotient_ne_zero_at_anchor T)

theorem normalizedXiMacroscopicQuotient_norm_le_outerClosedBall
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem (Metric.closedBall 0 (xiMacroscopicOuterRadius T)) z) :
    norm (TS301.Goldbach.normalizedXiMacroscopicQuotient T z) <=
      xiMacroscopicNormalizedBoundaryMajorant T := by
  have hRPos := xiMacroscopicOuterRadius_pos T
  have hDiff : DiffContOnCl Complex
      (TS301.Goldbach.normalizedXiMacroscopicQuotient T)
      (Metric.ball 0 (xiMacroscopicOuterRadius T)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact (normalizedXiMacroscopicQuotient_analyticAt T w).differentiableAt
      |>.differentiableWithinAt
  have hBoundary : forall w,
      Membership.mem (frontier (Metric.ball 0 (xiMacroscopicOuterRadius T))) w ->
        norm (TS301.Goldbach.normalizedXiMacroscopicQuotient T w) <=
          xiMacroscopicNormalizedBoundaryMajorant T := by
    intro w hw
    rw [frontier_ball 0 hRPos.ne'] at hw
    apply normalizedXiMacroscopicQuotient_norm_le_boundary T w
    simpa [Metric.mem_sphere, dist_zero_right] using hw
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hDiff hBoundary
  rw [closure_ball 0 hRPos.ne']
  exact hz

theorem anchoredControlClosedBall_subset_outerClosedBall (T : Nat) :
    Metric.closedBall TS301.Goldbach.xiMacroscopicAnchor
        (TS301.Goldbach.xiMacroscopicControlRadius T) <=
      Metric.closedBall 0 (xiMacroscopicOuterRadius T) := by
  intro z hz
  rw [Metric.mem_closedBall] at hz
  change dist z TS301.Goldbach.xiMacroscopicAnchor <=
    16 * ((T : Real) + 4) at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hAnchor : norm TS301.Goldbach.xiMacroscopicAnchor = 2 := by
    norm_num [TS301.Goldbach.xiMacroscopicAnchor]
  have hNorm : norm z <=
      dist z TS301.Goldbach.xiMacroscopicAnchor +
        norm TS301.Goldbach.xiMacroscopicAnchor := by
    calc
      norm z = norm
          ((z - TS301.Goldbach.xiMacroscopicAnchor) +
            TS301.Goldbach.xiMacroscopicAnchor) := by ring_nf
      _ <= norm (z - TS301.Goldbach.xiMacroscopicAnchor) +
          norm TS301.Goldbach.xiMacroscopicAnchor := norm_add_le _ _
      _ = dist z TS301.Goldbach.xiMacroscopicAnchor +
          norm TS301.Goldbach.xiMacroscopicAnchor := by
        simp [dist_eq, Complex.norm_eq_abs]
  unfold xiMacroscopicOuterRadius TS301.Goldbach.xiMacroscopicInnerRadius
  rw [hAnchor] at hNorm
  have hT : 0 <= (T : Real) := Nat.cast_nonneg T
  nlinarith

theorem normalizedXiMacroscopicQuotient_norm_le_controlBall
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem
      (Metric.closedBall TS301.Goldbach.xiMacroscopicAnchor
        (TS301.Goldbach.xiMacroscopicControlRadius T)) z) :
    norm (TS301.Goldbach.normalizedXiMacroscopicQuotient T z) <=
      xiMacroscopicNormalizedBoundaryMajorant T := by
  exact normalizedXiMacroscopicQuotient_norm_le_outerClosedBall T z
    (anchoredControlClosedBall_subset_outerClosedBall T hz)

/-! ## A closed real-part envelope -/

/-- Fixed cost of normalizing at the nonzero anchor. -/
noncomputable def xiMacroscopicAnchorLogCost : Real :=
  max 0 (-Real.log xiMacroscopicAnchorNorm)

theorem xiMacroscopicAnchorLogCost_nonnegative :
    0 <= xiMacroscopicAnchorLogCost := by
  exact le_max_left _ _

theorem neg_log_anchorNorm_le_cost :
    -Real.log xiMacroscopicAnchorNorm <= xiMacroscopicAnchorLogCost := by
  exact le_max_right _ _

/-- Elementary logarithmic estimate for the closed TS289 xi majorant. -/
theorem xiMacroscopicOuterXiMajorant_log_le
    (T : Nat) :
    Real.log (xiMacroscopicOuterXiMajorant T) <=
      (xiMacroscopicOuterRadius T + 3) *
          Real.log (xiMacroscopicOuterRadius T + 2) +
        TS289.Goldbach.completedZetaThetaTailConstant := by
  let R := xiMacroscopicOuterRadius T
  let C := TS289.Goldbach.completedZetaThetaTailConstant
  let E := R * Real.log (R + 2)
  let X := R * (R + 1) * (C * Real.exp E)
  have hR2 : 2 <= R := xiMacroscopicOuterRadius_ge_two T
  have hRPos : 0 < R := lt_of_lt_of_le (by norm_num) hR2
  have hC2 : 2 <= C := TS290.Goldbach.two_le_completedZetaThetaTailConstant
  have hCPos : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hLogNonnegative : 0 <= Real.log (R + 2) := by
    apply Real.log_nonneg
    linarith
  have hENonnegative : 0 <= E := mul_nonneg hRPos.le hLogNonnegative
  have hExpOne : 1 <= Real.exp E := Real.one_le_exp hENonnegative
  have hProdOne : 6 <= R * (R + 1) := by
    have hNonnegative : 0 <= (R - 2) * (R + 3) :=
      mul_nonneg (sub_nonneg.mpr hR2) (by linarith)
    nlinarith
  have hProdTwo : 12 <= R * (R + 1) * C := by
    have h := mul_le_mul hProdOne hC2
      (by norm_num : (0 : Real) <= 2)
      (by linarith : 0 <= R * (R + 1))
    norm_num at h
    exact h
  have hX12 : 12 <= X := by
    have h := mul_le_mul hProdTwo hExpOne
      (by norm_num : (0 : Real) <= 1)
      (by linarith : 0 <= R * (R + 1) * C)
    norm_num at h
    simpa [X, mul_assoc] using h
  have hXPos : 0 < X := by linarith
  have hMax : max 1 ((X + 1) / 2) = (X + 1) / 2 := by
    rw [max_eq_right]
    linarith
  have hMajorantEq : xiMacroscopicOuterXiMajorant T = (X + 1) / 2 := by
    unfold xiMacroscopicOuterXiMajorant
      TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
      TS289.Goldbach.completedZetaThetaClosedMajorant
    change max 1 ((X + 1) / 2) = (X + 1) / 2
    exact hMax
  have hMajorantLeX : xiMacroscopicOuterXiMajorant T <= X := by
    rw [hMajorantEq]
    linarith
  have hLogX : Real.log X =
      Real.log R + Real.log (R + 1) + Real.log C + E := by
    dsimp [X]
    rw [Real.log_mul (mul_ne_zero hRPos.ne' (by linarith))
      (mul_ne_zero hCPos.ne' (Real.exp_pos E).ne')]
    rw [Real.log_mul hRPos.ne' (by linarith)]
    rw [Real.log_mul hCPos.ne' (Real.exp_pos E).ne']
    rw [Real.log_exp]
    ring
  have hLogMajorant : Real.log (xiMacroscopicOuterXiMajorant T) <= Real.log X :=
    Real.strictMonoOn_log.monotoneOn
      (xiMacroscopicOuterXiMajorant_pos T) hXPos hMajorantLeX
  have hLogC : Real.log C <= C :=
    (Real.log_le_sub_one_of_pos hCPos).trans (by linarith)
  have hLogR : Real.log R <= Real.log (R + 2) :=
    Real.strictMonoOn_log.monotoneOn hRPos
      (add_pos hRPos (by norm_num)) (le_add_of_nonneg_right (by norm_num))
  have hLogRSucc : Real.log (R + 1) <= Real.log (R + 2) :=
    Real.strictMonoOn_log.monotoneOn
      (add_pos hRPos (by norm_num))
      (add_pos hRPos (by norm_num))
      (by linarith)
  apply hLogMajorant.trans
  rw [hLogX]
  dsimp [E]
  nlinarith

theorem xiMacroscopicPolynomialRatioBase_log_le
    (T : Nat) :
    Real.log (xiMacroscopicPolynomialRatioBase T) <=
      1 / (2 * TS301.Goldbach.xiMacroscopicInnerRadius T) := by
  have hBasePos := xiMacroscopicPolynomialRatioBase_pos T
  have h := Real.log_le_sub_one_of_pos hBasePos
  unfold xiMacroscopicPolynomialRatioBase at h
  unfold xiMacroscopicPolynomialRatioBase
  linarith

/-- Exact logarithm of the positive boundary module majorant. -/
theorem log_xiMacroscopicNormalizedBoundaryMajorant
    (T : Nat) :
    Real.log (xiMacroscopicNormalizedBoundaryMajorant T) =
      Real.log (xiMacroscopicOuterXiMajorant T) -
        Real.log xiMacroscopicAnchorNorm +
      (TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T : Real) *
        Real.log (xiMacroscopicPolynomialRatioBase T) := by
  unfold xiMacroscopicNormalizedBoundaryMajorant
  rw [Real.log_mul
      (div_ne_zero (xiMacroscopicOuterXiMajorant_pos T).ne'
        xiMacroscopicAnchorNorm_pos.ne')
      (pow_ne_zero _ (xiMacroscopicPolynomialRatioBase_pos T).ne')]
  rw [Real.log_div (xiMacroscopicOuterXiMajorant_pos T).ne'
    xiMacroscopicAnchorNorm_pos.ne']
  rw [Real.log_pow]

/-- A deliberately generous quadratic closed envelope. -/
noncomputable def xiMacroscopicClosedEnvelopeConstant : Real :=
  263171 + TS289.Goldbach.completedZetaThetaTailConstant +
    xiMacroscopicAnchorLogCost +
    514 * TS290.Goldbach.xiDyadicLogLinearConstant

noncomputable def xiMacroscopicClosedRealPartEnvelope (T : Nat) : Real :=
  xiMacroscopicClosedEnvelopeConstant * ((T : Real) + 4) ^ 2

theorem xiMacroscopicClosedEnvelopeConstant_pos :
    0 < xiMacroscopicClosedEnvelopeConstant := by
  unfold xiMacroscopicClosedEnvelopeConstant
  have hTheta := TS289.Goldbach.completedZetaThetaTailConstant_pos
  have hAnchor := xiMacroscopicAnchorLogCost_nonnegative
  have hCount := TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
  nlinarith

theorem xiMacroscopicClosedRealPartEnvelope_pos (T : Nat) :
    0 < xiMacroscopicClosedRealPartEnvelope T := by
  unfold xiMacroscopicClosedRealPartEnvelope
  have hU : 0 < (T : Real) + 4 := by positivity
  exact mul_pos xiMacroscopicClosedEnvelopeConstant_pos (sq_pos_of_pos hU)

theorem xiMacroscopicPolynomialLogCost_le_closed
    (T : Nat) :
    (TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T : Real) *
        Real.log (xiMacroscopicPolynomialRatioBase T) <=
      514 * TS290.Goldbach.xiDyadicLogLinearConstant *
        ((T : Real) + 4) ^ 2 := by
  let M : Real := TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T
  let r : Real := TS301.Goldbach.xiMacroscopicInnerRadius T
  let C : Real := TS290.Goldbach.xiDyadicLogLinearConstant
  let u : Real := (T : Real) + 4
  have hu : 1 <= u := by
    dsimp [u]
    have hT : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hr : r = 64 * u := by rfl
  have hrPos : 0 < r := TS301.Goldbach.xiMacroscopicInnerRadius_pos T
  have hMNonnegative : 0 <= M := by
    dsimp [M]
    exact Nat.cast_nonneg _
  have hCNonnegative : 0 <= C :=
    TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
  have hLogCost :
      M * Real.log (xiMacroscopicPolynomialRatioBase T) <= M / (2 * r) := by
    have hLog := xiMacroscopicPolynomialRatioBase_log_le T
    change Real.log (xiMacroscopicPolynomialRatioBase T) <= 1 / (2 * r) at hLog
    have h := mul_le_mul_of_nonneg_left hLog hMNonnegative
    simpa [div_eq_mul_inv, mul_assoc] using h
  have hMClosed : M <= TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T := by
    exact TS302.Goldbach.xiMacroscopicFactorMultiplicityCount_le_closedEnvelope T
  have hDiv : M / (2 * r) <=
      TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T / (2 * r) := by
    exact div_le_div_of_nonneg_right hMClosed (by positivity)
  have hCountDiv :
      TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T / (2 * r) =
        2 * C * Real.log (256 * u + 2) := by
    unfold TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope
      TS302.Goldbach.xiMacroscopicCorrectionCountingRadius
    change (C * (4 * r) * Real.log (4 * r + 2)) / (2 * r) =
      2 * C * Real.log (256 * u + 2)
    rw [hr]
    field_simp
    ring
  have hLog : Real.log (256 * u + 2) <= 257 * u := by
    have hArgPos : 0 < 256 * u + 2 := by positivity
    have hBase := Real.log_le_sub_one_of_pos hArgPos
    linarith
  have hScaled : 2 * C * Real.log (256 * u + 2) <= 514 * C * u := by
    have hTwoC : 0 <= 2 * C := mul_nonneg (by norm_num) hCNonnegative
    have h := mul_le_mul_of_nonneg_left hLog hTwoC
    nlinarith
  have hUScale : 514 * C * u <= 514 * C * u ^ 2 := by
    have huNonnegative : 0 <= u := zero_le_one.trans hu
    have huSq : u <= u ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left huSq
      (mul_nonneg (by norm_num) hCNonnegative)
  calc
    (TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T : Real) *
        Real.log (xiMacroscopicPolynomialRatioBase T) =
      M * Real.log (xiMacroscopicPolynomialRatioBase T) := rfl
    _ <= M / (2 * r) := hLogCost
    _ <= TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T / (2 * r) := hDiv
    _ = 2 * C * Real.log (256 * u + 2) := hCountDiv
    _ <= 514 * C * u := hScaled
    _ <= 514 * C * u ^ 2 := hUScale
    _ = 514 * TS290.Goldbach.xiDyadicLogLinearConstant *
        ((T : Real) + 4) ^ 2 := rfl

theorem xiMacroscopicOuterXiLogTerm_le_quadratic
    (T : Nat) :
    (xiMacroscopicOuterRadius T + 3) *
        Real.log (xiMacroscopicOuterRadius T + 2) <=
      263169 * ((T : Real) + 4) ^ 2 := by
  let u : Real := (T : Real) + 4
  have hu : 1 <= u := by
    dsimp [u]
    have hT : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have huFour : 4 <= u := by
    dsimp [u]
    simpa using (add_le_add_right (Nat.cast_nonneg T) 4)
  have hR : xiMacroscopicOuterRadius T = 512 * u := by
    dsimp [xiMacroscopicOuterRadius, TS301.Goldbach.xiMacroscopicInnerRadius, u]
    ring
  have hFirst : xiMacroscopicOuterRadius T + 3 <= 513 * u := by
    rw [hR]
    linarith
  have hArgPos : 0 < xiMacroscopicOuterRadius T + 2 := by
    linarith [xiMacroscopicOuterRadius_pos T]
  have hLogBase := Real.log_le_sub_one_of_pos hArgPos
  have hLog : Real.log (xiMacroscopicOuterRadius T + 2) <= 513 * u := by
    rw [hR] at hLogBase
    rw [hR]
    linarith
  have hFirstNonnegative : 0 <= xiMacroscopicOuterRadius T + 3 := by
    linarith [xiMacroscopicOuterRadius_pos T]
  have hLogNonnegative : 0 <= Real.log (xiMacroscopicOuterRadius T + 2) := by
    apply Real.log_nonneg
    linarith [xiMacroscopicOuterRadius_pos T]
  calc
    (xiMacroscopicOuterRadius T + 3) *
        Real.log (xiMacroscopicOuterRadius T + 2) <=
      (513 * u) * (513 * u) :=
        mul_le_mul hFirst hLog hLogNonnegative
          (by positivity)
    _ = 263169 * u ^ 2 := by ring
    _ = 263169 * ((T : Real) + 4) ^ 2 := rfl

theorem log_normalizedBoundaryMajorant_lt_closedEnvelope
    (T : Nat) :
    Real.log (xiMacroscopicNormalizedBoundaryMajorant T) <
      xiMacroscopicClosedRealPartEnvelope T := by
  let u : Real := (T : Real) + 4
  let Ctheta : Real := TS289.Goldbach.completedZetaThetaTailConstant
  let Canchor : Real := xiMacroscopicAnchorLogCost
  let Ccount : Real := TS290.Goldbach.xiDyadicLogLinearConstant
  have hu : 1 <= u := by
    dsimp [u]
    have hT : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have huSq : 1 <= u ^ 2 := by nlinarith
  have hThetaNonnegative : 0 <= Ctheta :=
    TS289.Goldbach.completedZetaThetaTailConstant_pos.le
  have hAnchorNonnegative : 0 <= Canchor := xiMacroscopicAnchorLogCost_nonnegative
  have hCountNonnegative : 0 <= Ccount :=
    TS290.Goldbach.xiDyadicLogLinearConstant_nonnegative
  have hThetaScale : Ctheta <= Ctheta * u ^ 2 := by
    nlinarith [mul_nonneg hThetaNonnegative (sub_nonneg.mpr huSq)]
  have hAnchorScale : Canchor <= Canchor * u ^ 2 := by
    nlinarith [mul_nonneg hAnchorNonnegative (sub_nonneg.mpr huSq)]
  have hLogBoundary :
      Real.log (xiMacroscopicNormalizedBoundaryMajorant T) <=
        263169 * u ^ 2 + Ctheta * u ^ 2 + Canchor * u ^ 2 +
          514 * Ccount * u ^ 2 := by
    rw [log_xiMacroscopicNormalizedBoundaryMajorant]
    have hXi := xiMacroscopicOuterXiMajorant_log_le T
    have hXiQuadratic := xiMacroscopicOuterXiLogTerm_le_quadratic T
    have hPoly := xiMacroscopicPolynomialLogCost_le_closed T
    have hAnchor := neg_log_anchorNorm_le_cost
    have hXiClosed :
        Real.log (xiMacroscopicOuterXiMajorant T) <=
          263169 * u ^ 2 + Ctheta * u ^ 2 := by
      calc
        Real.log (xiMacroscopicOuterXiMajorant T) <=
            (xiMacroscopicOuterRadius T + 3) *
                Real.log (xiMacroscopicOuterRadius T + 2) + Ctheta := by
          simpa [Ctheta] using hXi
        _ <= 263169 * u ^ 2 + Ctheta := by
          have hQuad :
              (xiMacroscopicOuterRadius T + 3) *
                  Real.log (xiMacroscopicOuterRadius T + 2) <=
                263169 * u ^ 2 := by
            simpa [u] using hXiQuadratic
          linarith
        _ <= 263169 * u ^ 2 + Ctheta * u ^ 2 := by linarith
    have hAnchorClosed :
        -Real.log xiMacroscopicAnchorNorm <= Canchor * u ^ 2 :=
      hAnchor.trans (by simpa [Canchor] using hAnchorScale)
    have hPolyClosed :
        (TS302.Goldbach.xiMacroscopicFactorMultiplicityCount T : Real) *
            Real.log (xiMacroscopicPolynomialRatioBase T) <=
          514 * Ccount * u ^ 2 := by
      simpa [Ccount, u] using hPoly
    linarith
  have hStrict :
      263169 * u ^ 2 + Ctheta * u ^ 2 + Canchor * u ^ 2 +
          514 * Ccount * u ^ 2 <
        (263171 + Ctheta + Canchor + 514 * Ccount) * u ^ 2 := by
    have huSqPos : 0 < u ^ 2 := lt_of_lt_of_le zero_lt_one huSq
    nlinarith
  apply hLogBoundary.trans_lt
  simpa [xiMacroscopicClosedRealPartEnvelope,
    xiMacroscopicClosedEnvelopeConstant, u, Ctheta, Canchor, Ccount] using hStrict

theorem anchoredXiMacroscopicLog_re_lt_closedEnvelope
    (T : Nat)
    (z : Complex)
    (hz : Membership.mem
      (Metric.closedBall TS301.Goldbach.xiMacroscopicAnchor
        (TS301.Goldbach.xiMacroscopicControlRadius T)) z) :
    (TS301.Goldbach.anchoredXiMacroscopicLog T z).re <
      xiMacroscopicClosedRealPartEnvelope T := by
  have hExpEq := congrArg norm
    (TS301.Goldbach.exp_anchoredXiMacroscopicLog_eq_normalized T z hz)
  have hExp :
      Real.exp ((TS301.Goldbach.anchoredXiMacroscopicLog T z).re) =
        norm (TS301.Goldbach.normalizedXiMacroscopicQuotient T z) := by
    simpa [Complex.norm_eq_abs, Complex.abs_exp] using hExpEq
  have hNorm := normalizedXiMacroscopicQuotient_norm_le_controlBall T z hz
  have hExpLe :
      Real.exp ((TS301.Goldbach.anchoredXiMacroscopicLog T z).re) <=
        xiMacroscopicNormalizedBoundaryMajorant T := by
    rw [hExp]
    exact hNorm
  have hReLe :
      (TS301.Goldbach.anchoredXiMacroscopicLog T z).re <=
        Real.log (xiMacroscopicNormalizedBoundaryMajorant T) := by
    exact (Real.le_log_iff_exp_le
      (xiMacroscopicNormalizedBoundaryMajorant_pos T)).mpr hExpLe
  exact hReLe.trans_lt (log_normalizedBoundaryMajorant_lt_closedEnvelope T)

/-! ## Closed Borel-Caratheodory and Cauchy bounds -/

theorem anchoredXiMacroscopicLog_norm_le_closed
    (T : Nat)
    (z : Complex)
    (hz : dist z TS301.Goldbach.xiMacroscopicAnchor <
      TS301.Goldbach.xiMacroscopicControlRadius T) :
    norm (TS301.Goldbach.anchoredXiMacroscopicLog T z) <=
      2 * xiMacroscopicClosedRealPartEnvelope T *
          dist z TS301.Goldbach.xiMacroscopicAnchor /
        (TS301.Goldbach.xiMacroscopicControlRadius T -
          dist z TS301.Goldbach.xiMacroscopicAnchor) := by
  let f : Complex -> Complex := fun w =>
    TS301.Goldbach.anchoredXiMacroscopicLog T
      (TS301.Goldbach.xiMacroscopicAnchor + w)
  have hfDiff : DifferentiableOn Complex f
      (Metric.ball 0 (TS301.Goldbach.xiMacroscopicControlRadius T)) := by
    intro w hw
    have hwDist : dist
        (TS301.Goldbach.xiMacroscopicAnchor + w)
        TS301.Goldbach.xiMacroscopicAnchor <
          TS301.Goldbach.xiMacroscopicControlRadius T := by
      simpa [dist_eq] using hw
    have hwClosed : Membership.mem
        (Metric.closedBall TS301.Goldbach.xiMacroscopicAnchor
          (TS301.Goldbach.xiMacroscopicControlRadius T))
        (TS301.Goldbach.xiMacroscopicAnchor + w) :=
      Metric.mem_closedBall.mpr hwDist.le
    have hOuter :=
      (TS301.Goldbach.anchoredXiMacroscopicLog_analyticOnNhd_controlBall
        T _ hwClosed).differentiableAt
    have hInner : DifferentiableAt Complex
        (fun u : Complex => TS301.Goldbach.xiMacroscopicAnchor + u) w :=
      differentiableAt_const TS301.Goldbach.xiMacroscopicAnchor
        |>.add differentiableAt_id
    exact (hOuter.comp w hInner).differentiableWithinAt
  have hfZero : f 0 = 0 := by
    simp [f, TS301.Goldbach.anchoredXiMacroscopicLog_anchor]
  have hfRe : forall w,
      Membership.mem
        (Metric.ball 0 (TS301.Goldbach.xiMacroscopicControlRadius T)) w ->
      (f w).re < xiMacroscopicClosedRealPartEnvelope T := by
    intro w hw
    apply anchoredXiMacroscopicLog_re_lt_closedEnvelope T
    rw [Metric.mem_closedBall]
    simpa [dist_eq] using (Metric.mem_ball.mp hw).le
  have hw : Membership.mem
      (Metric.ball 0 (TS301.Goldbach.xiMacroscopicControlRadius T))
      (z - TS301.Goldbach.xiMacroscopicAnchor) := by
    simpa [Metric.mem_ball, dist_eq] using hz
  have hMaps : MapsTo f
      (Metric.ball 0 (TS301.Goldbach.xiMacroscopicControlRadius T))
      {u : Complex | u.re < xiMacroscopicClosedRealPartEnvelope T} := hfRe
  have hBC := TS300.Goldbach.centered_borelCaratheodory_zero
    (xiMacroscopicClosedRealPartEnvelope_pos T)
    hfDiff hMaps (TS301.Goldbach.xiMacroscopicControlRadius_pos T) hw hfZero
  simpa [f, dist_eq, sub_add_cancel] using hBC

theorem anchoredXiMacroscopicLog_norm_le_two_closedEnvelope
    (T : Nat)
    (z : Complex)
    (hz : dist z TS301.Goldbach.xiMacroscopicAnchor <=
      TS301.Goldbach.xiMacroscopicControlRadius T / 2) :
    norm (TS301.Goldbach.anchoredXiMacroscopicLog T z) <=
      2 * xiMacroscopicClosedRealPartEnvelope T := by
  have hRPos := TS301.Goldbach.xiMacroscopicControlRadius_pos T
  have hzLt : dist z TS301.Goldbach.xiMacroscopicAnchor <
      TS301.Goldbach.xiMacroscopicControlRadius T := by linarith
  have hBase := anchoredXiMacroscopicLog_norm_le_closed T z hzLt
  have hDistNonnegative : 0 <= dist z TS301.Goldbach.xiMacroscopicAnchor :=
    dist_nonneg
  have hMNonnegative : 0 <= xiMacroscopicClosedRealPartEnvelope T :=
    (xiMacroscopicClosedRealPartEnvelope_pos T).le
  have hDenPos : 0 < TS301.Goldbach.xiMacroscopicControlRadius T -
      dist z TS301.Goldbach.xiMacroscopicAnchor := sub_pos.mpr hzLt
  apply hBase.trans
  have hNumerator :
      2 * xiMacroscopicClosedRealPartEnvelope T *
          dist z TS301.Goldbach.xiMacroscopicAnchor <=
        (2 * xiMacroscopicClosedRealPartEnvelope T) *
          (TS301.Goldbach.xiMacroscopicControlRadius T -
            dist z TS301.Goldbach.xiMacroscopicAnchor) := by
    nlinarith
  calc
    2 * xiMacroscopicClosedRealPartEnvelope T *
          dist z TS301.Goldbach.xiMacroscopicAnchor /
        (TS301.Goldbach.xiMacroscopicControlRadius T -
          dist z TS301.Goldbach.xiMacroscopicAnchor) <=
      ((2 * xiMacroscopicClosedRealPartEnvelope T) *
          (TS301.Goldbach.xiMacroscopicControlRadius T -
            dist z TS301.Goldbach.xiMacroscopicAnchor)) /
        (TS301.Goldbach.xiMacroscopicControlRadius T -
          dist z TS301.Goldbach.xiMacroscopicAnchor) :=
      div_le_div_of_nonneg_right hNumerator hDenPos.le
    _ = 2 * xiMacroscopicClosedRealPartEnvelope T := by field_simp

noncomputable def finiteGridTopClosedMacroscopicLocalLogData
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (TS301.Goldbach.normalizedXiMacroscopicQuotient T)
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) where
  radius := TS301.Goldbach.xiMacroscopicLocalRadius T
  radius_pos := TS301.Goldbach.xiMacroscopicLocalRadius_pos T
  logarithm := TS301.Goldbach.anchoredXiMacroscopicLog T
  logarithm_diffContOnCl :=
    (TS301.Goldbach.finiteGridTopMacroscopicLocalLogData T sigma hSigma).logarithm_diffContOnCl
  exp_logarithm_eq :=
    (TS301.Goldbach.finiteGridTopMacroscopicLocalLogData T sigma hSigma).exp_logarithm_eq
  sphereBound := 2 * xiMacroscopicClosedRealPartEnvelope T
  logarithm_norm_le := by
    intro z hz
    apply anchoredXiMacroscopicLog_norm_le_two_closedEnvelope
    exact TS301.Goldbach.localSphere_subset_controlBall T
      (TS301.Goldbach.finiteGridHorizontalPoint_dist_anchor_le T sigma hSigma) hz

noncomputable def finiteGridBottomClosedMacroscopicLocalLogData
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    TS295.Goldbach.LocalHolomorphicLogCauchyData
      (TS301.Goldbach.normalizedXiMacroscopicQuotient T)
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) where
  radius := TS301.Goldbach.xiMacroscopicLocalRadius T
  radius_pos := TS301.Goldbach.xiMacroscopicLocalRadius_pos T
  logarithm := TS301.Goldbach.anchoredXiMacroscopicLog T
  logarithm_diffContOnCl :=
    (TS301.Goldbach.finiteGridBottomMacroscopicLocalLogData T sigma hSigma).logarithm_diffContOnCl
  exp_logarithm_eq :=
    (TS301.Goldbach.finiteGridBottomMacroscopicLocalLogData T sigma hSigma).exp_logarithm_eq
  sphereBound := 2 * xiMacroscopicClosedRealPartEnvelope T
  logarithm_norm_le := by
    intro z hz
    apply anchoredXiMacroscopicLog_norm_le_two_closedEnvelope
    exact TS301.Goldbach.localSphere_subset_controlBall T
      (TS301.Goldbach.finiteGridBottomHorizontalPoint_dist_anchor_le T sigma hSigma) hz

theorem xiMacroscopicQuotient_logDerivative_norm_le_closed_top
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      (2 * xiMacroscopicClosedRealPartEnvelope T) /
        TS301.Goldbach.xiMacroscopicLocalRadius T := by
  let c := TS300.Goldbach.finiteGridTopHorizontalPoint T sigma
  have hcControl : Membership.mem
      (Metric.closedBall TS301.Goldbach.xiMacroscopicAnchor
        (TS301.Goldbach.xiMacroscopicControlRadius T)) c := by
    rw [Metric.mem_closedBall]
    have hBound : (T : Real) + 5 <=
        TS301.Goldbach.xiMacroscopicControlRadius T := by
      change (T : Real) + 5 <= 16 * ((T : Real) + 4)
      nlinarith [(Nat.cast_nonneg T : (0 : Real) <= (T : Real))]
    exact (TS301.Goldbach.finiteGridHorizontalPoint_dist_anchor_le T sigma hSigma).trans hBound
  rw [<- TS301.Goldbach.normalizedXiMacroscopicQuotient_logDeriv_eq T c hcControl]
  exact (finiteGridTopClosedMacroscopicLocalLogData T sigma hSigma).logDerivative_norm_le

theorem xiMacroscopicQuotient_logDerivative_norm_le_closed_bottom
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      (2 * xiMacroscopicClosedRealPartEnvelope T) /
        TS301.Goldbach.xiMacroscopicLocalRadius T := by
  let c := TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma
  have hcControl : Membership.mem
      (Metric.closedBall TS301.Goldbach.xiMacroscopicAnchor
        (TS301.Goldbach.xiMacroscopicControlRadius T)) c := by
    rw [Metric.mem_closedBall]
    have hBound : (T : Real) + 5 <=
        TS301.Goldbach.xiMacroscopicControlRadius T := by
      change (T : Real) + 5 <= 16 * ((T : Real) + 4)
      nlinarith [(Nat.cast_nonneg T : (0 : Real) <= (T : Real))]
    exact (TS301.Goldbach.finiteGridBottomHorizontalPoint_dist_anchor_le T sigma hSigma).trans hBound
  rw [<- TS301.Goldbach.normalizedXiMacroscopicQuotient_logDeriv_eq T c hcControl]
  exact (finiteGridBottomClosedMacroscopicLocalLogData T sigma hSigma).logDerivative_norm_le

/-! ## Closed horizontal decay of the macroscopic quotient -/

noncomputable def xiMacroscopicClosedLogDerivativeEnvelope (T : Nat) : Real :=
  xiMacroscopicClosedEnvelopeConstant * ((T : Real) + 4)

theorem xiMacroscopicClosedLogDerivativeEnvelope_nonnegative (T : Nat) :
    0 <= xiMacroscopicClosedLogDerivativeEnvelope T := by
  unfold xiMacroscopicClosedLogDerivativeEnvelope
  exact mul_nonneg xiMacroscopicClosedEnvelopeConstant_pos.le (by positivity)

theorem xiMacroscopicQuotient_logDerivative_norm_le_linear_top
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      xiMacroscopicClosedLogDerivativeEnvelope T := by
  apply (xiMacroscopicQuotient_logDerivative_norm_le_closed_top T sigma hSigma).trans_eq
  unfold xiMacroscopicClosedRealPartEnvelope
    xiMacroscopicClosedLogDerivativeEnvelope
    TS301.Goldbach.xiMacroscopicLocalRadius
  have hU : Not (((T : Real) + 4) = 0) := ne_of_gt (by positivity)
  field_simp
  ring

theorem xiMacroscopicQuotient_logDerivative_norm_le_linear_bottom
    (T : Nat)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      xiMacroscopicClosedLogDerivativeEnvelope T := by
  apply (xiMacroscopicQuotient_logDerivative_norm_le_closed_bottom T sigma hSigma).trans_eq
  unfold xiMacroscopicClosedRealPartEnvelope
    xiMacroscopicClosedLogDerivativeEnvelope
    TS301.Goldbach.xiMacroscopicLocalRadius
  have hU : Not (((T : Real) + 4) = 0) := ne_of_gt (by positivity)
  field_simp
  ring

noncomputable def xiMacroscopicClosedLogDerivativeDecayEnvelope (T : Nat) : Real :=
  5 * xiMacroscopicClosedEnvelopeConstant / (T : Real)

theorem xiMacroscopicClosedLogDerivativeDecayEnvelope_nonnegative (T : Nat) :
    0 <= xiMacroscopicClosedLogDerivativeDecayEnvelope T := by
  unfold xiMacroscopicClosedLogDerivativeDecayEnvelope
  exact div_nonneg
    (mul_nonneg (by norm_num) xiMacroscopicClosedEnvelopeConstant_pos.le)
    (Nat.cast_nonneg T)

theorem xiMacroscopicClosedLogDerivativeEnvelope_div_sq_le_decay
    (T : Nat)
    (hT : 1 <= T) :
    xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2 <=
      xiMacroscopicClosedLogDerivativeDecayEnvelope T := by
  have hTR : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
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
  unfold xiMacroscopicClosedLogDerivativeEnvelope
    xiMacroscopicClosedLogDerivativeDecayEnvelope
  have hConstant := xiMacroscopicClosedEnvelopeConstant_pos.le
  calc
    xiMacroscopicClosedEnvelopeConstant * ((T : Real) + 4) /
        (T : Real) ^ 2 =
      xiMacroscopicClosedEnvelopeConstant *
        (((T : Real) + 4) / (T : Real) ^ 2) := by ring
    _ <= xiMacroscopicClosedEnvelopeConstant * (5 / (T : Real)) :=
      mul_le_mul_of_nonneg_left hRatio hConstant
    _ = 5 * xiMacroscopicClosedEnvelopeConstant / (T : Real) := by ring

theorem xiMacroscopicClosedLogDerivativeDecayEnvelope_tendsto_zero :
    Tendsto xiMacroscopicClosedLogDerivativeDecayEnvelope atTop (nhds 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul
    (5 * xiMacroscopicClosedEnvelopeConstant)
  convert h using 1
  case h.e'_3 =>
    funext T
    unfold xiMacroscopicClosedLogDerivativeDecayEnvelope
    ring
  case h.e'_5 => ring

theorem xiMacroscopicClosedLogDerivativeEnvelope_div_sq_tendsto_zero :
    Tendsto
      (fun T : Nat =>
        xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    xiMacroscopicClosedLogDerivativeDecayEnvelope_tendsto_zero
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg
      (xiMacroscopicClosedLogDerivativeEnvelope_nonnegative T)
      (sq_nonneg (T : Real))
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact xiMacroscopicClosedLogDerivativeEnvelope_div_sq_le_decay T hT

noncomputable def xiMacroscopicQuotientTopPointwise
    (x T : Nat)
    (sigma : Real) : Real :=
  norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
    norm ((x : Complex) ^ (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
      norm (TS257.Goldbach.triangleSplineMellinKernel
        (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma))

noncomputable def xiMacroscopicQuotientBottomPointwise
    (x T : Nat)
    (sigma : Real) : Real :=
  norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
    norm ((x : Complex) ^ (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
      norm (TS257.Goldbach.triangleSplineMellinKernel
        (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma))

noncomputable def xiMacroscopicQuotientHorizontalComponent
    (x T : Nat) : Real :=
  (7 / 2 : Real) * TS298.Goldbach.rightLineScale x *
    (xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2)

theorem xiMacroscopicQuotientTopPointwise_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    xiMacroscopicQuotientTopPointwise x T sigma <=
      TS298.Goldbach.rightLineScale x *
        (xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hInv : 1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
      1 / (T : Real) ^ 2 := by
    have hSq : (T : Real) ^ 2 <=
        (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
    exact one_div_le_one_div_of_le (sq_pos_of_pos hTPos) hSq
  have hEnvelope0 := xiMacroscopicClosedLogDerivativeEnvelope_nonnegative T
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold xiMacroscopicQuotientTopPointwise
  calc
    norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
        norm ((x : Complex) ^
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
        norm (TS257.Goldbach.triangleSplineMellinKernel
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      xiMacroscopicClosedLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst := mul_le_mul
        (xiMacroscopicQuotient_logDerivative_norm_le_linear_top T sigma hSigma)
        (TS300.Goldbach.nat_cpow_finiteGridTop_norm_le_rightLineScale
          x T hT sigma hSigma.2)
        (norm_nonneg _) hEnvelope0
      exact mul_le_mul hFirst
        (TS300.Goldbach.triangleSplineMellinKernel_finiteGridTop_norm_le
          T hT sigma)
        (norm_nonneg _) (mul_nonneg hEnvelope0 hScale0)
    _ <= xiMacroscopicClosedLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hInv (mul_nonneg hEnvelope0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
        (xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2) := by ring

theorem xiMacroscopicQuotientBottomPointwise_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    xiMacroscopicQuotientBottomPointwise x T sigma <=
      TS298.Goldbach.rightLineScale x *
        (xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hInv : 1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
      1 / (T : Real) ^ 2 := by
    have hSq : (T : Real) ^ 2 <=
        (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
    exact one_div_le_one_div_of_le (sq_pos_of_pos hTPos) hSq
  have hEnvelope0 := xiMacroscopicClosedLogDerivativeEnvelope_nonnegative T
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold xiMacroscopicQuotientBottomPointwise
  calc
    norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T)
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        TS301.Goldbach.xiMacroscopicQuotient T
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
        norm ((x : Complex) ^
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
        norm (TS257.Goldbach.triangleSplineMellinKernel
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      xiMacroscopicClosedLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst := mul_le_mul
        (xiMacroscopicQuotient_logDerivative_norm_le_linear_bottom T sigma hSigma)
        (TS300.Goldbach.nat_cpow_finiteGridBottom_norm_le_rightLineScale
          x T hT sigma hSigma.2)
        (norm_nonneg _) hEnvelope0
      exact mul_le_mul hFirst
        (TS300.Goldbach.triangleSplineMellinKernel_finiteGridBottom_norm_le
          T hT sigma)
        (norm_nonneg _) (mul_nonneg hEnvelope0 hScale0)
    _ <= xiMacroscopicClosedLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hInv (mul_nonneg hEnvelope0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
        (xiMacroscopicClosedLogDerivativeEnvelope T / (T : Real) ^ 2) := by ring

theorem xiMacroscopicQuotientTop_integratedWidth_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    (7 / 2 : Real) * xiMacroscopicQuotientTopPointwise x T sigma <=
      xiMacroscopicQuotientHorizontalComponent x T := by
  unfold xiMacroscopicQuotientHorizontalComponent
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (xiMacroscopicQuotientTopPointwise_le x T hT sigma hSigma)
    (by norm_num : (0 : Real) <= 7 / 2)

theorem xiMacroscopicQuotientBottom_integratedWidth_le
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    (7 / 2 : Real) * xiMacroscopicQuotientBottomPointwise x T sigma <=
      xiMacroscopicQuotientHorizontalComponent x T := by
  unfold xiMacroscopicQuotientHorizontalComponent
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left
    (xiMacroscopicQuotientBottomPointwise_le x T hT sigma hSigma)
    (by norm_num : (0 : Real) <= 7 / 2)

theorem xiMacroscopicQuotientHorizontalComponent_tendsto_zero
    (x : Nat) :
    Tendsto (xiMacroscopicQuotientHorizontalComponent x) atTop (nhds 0) := by
  unfold xiMacroscopicQuotientHorizontalComponent
  simpa using xiMacroscopicClosedLogDerivativeEnvelope_div_sq_tendsto_zero.const_mul
    ((7 / 2 : Real) * TS298.Goldbach.rightLineScale x)

/-! ## Audit ledger -/

structure ClosedAnchoredMacroscopicEnvelopeLedger where
  quantitative_outer_circle_defined : Prop
  factor_roots_separated_from_outer_circle : Prop
  anchor_polynomial_upper_bound_proved : Prop
  outer_polynomial_lower_bound_proved : Prop
  normalized_quotient_boundary_bound_proved : Prop
  maximum_modulus_transport_proved : Prop
  closed_quadratic_real_part_envelope_proved : Prop
  centered_borel_caratheodory_reused : Prop
  closed_linear_log_derivative_bound_proved : Prop
  fixed_scale_quotient_horizontal_decay_proved : Prop
  moving_center_minimum_modulus_not_used : Prop
  local_zero_density_not_used : Prop
  riemann_hypothesis_not_used : Prop
  infinite_hadamard_product_not_used : Prop
  completion_correction_rate_not_proved : Prop
  complete_horizontal_decay_not_proved : Prop
  fixed_left_boundary_not_proved : Prop
  exceptional_residues_not_completed : Prop
  perron_inversion_not_proved : Prop
  meromorphic_residue_theorem_not_proved : Prop
  infinite_explicit_formula_not_proved : Prop
  gallagher_not_proved : Prop
  otsa_not_proved : Prop
  goldbach_not_claimed : Prop

def closedAnchoredMacroscopicEnvelopeLedger :
    ClosedAnchoredMacroscopicEnvelopeLedger where
  quantitative_outer_circle_defined := True
  factor_roots_separated_from_outer_circle := True
  anchor_polynomial_upper_bound_proved := True
  outer_polynomial_lower_bound_proved := True
  normalized_quotient_boundary_bound_proved := True
  maximum_modulus_transport_proved := True
  closed_quadratic_real_part_envelope_proved := True
  centered_borel_caratheodory_reused := True
  closed_linear_log_derivative_bound_proved := True
  fixed_scale_quotient_horizontal_decay_proved := True
  moving_center_minimum_modulus_not_used := True
  local_zero_density_not_used := True
  riemann_hypothesis_not_used := True
  infinite_hadamard_product_not_used := True
  completion_correction_rate_not_proved := True
  complete_horizontal_decay_not_proved := True
  fixed_left_boundary_not_proved := True
  exceptional_residues_not_completed := True
  perron_inversion_not_proved := True
  meromorphic_residue_theorem_not_proved := True
  infinite_explicit_formula_not_proved := True
  gallagher_not_proved := True
  otsa_not_proved := True
  goldbach_not_claimed := True

end Goldbach
end TS303
