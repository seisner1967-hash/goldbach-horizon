import Mathlib.Tactic
import TS.Goldbach.Strong.TS274.MinimalJensenInequalityBackport

/-!
# TS275 - Finite Jensen Polynomial Factorization Reduction

TS274 proved the finite counting core of Jensen's inequality.  This sprint
separates the zeros counted in an inner disk from the complete finite family
factorized below the averaging circle.  It also introduces an analytic buffer

`0 < r < R < S`

so every circle integral at radius `R` lies strictly inside the analytic disk
of radius `S`.

The finite zero polynomial is a concrete `Finset.prod` with natural
multiplicities.  Its analyticity, zero set away from the selected roots,
center value, logarithmic center identity, weighted mass identity, and the
inner-to-factor mass comparison are proved.  Buffered data then records a
factorization `f = P * g` with a nonvanishing analytic quotient on the disk of
radius `S`; nonvanishing of `f` on the averaging sphere and collar follows.

An explicit normalized angular average reduces the remaining Jensen boundary
estimate to two named inputs: the average of each linear factor and the
logarithmic mean value of the nonvanishing quotient.  Neither input is proved
here.  No concrete factorization construction, Riemann xi function, effective
zero count, explicit formula, Gallagher estimate, OTSA bridge, or Goldbach
statement is claimed.
-/

namespace TS275
namespace Goldbach

/-- Three-radius geometry for finite Jensen factorization. -/
structure JensenDiskConfiguration where
  center : Complex
  innerRadius : Real
  averagingRadius : Real
  analyticRadius : Real

  innerRadius_positive :
    0 < innerRadius

  innerRadius_lt_averagingRadius :
    innerRadius < averagingRadius

  averagingRadius_lt_analyticRadius :
    averagingRadius < analyticRadius

namespace JensenDiskConfiguration

theorem averagingRadius_positive
    (C : JensenDiskConfiguration) :
    0 < C.averagingRadius :=
  C.innerRadius_positive.trans C.innerRadius_lt_averagingRadius

theorem analyticRadius_positive
    (C : JensenDiskConfiguration) :
    0 < C.analyticRadius :=
  C.averagingRadius_positive.trans C.averagingRadius_lt_analyticRadius

theorem innerRadius_lt_analyticRadius
    (C : JensenDiskConfiguration) :
    C.innerRadius < C.analyticRadius :=
  C.innerRadius_lt_averagingRadius.trans C.averagingRadius_lt_analyticRadius

/-- Complex closed-ball membership written with `Complex.abs`. -/
theorem mem_closedBall_iff_abs_sub
    (C : JensenDiskConfiguration)
    (z : Complex)
    (radius : Real) :
    Membership.mem (Metric.closedBall C.center radius) z <->
      Complex.abs (z - C.center) <= radius := by
  rw [Metric.mem_closedBall, dist_eq_norm, Complex.norm_eq_abs]

theorem averagingClosedBall_subset_analyticClosedBall
    (C : JensenDiskConfiguration) :
    Metric.closedBall C.center C.averagingRadius <=
      Metric.closedBall C.center C.analyticRadius := by
  intro z hz
  rw [C.mem_closedBall_iff_abs_sub] at hz
  rw [C.mem_closedBall_iff_abs_sub]
  exact hz.trans C.averagingRadius_lt_analyticRadius.le

theorem innerClosedBall_subset_analyticClosedBall
    (C : JensenDiskConfiguration) :
    Metric.closedBall C.center C.innerRadius <=
      Metric.closedBall C.center C.analyticRadius := by
  intro z hz
  rw [C.mem_closedBall_iff_abs_sub] at hz
  rw [C.mem_closedBall_iff_abs_sub]
  exact hz.trans C.innerRadius_lt_analyticRadius.le

theorem averagingSphere_mem_analyticClosedBall
    (C : JensenDiskConfiguration)
    (z : Complex)
    (hz : Complex.abs (z - C.center) = C.averagingRadius) :
    Membership.mem (Metric.closedBall C.center C.analyticRadius) z := by
  rw [C.mem_closedBall_iff_abs_sub]
  exact hz.le.trans C.averagingRadius_lt_analyticRadius.le

end JensenDiskConfiguration

/-- Zeros counted by TS274 in the inner disk. -/
structure JensenInnerZeroData where
  config : JensenDiskConfiguration
  innerZeros : Finset Complex
  innerMultiplicity : Complex -> Nat

  inner_zero_ne_center :
    forall rho : Complex,
      Membership.mem innerZeros rho ->
        Not (rho = config.center)

  inner_zero_mem_disk :
    forall rho : Complex,
      Membership.mem innerZeros rho ->
        Complex.abs (rho - config.center) <= config.innerRadius

namespace JensenInnerZeroData

/-- Exact bridge back to the TS274 inner counting data. -/
def toFiniteJensenDiskData
    (D : JensenInnerZeroData) :
    TS274.Goldbach.FiniteJensenDiskData where
  center := D.config.center
  innerRadius := D.config.innerRadius
  outerRadius := D.config.averagingRadius
  zeros := D.innerZeros
  multiplicity := D.innerMultiplicity
  innerRadius_positive := D.config.innerRadius_positive
  innerRadius_lt_outerRadius := D.config.innerRadius_lt_averagingRadius
  zero_ne_center := D.inner_zero_ne_center
  zero_mem_innerDisk := D.inner_zero_mem_disk

end JensenInnerZeroData

/-- Complete finite zero family factorized below the averaging circle. -/
structure JensenFactorZeroData extends JensenInnerZeroData where
  factorZeros : Finset Complex
  factorMultiplicity : Complex -> Nat

  factor_zero_ne_center :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        Not (rho = config.center)

  factor_zero_mem_open_disk :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        Complex.abs (rho - config.center) < config.averagingRadius

  innerZeros_subset_factorZeros :
    innerZeros <= factorZeros

  multiplicity_agrees :
    forall rho : Complex,
      Membership.mem innerZeros rho ->
        innerMultiplicity rho = factorMultiplicity rho

  factorMultiplicity_positive :
    forall rho : Complex,
      Membership.mem factorZeros rho ->
        0 < factorMultiplicity rho

/-- Concrete finite zero polynomial with natural multiplicities. -/
noncomputable def finiteJensenZeroPolynomial
    (D : JensenFactorZeroData)
    (z : Complex) :
    Complex :=
  Finset.prod D.factorZeros
    (fun rho => (z - rho) ^ D.factorMultiplicity rho)

/-- A finite product of powered linear factors is analytic everywhere. -/
theorem finiteJensenZeroPolynomial_analyticAt
    (D : JensenFactorZeroData)
    (z : Complex) :
    AnalyticAt Complex (finiteJensenZeroPolynomial D) z := by
  classical
  unfold finiteJensenZeroPolynomial
  induction D.factorZeros using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const :
        AnalyticAt Complex (fun _ : Complex => (1 : Complex)) z)
  | @insert rho zeros hRho ih =>
      have hFactor :
          AnalyticAt Complex
            (fun w : Complex => (w - rho) ^ D.factorMultiplicity rho) z :=
        (analyticAt_id.sub analyticAt_const).pow _
      simpa [Finset.prod_insert hRho] using hFactor.mul ih

theorem finiteJensenZeroPolynomial_analyticOnNhd
    (D : JensenFactorZeroData)
    (s : Set Complex) :
    AnalyticOnNhd Complex (finiteJensenZeroPolynomial D) s := by
  intro z _
  exact finiteJensenZeroPolynomial_analyticAt D z

/-- The zero polynomial is nonzero away from every selected root. -/
theorem finiteJensenZeroPolynomial_ne_zero_of_avoids_roots
    (D : JensenFactorZeroData)
    (z : Complex)
    (hAvoid :
      forall rho : Complex,
        Membership.mem D.factorZeros rho ->
          Not (z = rho)) :
    Not (finiteJensenZeroPolynomial D z = 0) := by
  classical
  unfold finiteJensenZeroPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro rho hRho
  exact pow_ne_zero _ (sub_ne_zero.mpr (hAvoid rho hRho))

/-- Positive multiplicities make the roots exactly the factor `Finset`. -/
theorem finiteJensenZeroPolynomial_eq_zero_iff
    (D : JensenFactorZeroData)
    (z : Complex) :
    finiteJensenZeroPolynomial D z = 0 <->
      Membership.mem D.factorZeros z := by
  constructor
  case mp =>
    intro hZero
    by_contra hMem
    exact finiteJensenZeroPolynomial_ne_zero_of_avoids_roots D z
      (fun rho hRho hEq => by
        apply hMem
        rw [hEq]
        exact hRho) hZero
  case mpr =>
    intro hMem
    unfold finiteJensenZeroPolynomial
    rw [Finset.prod_eq_zero_iff]
    refine Exists.intro z (And.intro hMem ?_)
    rw [sub_self]
    exact zero_pow (Nat.ne_of_gt (D.factorMultiplicity_positive z hMem))

theorem finiteJensenZeroPolynomial_at_center_ne_zero
    (D : JensenFactorZeroData) :
    Not (finiteJensenZeroPolynomial D D.config.center = 0) :=
  finiteJensenZeroPolynomial_ne_zero_of_avoids_roots D D.config.center
    (fun rho hRho hEq => D.factor_zero_ne_center rho hRho hEq.symm)

/-- Exact absolute value of the finite zero polynomial. -/
theorem finiteJensenZeroPolynomial_abs
    (D : JensenFactorZeroData)
    (z : Complex) :
    Complex.abs (finiteJensenZeroPolynomial D z) =
      Finset.prod D.factorZeros
        (fun rho => Complex.abs (z - rho) ^ D.factorMultiplicity rho) := by
  unfold finiteJensenZeroPolynomial
  rw [Complex.abs.map_prod]
  apply Finset.prod_congr rfl
  intro rho _
  exact Complex.abs.map_pow (z - rho) (D.factorMultiplicity rho)

theorem finiteJensenZeroPolynomial_abs_at_center_positive
    (D : JensenFactorZeroData) :
    0 < Complex.abs (finiteJensenZeroPolynomial D D.config.center) := by
  rw [<- Complex.norm_eq_abs, norm_pos_iff]
  exact finiteJensenZeroPolynomial_at_center_ne_zero D

/-- Logarithm of the center value as a multiplicity-weighted finite sum. -/
theorem finiteJensenZeroPolynomial_log_abs_at_center
    (D : JensenFactorZeroData) :
    Real.log (Complex.abs (finiteJensenZeroPolynomial D D.config.center)) =
      Finset.sum D.factorZeros
        (fun rho =>
          (D.factorMultiplicity rho : Real) *
            Real.log (Complex.abs (D.config.center - rho))) := by
  rw [finiteJensenZeroPolynomial_abs]
  rw [Real.log_prod]
  case hf =>
    intro rho hRho
    exact pow_ne_zero _
      (ne_of_gt (by
        rw [<- Complex.norm_eq_abs, norm_pos_iff]
        exact sub_ne_zero.mpr
          (fun hEq => D.factor_zero_ne_center rho hRho hEq.symm)))
  apply Finset.sum_congr rfl
  intro rho _
  exact Real.log_pow _ _

/-- Pointwise logarithmic product identity away from all factor roots. -/
theorem finiteJensenZeroPolynomial_log_abs_of_avoids_roots
    (D : JensenFactorZeroData)
    (z : Complex)
    (hAvoid :
      forall rho : Complex,
        Membership.mem D.factorZeros rho ->
          Not (z = rho)) :
    Real.log (Complex.abs (finiteJensenZeroPolynomial D z)) =
      Finset.sum D.factorZeros
        (fun rho =>
          (D.factorMultiplicity rho : Real) *
            Real.log (Complex.abs (z - rho))) := by
  rw [finiteJensenZeroPolynomial_abs]
  rw [Real.log_prod]
  case hf =>
    intro rho hRho
    exact pow_ne_zero _
      (ne_of_gt (by
        rw [<- Complex.norm_eq_abs, norm_pos_iff]
        exact sub_ne_zero.mpr (hAvoid rho hRho)))
  apply Finset.sum_congr rfl
  intro rho _
  exact Real.log_pow _ _

/-- Natural multiplicity count over all factorized zeros. -/
def finiteFactorMultiplicityCount
    (D : JensenFactorZeroData) :
    Nat :=
  Finset.sum D.factorZeros D.factorMultiplicity

/-- Real multiplicity mass over all factorized zeros. -/
noncomputable def finiteFactorMultiplicityMass
    (D : JensenFactorZeroData) :
    Real :=
  Finset.sum D.factorZeros
    (fun rho => (D.factorMultiplicity rho : Real))

theorem finiteFactorMultiplicityMass_eq_count
    (D : JensenFactorZeroData) :
    finiteFactorMultiplicityMass D =
      (finiteFactorMultiplicityCount D : Real) := by
  simp [finiteFactorMultiplicityMass, finiteFactorMultiplicityCount]

/-- Jensen weight at the averaging radius for a factorized zero. -/
noncomputable def finiteFactorJensenWeight
    (D : JensenFactorZeroData)
    (rho : Complex) :
    Real :=
  Real.log
    (D.config.averagingRadius /
      Complex.abs (rho - D.config.center))

/-- Complete weighted mass over all factorized zeros. -/
noncomputable def finiteFactorJensenWeightedMass
    (D : JensenFactorZeroData) :
    Real :=
  Finset.sum D.factorZeros
    (fun rho =>
      (D.factorMultiplicity rho : Real) *
        finiteFactorJensenWeight D rho)

theorem factor_zero_distance_positive
    (D : JensenFactorZeroData)
    (rho : Complex)
    (hRho : Membership.mem D.factorZeros rho) :
    0 < Complex.abs (rho - D.config.center) := by
  rw [<- Complex.norm_eq_abs, norm_pos_iff]
  exact sub_ne_zero.mpr (D.factor_zero_ne_center rho hRho)

theorem finiteFactorJensenWeight_positive
    (D : JensenFactorZeroData)
    (rho : Complex)
    (hRho : Membership.mem D.factorZeros rho) :
    0 < finiteFactorJensenWeight D rho := by
  unfold finiteFactorJensenWeight
  apply Real.log_pos
  have hDistance := factor_zero_distance_positive D rho hRho
  calc
    1 = Complex.abs (rho - D.config.center) /
        Complex.abs (rho - D.config.center) := by
      rw [div_self hDistance.ne']
    _ < D.config.averagingRadius /
        Complex.abs (rho - D.config.center) :=
      (div_lt_div_iff_of_pos_right hDistance).mpr
        (D.factor_zero_mem_open_disk rho hRho)

theorem finiteFactorJensenWeightedMass_nonnegative
    (D : JensenFactorZeroData) :
    0 <= finiteFactorJensenWeightedMass D := by
  unfold finiteFactorJensenWeightedMass
  apply Finset.sum_nonneg
  intro rho hRho
  exact mul_nonneg (Nat.cast_nonneg _) (finiteFactorJensenWeight_positive D rho hRho).le

/-- The TS274 inner mass is dominated by the complete factor mass. -/
theorem innerJensenWeightedMass_le_factorJensenWeightedMass
    (D : JensenFactorZeroData) :
    TS274.Goldbach.finiteJensenWeightedMass
        D.toJensenInnerZeroData.toFiniteJensenDiskData <=
      finiteFactorJensenWeightedMass D := by
  let innerData := D.toJensenInnerZeroData.toFiniteJensenDiskData
  have hRewrite :
      TS274.Goldbach.finiteJensenWeightedMass innerData =
        Finset.sum D.innerZeros
          (fun rho =>
            (D.factorMultiplicity rho : Real) *
              finiteFactorJensenWeight D rho) := by
    unfold TS274.Goldbach.finiteJensenWeightedMass
    apply Finset.sum_congr rfl
    intro rho hRho
    change Membership.mem D.innerZeros rho at hRho
    change
      (D.innerMultiplicity rho : Real) *
          Real.log
            (D.config.averagingRadius /
              Complex.abs (rho - D.config.center)) =
        (D.factorMultiplicity rho : Real) *
          finiteFactorJensenWeight D rho
    rw [D.multiplicity_agrees rho hRho]
    rfl
  rw [hRewrite]
  unfold finiteFactorJensenWeightedMass
  apply Finset.sum_le_sum_of_subset_of_nonneg D.innerZeros_subset_factorZeros
  intro rho hFactor _
  exact mul_nonneg (Nat.cast_nonneg _)
    (finiteFactorJensenWeight_positive D rho hFactor).le

/-- Exact algebraic identity for the complete weighted factor mass. -/
theorem finiteFactorJensenWeightedMass_eq
    (D : JensenFactorZeroData) :
    finiteFactorJensenWeightedMass D =
      finiteFactorMultiplicityMass D * Real.log D.config.averagingRadius -
        Real.log
          (Complex.abs
            (finiteJensenZeroPolynomial D D.config.center)) := by
  rw [finiteJensenZeroPolynomial_log_abs_at_center]
  unfold finiteFactorJensenWeightedMass finiteFactorMultiplicityMass
  calc
    Finset.sum D.factorZeros
        (fun rho =>
          (D.factorMultiplicity rho : Real) *
            finiteFactorJensenWeight D rho) =
      Finset.sum D.factorZeros
        (fun rho =>
          (D.factorMultiplicity rho : Real) * Real.log D.config.averagingRadius -
            (D.factorMultiplicity rho : Real) *
              Real.log (Complex.abs (D.config.center - rho))) := by
        apply Finset.sum_congr rfl
        intro rho hRho
        unfold finiteFactorJensenWeight
        have hRadius : Not (D.config.averagingRadius = 0) :=
          D.config.averagingRadius_positive.ne'
        have hDistance :
            Not (Complex.abs (rho - D.config.center) = 0) :=
          (factor_zero_distance_positive D rho hRho).ne'
        rw [Real.log_div hRadius hDistance]
        have hAbs :
            Complex.abs (D.config.center - rho) =
              Complex.abs (rho - D.config.center) := by
          rw [show D.config.center - rho = -(rho - D.config.center) by ring]
          exact AbsoluteValue.map_neg Complex.abs (rho - D.config.center)
        rw [hAbs]
        ring
    _ = Finset.sum D.factorZeros
          (fun rho => (D.factorMultiplicity rho : Real)) *
            Real.log D.config.averagingRadius -
        Finset.sum D.factorZeros
          (fun rho =>
            (D.factorMultiplicity rho : Real) *
              Real.log (Complex.abs (D.config.center - rho))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]

/-- Buffered analytic factorization on the radius-`S` closed ball. -/
structure BufferedJensenFactorizationData where
  zeroData : JensenFactorZeroData
  f : Complex -> Complex
  g : Complex -> Complex

  f_analytic :
    AnalyticOnNhd Complex f
      (Metric.closedBall
        zeroData.config.center zeroData.config.analyticRadius)

  g_analytic :
    AnalyticOnNhd Complex g
      (Metric.closedBall
        zeroData.config.center zeroData.config.analyticRadius)

  factorization :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall
            zeroData.config.center zeroData.config.analyticRadius) z ->
        f z = finiteJensenZeroPolynomial zeroData z * g z

  g_nonzero :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall
            zeroData.config.center zeroData.config.analyticRadius) z ->
        Not (g z = 0)

namespace BufferedJensenFactorizationData

theorem mem_analyticClosedBall_of_abs_le
    (D : BufferedJensenFactorizationData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.zeroData.config.center) <=
        D.zeroData.config.analyticRadius) :
    Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius) z := by
  rw [D.zeroData.config.mem_closedBall_iff_abs_sub]
  exact hz

theorem zeroPolynomial_nonzero_on_collar
    (D : BufferedJensenFactorizationData)
    (z : Complex)
    (hLower :
      D.zeroData.config.averagingRadius <=
        Complex.abs (z - D.zeroData.config.center)) :
    Not (finiteJensenZeroPolynomial D.zeroData z = 0) := by
  apply finiteJensenZeroPolynomial_ne_zero_of_avoids_roots
  intro rho hRho hEq
  have hInside := D.zeroData.factor_zero_mem_open_disk rho hRho
  rw [hEq] at hLower
  exact (not_lt_of_ge hLower) hInside

theorem f_nonzero_on_collar
    (D : BufferedJensenFactorizationData)
    (z : Complex)
    (hLower :
      D.zeroData.config.averagingRadius <=
        Complex.abs (z - D.zeroData.config.center))
    (hUpper :
      Complex.abs (z - D.zeroData.config.center) <=
        D.zeroData.config.analyticRadius) :
    Not (D.f z = 0) := by
  have hMem := D.mem_analyticClosedBall_of_abs_le z hUpper
  rw [D.factorization z hMem]
  exact mul_ne_zero
    (D.zeroPolynomial_nonzero_on_collar z hLower)
    (D.g_nonzero z hMem)

theorem f_nonzero_on_averagingSphere
    (D : BufferedJensenFactorizationData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.zeroData.config.center) =
        D.zeroData.config.averagingRadius) :
    Not (D.f z = 0) := by
  apply D.f_nonzero_on_collar z hz.ge
  exact hz.le.trans D.zeroData.config.averagingRadius_lt_analyticRadius.le

theorem center_mem_analyticClosedBall
    (D : BufferedJensenFactorizationData) :
    Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius)
      D.zeroData.config.center := by
  apply D.mem_analyticClosedBall_of_abs_le
  simp [D.zeroData.config.analyticRadius_positive.le]

theorem f_nonzero_at_center
    (D : BufferedJensenFactorizationData) :
    Not (D.f D.zeroData.config.center = 0) := by
  have hMem := D.center_mem_analyticClosedBall
  rw [D.factorization D.zeroData.config.center hMem]
  exact mul_ne_zero
    (finiteJensenZeroPolynomial_at_center_ne_zero D.zeroData)
    (D.g_nonzero D.zeroData.config.center hMem)

theorem log_abs_factorization
    (D : BufferedJensenFactorizationData)
    (z : Complex)
    (hMem :
      Membership.mem
        (Metric.closedBall
          D.zeroData.config.center D.zeroData.config.analyticRadius) z)
    (hP : Not (finiteJensenZeroPolynomial D.zeroData z = 0)) :
    Real.log (Complex.abs (D.f z)) =
      Real.log (Complex.abs (finiteJensenZeroPolynomial D.zeroData z)) +
        Real.log (Complex.abs (D.g z)) := by
  rw [D.factorization z hMem, Complex.abs.map_mul]
  apply Real.log_mul
  case hx =>
    rw [<- Complex.norm_eq_abs, norm_ne_zero_iff]
    exact hP
  case hy =>
    rw [<- Complex.norm_eq_abs, norm_ne_zero_iff]
    exact D.g_nonzero z hMem

theorem log_abs_factorization_at_center
    (D : BufferedJensenFactorizationData) :
    Real.log (Complex.abs (D.f D.zeroData.config.center)) =
      Real.log
          (Complex.abs
            (finiteJensenZeroPolynomial D.zeroData D.zeroData.config.center)) +
        Real.log (Complex.abs (D.g D.zeroData.config.center)) :=
  D.log_abs_factorization D.zeroData.config.center
    D.center_mem_analyticClosedBall
    (finiteJensenZeroPolynomial_at_center_ne_zero D.zeroData)

end BufferedJensenFactorizationData

/-- Standard angular parametrization of a complex circle. -/
noncomputable def angularCirclePoint
    (center : Complex)
    (radius theta : Real) :
    Complex :=
  center + (radius : Complex) *
    Complex.exp (Complex.I * (theta : Complex))

/-- Normalized angular average over one turn. -/
noncomputable def angularCircleAverage
    (h : Complex -> Real)
    (center : Complex)
    (radius : Real) :
    Real :=
  (1 / (2 * Real.pi)) *
    intervalIntegral
      (fun theta => h (angularCirclePoint center radius theta))
      0 (2 * Real.pi) MeasureTheory.volume

/-- Interval-integrability of a function along the angular parametrization. -/
def AngularIntervalIntegrable
    (h : Complex -> Real)
    (center : Complex)
    (radius : Real) :
    Prop :=
  IntervalIntegrable
    (fun theta => h (angularCirclePoint center radius theta))
    MeasureTheory.volume 0 (2 * Real.pi)

theorem angularCirclePoint_abs_sub_center
    (center : Complex)
    (radius theta : Real)
    (hRadius : 0 <= radius) :
    Complex.abs (angularCirclePoint center radius theta - center) = radius := by
  unfold angularCirclePoint
  rw [add_sub_cancel_left]
  rw [Complex.abs.map_mul, Complex.abs_exp]
  simp [Complex.abs_ofReal, abs_of_nonneg hRadius]

theorem angularCircleAverage_congr
    (h k : Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hEq : forall theta : Real,
      h (angularCirclePoint center radius theta) =
        k (angularCirclePoint center radius theta)) :
    angularCircleAverage h center radius =
      angularCircleAverage k center radius := by
  unfold angularCircleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _
  exact hEq theta

theorem angularCircleAverage_const
    (a : Real)
    (center : Complex)
    (radius : Real) :
    angularCircleAverage (fun _ => a) center radius = a := by
  unfold angularCircleAverage
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp [Real.pi_ne_zero]

theorem angularCircleAverage_add
    (h k : Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hH : AngularIntervalIntegrable h center radius)
    (hK : AngularIntervalIntegrable k center radius) :
    angularCircleAverage (fun z => h z + k z) center radius =
      angularCircleAverage h center radius +
        angularCircleAverage k center radius := by
  unfold angularCircleAverage AngularIntervalIntegrable at *
  rw [intervalIntegral.integral_add hH hK]
  ring

theorem angularIntervalIntegrable_add
    (h k : Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hH : AngularIntervalIntegrable h center radius)
    (hK : AngularIntervalIntegrable k center radius) :
    AngularIntervalIntegrable (fun z => h z + k z) center radius := by
  unfold AngularIntervalIntegrable at hH hK
  unfold AngularIntervalIntegrable
  exact hH.add hK

theorem angularIntervalIntegrable_congr
    (h k : Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hH : AngularIntervalIntegrable h center radius)
    (hEq : forall theta : Real,
      h (angularCirclePoint center radius theta) =
        k (angularCirclePoint center radius theta)) :
    AngularIntervalIntegrable k center radius := by
  unfold AngularIntervalIntegrable at hH
  unfold AngularIntervalIntegrable
  apply hH.congr
  filter_upwards [] with theta
  exact hEq theta

theorem angularCircleAverage_const_mul
    (a : Real)
    (h : Complex -> Real)
    (center : Complex)
    (radius : Real) :
    angularCircleAverage (fun z => a * h z) center radius =
      a * angularCircleAverage h center radius := by
  unfold angularCircleAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem angularIntervalIntegrable_const_mul
    (a : Real)
    (h : Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hInt : AngularIntervalIntegrable h center radius) :
    AngularIntervalIntegrable (fun z => a * h z) center radius := by
  unfold AngularIntervalIntegrable at hInt
  unfold AngularIntervalIntegrable
  exact hInt.const_mul a

theorem angularIntervalIntegrable_finset_sum
    {alpha : Type*}
    (s : Finset alpha)
    (h : alpha -> Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hInt : forall i : alpha,
      Membership.mem s i ->
        AngularIntervalIntegrable (h i) center radius) :
    AngularIntervalIntegrable
      (fun z => Finset.sum s (fun i => h i z)) center radius := by
  unfold AngularIntervalIntegrable at hInt
  unfold AngularIntervalIntegrable
  classical
  revert hInt
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using (intervalIntegrable_const :
        IntervalIntegrable (fun _ : Real => (0 : Real))
          MeasureTheory.volume 0 (2 * Real.pi))
  | @insert a s ha ih =>
      intro hInt
      have haInt := hInt a (Finset.mem_insert_self a s)
      have hsInt := ih (fun i hi => hInt i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using haInt.add hsInt

theorem angularCircleAverage_finset_sum
    {alpha : Type*}
    (s : Finset alpha)
    (h : alpha -> Complex -> Real)
    (center : Complex)
    (radius : Real)
    (hInt : forall i : alpha,
      Membership.mem s i ->
        AngularIntervalIntegrable (h i) center radius) :
    angularCircleAverage (fun z => Finset.sum s (fun i => h i z)) center radius =
      Finset.sum s (fun i => angularCircleAverage (h i) center radius) := by
  unfold angularCircleAverage AngularIntervalIntegrable at *
  rw [intervalIntegral.integral_finset_sum hInt]
  rw [Finset.mul_sum]

/-- TS276 input: each logarithmic linear factor has its classical mean. -/
structure LinearFactorAngularAverageStatement
    (D : JensenFactorZeroData) : Prop where
  intervalIntegrable :
    forall rho : Complex,
      Membership.mem D.factorZeros rho ->
        AngularIntervalIntegrable
          (fun z => Real.log (Complex.abs (z - rho)))
          D.config.center D.config.averagingRadius

  average_eq :
    forall rho : Complex,
      Membership.mem D.factorZeros rho ->
        angularCircleAverage
            (fun z => Real.log (Complex.abs (z - rho)))
            D.config.center D.config.averagingRadius =
          Real.log D.config.averagingRadius

/-- The logarithm of the factor polynomial is integrable on the circle. -/
theorem factorPolynomialLog_angularIntervalIntegrable
    (D : JensenFactorZeroData)
    (H : LinearFactorAngularAverageStatement D) :
    AngularIntervalIntegrable
      (fun z => Real.log (Complex.abs (finiteJensenZeroPolynomial D z)))
      D.config.center D.config.averagingRadius := by
  have hSum :
      AngularIntervalIntegrable
        (fun z =>
          Finset.sum D.factorZeros
            (fun rho =>
              (D.factorMultiplicity rho : Real) *
                Real.log (Complex.abs (z - rho))))
        D.config.center D.config.averagingRadius := by
    apply angularIntervalIntegrable_finset_sum
    intro rho hRho
    exact angularIntervalIntegrable_const_mul _ _ _ _
      (H.intervalIntegrable rho hRho)
  unfold AngularIntervalIntegrable at hSum
  unfold AngularIntervalIntegrable
  apply hSum.congr
  filter_upwards [] with theta
  symm
  apply finiteJensenZeroPolynomial_log_abs_of_avoids_roots
  intro rho hRho hEq
  have hPoint := angularCirclePoint_abs_sub_center
    D.config.center D.config.averagingRadius theta
    D.config.averagingRadius_positive.le
  rw [hEq] at hPoint
  exact (ne_of_lt (D.factor_zero_mem_open_disk rho hRho)) hPoint

/-- TS276 linear-factor means give the polynomial logarithmic mean. -/
theorem factorPolynomialLog_angularCircleAverage
    (D : JensenFactorZeroData)
    (H : LinearFactorAngularAverageStatement D) :
    angularCircleAverage
        (fun z => Real.log (Complex.abs (finiteJensenZeroPolynomial D z)))
        D.config.center D.config.averagingRadius =
      finiteFactorMultiplicityMass D *
        Real.log D.config.averagingRadius := by
  calc
    angularCircleAverage
        (fun z => Real.log (Complex.abs (finiteJensenZeroPolynomial D z)))
        D.config.center D.config.averagingRadius =
      angularCircleAverage
        (fun z =>
          Finset.sum D.factorZeros
            (fun rho =>
              (D.factorMultiplicity rho : Real) *
                Real.log (Complex.abs (z - rho))))
        D.config.center D.config.averagingRadius := by
          apply angularCircleAverage_congr
          intro theta
          apply finiteJensenZeroPolynomial_log_abs_of_avoids_roots
          intro rho hRho hEq
          have hPoint := angularCirclePoint_abs_sub_center
            D.config.center D.config.averagingRadius theta
            D.config.averagingRadius_positive.le
          rw [hEq] at hPoint
          exact (ne_of_lt (D.factor_zero_mem_open_disk rho hRho)) hPoint
    _ = Finset.sum D.factorZeros
        (fun rho =>
          angularCircleAverage
            (fun z =>
              (D.factorMultiplicity rho : Real) *
                Real.log (Complex.abs (z - rho)))
            D.config.center D.config.averagingRadius) := by
          apply angularCircleAverage_finset_sum
          intro rho hRho
          exact (H.intervalIntegrable rho hRho).const_mul _
    _ = Finset.sum D.factorZeros
        (fun rho =>
          (D.factorMultiplicity rho : Real) *
            angularCircleAverage
              (fun z => Real.log (Complex.abs (z - rho)))
              D.config.center D.config.averagingRadius) := by
          apply Finset.sum_congr rfl
          intro rho _
          rw [angularCircleAverage_const_mul]
    _ = Finset.sum D.factorZeros
        (fun rho =>
          (D.factorMultiplicity rho : Real) *
            Real.log D.config.averagingRadius) := by
          apply Finset.sum_congr rfl
          intro rho hRho
          rw [H.average_eq rho hRho]
    _ = finiteFactorMultiplicityMass D *
        Real.log D.config.averagingRadius := by
          unfold finiteFactorMultiplicityMass
          rw [Finset.sum_mul]

/-- TS277 input: logarithmic mean value for the nonvanishing quotient. -/
structure NonvanishingQuotientAngularAverageStatement
    (D : BufferedJensenFactorizationData) : Prop where
  intervalIntegrable :
    AngularIntervalIntegrable
      (fun z => Real.log (Complex.abs (D.g z)))
      D.zeroData.config.center D.zeroData.config.averagingRadius

  average_eq :
    angularCircleAverage
        (fun z => Real.log (Complex.abs (D.g z)))
      D.zeroData.config.center D.zeroData.config.averagingRadius =
      Real.log (Complex.abs (D.g D.zeroData.config.center))

/-- Pointwise logarithmic factorization on the averaging circle. -/
theorem buffered_log_abs_factorization_on_angularCircle
    (D : BufferedJensenFactorizationData)
    (theta : Real) :
    Real.log
        (Complex.abs
          (D.f
            (angularCirclePoint
              D.zeroData.config.center
              D.zeroData.config.averagingRadius theta))) =
      Real.log
          (Complex.abs
            (finiteJensenZeroPolynomial D.zeroData
              (angularCirclePoint
                D.zeroData.config.center
                D.zeroData.config.averagingRadius theta))) +
        Real.log
          (Complex.abs
            (D.g
              (angularCirclePoint
                D.zeroData.config.center
                D.zeroData.config.averagingRadius theta))) := by
  let z := angularCirclePoint
    D.zeroData.config.center D.zeroData.config.averagingRadius theta
  have hSphere :
      Complex.abs (z - D.zeroData.config.center) =
        D.zeroData.config.averagingRadius :=
    angularCirclePoint_abs_sub_center
      D.zeroData.config.center D.zeroData.config.averagingRadius theta
      D.zeroData.config.averagingRadius_positive.le
  have hMem := D.zeroData.config.averagingSphere_mem_analyticClosedBall z hSphere
  exact D.log_abs_factorization z hMem
    (D.zeroPolynomial_nonzero_on_collar z hSphere.ge)

theorem buffered_log_abs_f_angularIntervalIntegrable
    (D : BufferedJensenFactorizationData)
    (HLinear : LinearFactorAngularAverageStatement D.zeroData)
    (HQuotient : NonvanishingQuotientAngularAverageStatement D) :
    AngularIntervalIntegrable
      (fun z => Real.log (Complex.abs (D.f z)))
      D.zeroData.config.center D.zeroData.config.averagingRadius := by
  have hAdd := angularIntervalIntegrable_add
    (fun z => Real.log (Complex.abs (finiteJensenZeroPolynomial D.zeroData z)))
    (fun z => Real.log (Complex.abs (D.g z)))
    D.zeroData.config.center D.zeroData.config.averagingRadius
    (factorPolynomialLog_angularIntervalIntegrable D.zeroData HLinear)
    HQuotient.intervalIntegrable
  apply angularIntervalIntegrable_congr
    (fun z =>
      Real.log (Complex.abs (finiteJensenZeroPolynomial D.zeroData z)) +
        Real.log (Complex.abs (D.g z)))
    (fun z => Real.log (Complex.abs (D.f z)))
    D.zeroData.config.center D.zeroData.config.averagingRadius hAdd
  intro theta
  exact (buffered_log_abs_factorization_on_angularCircle D theta).symm

/-- The two mean-value inputs determine the logarithmic mean of `f`. -/
theorem buffered_log_abs_f_angularCircleAverage
    (D : BufferedJensenFactorizationData)
    (HLinear : LinearFactorAngularAverageStatement D.zeroData)
    (HQuotient : NonvanishingQuotientAngularAverageStatement D) :
    angularCircleAverage
        (fun z => Real.log (Complex.abs (D.f z)))
        D.zeroData.config.center D.zeroData.config.averagingRadius =
      finiteFactorMultiplicityMass D.zeroData *
          Real.log D.zeroData.config.averagingRadius +
        Real.log (Complex.abs (D.g D.zeroData.config.center)) := by
  calc
    angularCircleAverage
        (fun z => Real.log (Complex.abs (D.f z)))
        D.zeroData.config.center D.zeroData.config.averagingRadius =
      angularCircleAverage
        (fun z =>
          Real.log (Complex.abs (finiteJensenZeroPolynomial D.zeroData z)) +
            Real.log (Complex.abs (D.g z)))
        D.zeroData.config.center D.zeroData.config.averagingRadius := by
          apply angularCircleAverage_congr
          intro theta
          exact buffered_log_abs_factorization_on_angularCircle D theta
    _ = angularCircleAverage
          (fun z => Real.log (Complex.abs (finiteJensenZeroPolynomial D.zeroData z)))
          D.zeroData.config.center D.zeroData.config.averagingRadius +
        angularCircleAverage
          (fun z => Real.log (Complex.abs (D.g z)))
          D.zeroData.config.center D.zeroData.config.averagingRadius := by
          apply angularCircleAverage_add
          case hH =>
            exact factorPolynomialLog_angularIntervalIntegrable D.zeroData HLinear
          case hK =>
            exact HQuotient.intervalIntegrable
    _ = finiteFactorMultiplicityMass D.zeroData *
          Real.log D.zeroData.config.averagingRadius +
        Real.log (Complex.abs (D.g D.zeroData.config.center)) := by
          rw [factorPolynomialLog_angularCircleAverage D.zeroData HLinear]
          rw [HQuotient.average_eq]

/-- A pointwise boundary norm bound on the averaging sphere. -/
structure BoundaryNormOnAveragingSphereStatement
    (D : BufferedJensenFactorizationData)
    (M : Real) : Prop where
  M_positive : 0 < M

  norm_le :
    forall z : Complex,
      Complex.abs (z - D.zeroData.config.center) =
          D.zeroData.config.averagingRadius ->
        Complex.abs (D.f z) <= M

/-- A pointwise boundary norm bound controls the normalized log average. -/
theorem angularCircleAverage_log_abs_f_le_log_bound
    (D : BufferedJensenFactorizationData)
    (M : Real)
    (HLinear : LinearFactorAngularAverageStatement D.zeroData)
    (HQuotient : NonvanishingQuotientAngularAverageStatement D)
    (HBoundary : BoundaryNormOnAveragingSphereStatement D M) :
    angularCircleAverage
        (fun z => Real.log (Complex.abs (D.f z)))
        D.zeroData.config.center D.zeroData.config.averagingRadius <=
      Real.log M := by
  have hFInt := buffered_log_abs_f_angularIntervalIntegrable D HLinear HQuotient
  unfold angularCircleAverage AngularIntervalIntegrable at hFInt
  have hConst :
      IntervalIntegrable (fun _ : Real => Real.log M)
        MeasureTheory.volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have hIntegral :
      intervalIntegral
          (fun theta =>
            Real.log
              (Complex.abs
                (D.f
                  (angularCirclePoint
                    D.zeroData.config.center
                    D.zeroData.config.averagingRadius theta))))
          0 (2 * Real.pi) MeasureTheory.volume <=
        intervalIntegral (fun _ : Real => Real.log M)
          0 (2 * Real.pi) MeasureTheory.volume := by
    apply intervalIntegral.integral_mono_on
      (show (0 : Real) <= 2 * Real.pi by positivity) hFInt hConst
    intro theta _
    let z := angularCirclePoint
      D.zeroData.config.center D.zeroData.config.averagingRadius theta
    have hSphere :
        Complex.abs (z - D.zeroData.config.center) =
          D.zeroData.config.averagingRadius :=
      angularCirclePoint_abs_sub_center
        D.zeroData.config.center D.zeroData.config.averagingRadius theta
        D.zeroData.config.averagingRadius_positive.le
    have hFNonzero := D.f_nonzero_on_averagingSphere z hSphere
    have hAbsPositive : 0 < Complex.abs (D.f z) := by
      rw [<- Complex.norm_eq_abs, norm_pos_iff]
      exact hFNonzero
    exact Real.strictMonoOn_log.monotoneOn
      hAbsPositive HBoundary.M_positive
      (HBoundary.norm_le z hSphere)
  have hScale : 0 <= 1 / (2 * Real.pi) := by positivity
  calc
    (1 / (2 * Real.pi)) *
        intervalIntegral
          (fun theta =>
            Real.log
              (Complex.abs
                (D.f
                  (angularCirclePoint
                    D.zeroData.config.center
                    D.zeroData.config.averagingRadius theta))))
          0 (2 * Real.pi) MeasureTheory.volume <=
      (1 / (2 * Real.pi)) *
        intervalIntegral (fun _ : Real => Real.log M)
          0 (2 * Real.pi) MeasureTheory.volume :=
        mul_le_mul_of_nonneg_left hIntegral hScale
    _ = Real.log M := by
      simpa [angularCircleAverage] using
        angularCircleAverage_const (Real.log M)
          D.zeroData.config.center D.zeroData.config.averagingRadius

/-- Main TS275 reduction: factorization plus the two means fill TS274's slot. -/
theorem finiteJensenBoundaryEstimate_of_factorization_and_angularMeans
    (D : BufferedJensenFactorizationData)
    (M : Real)
    (HLinear : LinearFactorAngularAverageStatement D.zeroData)
    (HQuotient : NonvanishingQuotientAngularAverageStatement D)
    (HBoundary : BoundaryNormOnAveragingSphereStatement D M) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData D.f M := by
  unfold TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
  unfold TS274.Goldbach.FiniteJensenWeightedUpperBoundStatement
  unfold TS274.Goldbach.finiteJensenBoundaryLogBudget
  have hAverage := buffered_log_abs_f_angularCircleAverage D HLinear HQuotient
  have hAverageLe := angularCircleAverage_log_abs_f_le_log_bound
    D M HLinear HQuotient HBoundary
  have hCore :
      finiteFactorMultiplicityMass D.zeroData *
            Real.log D.zeroData.config.averagingRadius +
          Real.log (Complex.abs (D.g D.zeroData.config.center)) <=
        Real.log M := by
    rw [<- hAverage]
    exact hAverageLe
  have hFactorMass :
      finiteFactorJensenWeightedMass D.zeroData <=
        Real.log M - Real.log (Complex.abs (D.f D.zeroData.config.center)) := by
    rw [finiteFactorJensenWeightedMass_eq]
    rw [D.log_abs_factorization_at_center]
    linarith
  have hFAbs :
      Not (Complex.abs (D.f D.zeroData.config.center) = 0) := by
    intro hAbs
    exact D.f_nonzero_at_center (Complex.abs.eq_zero.mp hAbs)
  calc
    TS274.Goldbach.finiteJensenWeightedMass
        D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData <=
      finiteFactorJensenWeightedMass D.zeroData :=
        innerJensenWeightedMass_le_factorJensenWeightedMass D.zeroData
    _ <= Real.log M -
        Real.log (Complex.abs (D.f D.zeroData.config.center)) := hFactorMass
    _ = Real.log
        (M / Complex.abs (D.f D.zeroData.config.center)) := by
      rw [Real.log_div HBoundary.M_positive.ne' hFAbs]

/-- Concrete TS275 ledger with the complete finite reduction. -/
structure FiniteJensenPolynomialFactorizationReductionLedger where
  ts274_backport :
    TS274.Goldbach.MinimalJensenInequalityBackportLedger

  zero_polynomial_analytic :
    forall (D : JensenFactorZeroData) (s : Set Complex),
      AnalyticOnNhd Complex (finiteJensenZeroPolynomial D) s

  inner_mass_le_factor_mass :
    forall D : JensenFactorZeroData,
      TS274.Goldbach.finiteJensenWeightedMass
          D.toJensenInnerZeroData.toFiniteJensenDiskData <=
        finiteFactorJensenWeightedMass D

  factor_mass_identity :
    forall D : JensenFactorZeroData,
      finiteFactorJensenWeightedMass D =
        finiteFactorMultiplicityMass D * Real.log D.config.averagingRadius -
          Real.log
            (Complex.abs
              (finiteJensenZeroPolynomial D D.config.center))

  boundary_reduction :
    forall (D : BufferedJensenFactorizationData) (M : Real),
      LinearFactorAngularAverageStatement D.zeroData ->
        NonvanishingQuotientAngularAverageStatement D ->
          BoundaryNormOnAveragingSphereStatement D M ->
            TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
              D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData D.f M

  factorization_construction_not_proved : True
  linear_factor_angular_average_not_proved : True
  nonvanishing_quotient_log_mean_not_proved : True
  analytic_zero_finset_not_constructed : True
  riemann_xi_not_defined : True
  zeta_counting_estimate_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

noncomputable def finiteJensenPolynomialFactorizationReductionLedger :
    FiniteJensenPolynomialFactorizationReductionLedger where
  ts274_backport := TS274.Goldbach.minimalJensenInequalityBackportLedger
  zero_polynomial_analytic := finiteJensenZeroPolynomial_analyticOnNhd
  inner_mass_le_factor_mass := innerJensenWeightedMass_le_factorJensenWeightedMass
  factor_mass_identity := finiteFactorJensenWeightedMass_eq
  boundary_reduction :=
    finiteJensenBoundaryEstimate_of_factorization_and_angularMeans
  factorization_construction_not_proved := True.intro
  linear_factor_angular_average_not_proved := True.intro
  nonvanishing_quotient_log_mean_not_proved := True.intro
  analytic_zero_finset_not_constructed := True.intro
  riemann_xi_not_defined := True.intro
  zeta_counting_estimate_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

def FiniteJensenPolynomialFactorizationReductionTarget : Prop :=
  Nonempty FiniteJensenPolynomialFactorizationReductionLedger

theorem finiteJensenPolynomialFactorizationReductionTarget :
    FiniteJensenPolynomialFactorizationReductionTarget :=
  Nonempty.intro finiteJensenPolynomialFactorizationReductionLedger

end Goldbach
end TS275
