import Mathlib.Tactic
import TS.Goldbach.Strong.TS275.FiniteJensenPolynomialFactorizationReduction

/-!
# TS276 - Linear Factor Angular Average

TS275 reduced its finite Jensen boundary estimate to the angular means of
linear factors and of a nonvanishing quotient.  This sprint discharges the
linear-factor port.

For a root strictly inside the averaging circle, normalize its displacement
to `a` with `abs a < 1`.  The function

`z |-> Complex.log (1 - (starRingEnd Complex) a * z)`

is continuous on the closed unit disk and complex differentiable in the open
unit disk because its argument stays in the slit plane.  Cauchy's formula at
the center makes its circular integral zero.  Taking real parts gives zero
average for `log |1 - star a * exp(i theta)|`.  Elementary circle geometry
then transports this identity to `log |c + R exp(i theta) - rho|`.

No Fourier series, infinite-sum interchange, Jensen divisor theorem,
nonvanishing-quotient mean value, concrete xi function, zeta counting bound,
explicit formula, Gallagher estimate, OTSA bridge, or Goldbach statement is
claimed.
-/

namespace TS276
namespace Goldbach

open MeasureTheory

/-- The displacement of a root normalized by the averaging radius. -/
noncomputable def normalizedLinearRoot
    (center rho : Complex)
    (radius : Real) : Complex :=
  (rho - center) / (radius : Complex)

/-- The holomorphic logarithmic factor used on the unit disk. -/
noncomputable def unitDiskLogFactor
    (a z : Complex) : Complex :=
  Complex.log (1 - (starRingEnd Complex) a * z)

/-- The real logarithmic boundary value of the normalized factor. -/
noncomputable def unitDiskBoundaryLog
    (a : Complex)
    (theta : Real) : Real :=
  Real.log
    (Complex.abs
      (1 - (starRingEnd Complex) a * circleMap 0 1 theta))

theorem normalizedLinearRoot_abs_lt_one
    (center rho : Complex)
    (radius : Real)
    (hRadius : 0 < radius)
    (hInside : Complex.abs (rho - center) < radius) :
    Complex.abs (normalizedLinearRoot center rho radius) < 1 := by
  unfold normalizedLinearRoot
  rw [<- Complex.norm_eq_abs, norm_div]
  simp only [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_pos hRadius]
  exact (div_lt_one hRadius).2 hInside

theorem unitDiskLogArgument_mem_slitPlane
    (a z : Complex)
    (hA : Complex.abs a < 1)
    (hZ : Membership.mem (Metric.closedBall (0 : Complex) 1) z) :
    Membership.mem Complex.slitPlane
      (1 - (starRingEnd Complex) a * z) := by
  have hZAbs : Complex.abs z <= 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, Complex.norm_eq_abs] using hZ
  have hNorm : norm (-((starRingEnd Complex) a * z)) < 1 := by
    rw [norm_neg, Complex.norm_eq_abs, Complex.abs.map_mul]
    calc
      Complex.abs ((starRingEnd Complex) a) * Complex.abs z <=
          Complex.abs ((starRingEnd Complex) a) * 1 :=
        mul_le_mul_of_nonneg_left hZAbs
          (Complex.abs.nonneg ((starRingEnd Complex) a))
      _ = Complex.abs a * 1 := by rw [Complex.abs_conj]
      _ < 1 := by simpa using hA
  simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hNorm

theorem unitDiskLogFactor_continuousAt
    (a z : Complex)
    (hA : Complex.abs a < 1)
    (hZ : Membership.mem (Metric.closedBall (0 : Complex) 1) z) :
    ContinuousAt (unitDiskLogFactor a) z := by
  have hInner :
      ContinuousAt
        (fun w : Complex => 1 - (starRingEnd Complex) a * w) z := by
    fun_prop
  exact hInner.clog (unitDiskLogArgument_mem_slitPlane a z hA hZ)

theorem unitDiskLogFactor_continuousOn_closedBall
    (a : Complex)
    (hA : Complex.abs a < 1) :
    ContinuousOn (unitDiskLogFactor a)
      (Metric.closedBall (0 : Complex) 1) := by
  intro z hZ
  exact (unitDiskLogFactor_continuousAt a z hA hZ).continuousWithinAt

theorem unitDiskLogFactor_differentiableAt
    (a z : Complex)
    (hA : Complex.abs a < 1)
    (hZ : Membership.mem (Metric.ball (0 : Complex) 1) z) :
    DifferentiableAt Complex (unitDiskLogFactor a) z := by
  have hZClosed : Membership.mem (Metric.closedBall (0 : Complex) 1) z :=
    Metric.ball_subset_closedBall hZ
  have hInner :
      DifferentiableAt Complex
        (fun w : Complex => 1 - (starRingEnd Complex) a * w) z := by
    fun_prop
  exact (Complex.differentiableAt_log
    (unitDiskLogArgument_mem_slitPlane a z hA hZClosed)).comp z hInner

theorem unitDiskLogFactor_circleIntegral_eq_zero
    (a : Complex)
    (hA : Complex.abs a < 1) :
    (circleIntegral
      (fun z : Complex => Inv.inv z * unitDiskLogFactor a z) 0 1) = 0 := by
  have hCauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      (E := Complex)
      (R := 1)
      (c := (0 : Complex))
      (f := unitDiskLogFactor a)
      (s := ({0} : Set Complex))
      one_pos (Set.countable_singleton (0 : Complex))
      (unitDiskLogFactor_continuousOn_closedBall a hA)
      (fun z hz => unitDiskLogFactor_differentiableAt a z hA hz.1)
  simpa [unitDiskLogFactor, smul_eq_mul] using hCauchy

theorem unitDiskLogFactor_circleIntegral_eq_I_mul_intervalIntegral
    (a : Complex) :
    circleIntegral
        (fun z : Complex => Inv.inv z * unitDiskLogFactor a z) 0 1 =
      Complex.I *
        intervalIntegral
          (fun theta : Real =>
            unitDiskLogFactor a (circleMap 0 1 theta))
          0 (2 * Real.pi) MeasureTheory.volume := by
  unfold circleIntegral
  calc
    intervalIntegral
        (fun theta : Real =>
          deriv (circleMap 0 1) theta *
            (Inv.inv (circleMap 0 1 theta) *
              unitDiskLogFactor a (circleMap 0 1 theta)))
        0 (2 * Real.pi) MeasureTheory.volume =
      intervalIntegral
        (fun theta : Real =>
          Complex.I * unitDiskLogFactor a (circleMap 0 1 theta))
        0 (2 * Real.pi) MeasureTheory.volume := by
          apply intervalIntegral.integral_congr
          intro theta _
          simp [deriv_circleMap, circleMap, smul_eq_mul, mul_assoc,
            mul_comm, mul_left_comm, Complex.exp_ne_zero]
    _ = Complex.I *
        intervalIntegral
          (fun theta : Real =>
            unitDiskLogFactor a (circleMap 0 1 theta))
          0 (2 * Real.pi) MeasureTheory.volume := by
          exact intervalIntegral.integral_const_mul Complex.I _

theorem unitDiskLogFactor_intervalIntegral_eq_zero
    (a : Complex)
    (hA : Complex.abs a < 1) :
    intervalIntegral
        (fun theta : Real =>
          unitDiskLogFactor a (circleMap 0 1 theta))
        0 (2 * Real.pi) MeasureTheory.volume = 0 := by
  have hCircle := unitDiskLogFactor_circleIntegral_eq_zero a hA
  rw [unitDiskLogFactor_circleIntegral_eq_I_mul_intervalIntegral] at hCircle
  exact (mul_eq_zero.mp hCircle).resolve_left Complex.I_ne_zero

theorem unitDiskLogFactor_angularIntervalIntegrable
    (a : Complex)
    (hA : Complex.abs a < 1) :
    IntervalIntegrable
      (fun theta : Real =>
        unitDiskLogFactor a (circleMap 0 1 theta))
      MeasureTheory.volume 0 (2 * Real.pi) := by
  have hContinuous :
      Continuous
        (fun theta : Real =>
          unitDiskLogFactor a (circleMap 0 1 theta)) := by
    rw [continuous_iff_continuousAt]
    intro theta
    exact (unitDiskLogFactor_continuousAt a _ hA
      (circleMap_mem_closedBall 0 (show (0 : Real) <= 1 by norm_num) theta)).comp
        (continuous_circleMap 0 1).continuousAt
  exact hContinuous.intervalIntegrable 0 (2 * Real.pi)

theorem unitDiskBoundaryLog_intervalIntegral_eq_zero
    (a : Complex)
    (hA : Complex.abs a < 1) :
    intervalIntegral (unitDiskBoundaryLog a)
      0 (2 * Real.pi) MeasureTheory.volume = 0 := by
  have hInt := unitDiskLogFactor_angularIntervalIntegrable a hA
  have hMap := Complex.reCLM.intervalIntegral_comp_comm hInt
  have hZero := unitDiskLogFactor_intervalIntegral_eq_zero a hA
  rw [hZero, map_zero] at hMap
  simpa [unitDiskBoundaryLog, unitDiskLogFactor, Complex.log_re,
    Complex.reCLM_apply] using hMap

theorem unitDiskBoundaryLog_continuous
    (a : Complex)
    (hA : Complex.abs a < 1) :
    Continuous (unitDiskBoundaryLog a) := by
  have hComplex :
      Continuous
        (fun theta : Real =>
          unitDiskLogFactor a (circleMap 0 1 theta)) := by
    rw [continuous_iff_continuousAt]
    intro theta
    exact (unitDiskLogFactor_continuousAt a _ hA
      (circleMap_mem_closedBall 0 (show (0 : Real) <= 1 by norm_num) theta)).comp
        (continuous_circleMap 0 1).continuousAt
  have hReal := Complex.continuous_re.comp hComplex
  have hEq :
      unitDiskBoundaryLog a =
        fun theta : Real =>
          (unitDiskLogFactor a (circleMap 0 1 theta)).re := by
    funext theta
    exact (Complex.log_re _).symm
  rw [hEq]
  simpa [Function.comp_apply] using hReal

theorem unitDiskBoundaryLog_intervalIntegrable
    (a : Complex)
    (hA : Complex.abs a < 1) :
    IntervalIntegrable (unitDiskBoundaryLog a)
      MeasureTheory.volume 0 (2 * Real.pi) :=
  (unitDiskBoundaryLog_continuous a hA).intervalIntegrable 0 (2 * Real.pi)

/-- On the unit circle, a linear distance equals its conjugate-product form. -/
theorem abs_sub_eq_abs_one_sub_conj_mul
    (u a : Complex)
    (hU : Complex.abs u = 1) :
    Complex.abs (u - a) =
      Complex.abs (1 - (starRingEnd Complex) a * u) := by
  have hUnit : (starRingEnd Complex) u * u = 1 := by
    rw [Complex.conj_mul', Complex.norm_eq_abs, hU]
    norm_num
  have hConjEq :
      (starRingEnd Complex)
          (1 - (starRingEnd Complex) a * u) =
        (starRingEnd Complex) u * (u - a) := by
    calc
      (starRingEnd Complex)
          (1 - (starRingEnd Complex) a * u) =
        1 - (starRingEnd Complex) u * a := by simp [mul_comm]
      _ = (starRingEnd Complex) u * u -
          (starRingEnd Complex) u * a := by rw [hUnit]
      _ = (starRingEnd Complex) u * (u - a) := by ring
  calc
    Complex.abs (u - a) =
        Complex.abs ((starRingEnd Complex) u) * Complex.abs (u - a) := by
      rw [Complex.abs_conj, hU, one_mul]
    _ = Complex.abs ((starRingEnd Complex) u * (u - a)) := by
      rw [Complex.abs.map_mul]
    _ = Complex.abs
        ((starRingEnd Complex)
          (1 - (starRingEnd Complex) a * u)) := by rw [hConjEq]
    _ = Complex.abs (1 - (starRingEnd Complex) a * u) := by
      rw [Complex.abs_conj]

theorem angularCirclePoint_eq_center_add_radius_mul_circleMap
    (center : Complex)
    (radius theta : Real) :
    TS275.Goldbach.angularCirclePoint center radius theta =
      center + (radius : Complex) * circleMap 0 1 theta := by
  simp [TS275.Goldbach.angularCirclePoint, circleMap, mul_comm]

theorem angularCirclePoint_sub_root_eq_scaled
    (center rho : Complex)
    (radius theta : Real)
    (hRadius : 0 < radius) :
    TS275.Goldbach.angularCirclePoint center radius theta - rho =
      (radius : Complex) *
        (circleMap 0 1 theta - normalizedLinearRoot center rho radius) := by
  rw [angularCirclePoint_eq_center_add_radius_mul_circleMap]
  unfold normalizedLinearRoot
  have hRadiusComplex : Not ((radius : Complex) = 0) := by
    exact_mod_cast hRadius.ne'
  field_simp [hRadiusComplex]
  ring

theorem angularCirclePoint_sub_root_abs_eq
    (center rho : Complex)
    (radius theta : Real)
    (hRadius : 0 < radius) :
    Complex.abs
        (TS275.Goldbach.angularCirclePoint center radius theta - rho) =
      radius *
        Complex.abs
          (1 -
            (starRingEnd Complex)
                (normalizedLinearRoot center rho radius) *
              circleMap 0 1 theta) := by
  rw [angularCirclePoint_sub_root_eq_scaled center rho radius theta hRadius]
  rw [Complex.abs.map_mul, Complex.abs_ofReal, abs_of_pos hRadius]
  rw [abs_sub_eq_abs_one_sub_conj_mul]
  simpa using abs_circleMap_zero 1 theta

theorem linearFactor_boundaryLog_eq
    (center rho : Complex)
    (radius theta : Real)
    (hRadius : 0 < radius)
    (hInside : Complex.abs (rho - center) < radius) :
    Real.log
        (Complex.abs
          (TS275.Goldbach.angularCirclePoint center radius theta - rho)) =
      Real.log radius +
        unitDiskBoundaryLog
          (normalizedLinearRoot center rho radius) theta := by
  have hA := normalizedLinearRoot_abs_lt_one
    center rho radius hRadius hInside
  have hArgMem := unitDiskLogArgument_mem_slitPlane
    (normalizedLinearRoot center rho radius)
    (circleMap 0 1 theta) hA
    (circleMap_mem_closedBall 0 (show (0 : Real) <= 1 by norm_num) theta)
  have hArgAbs :
      Not
        (Complex.abs
          (1 -
            (starRingEnd Complex)
                (normalizedLinearRoot center rho radius) *
              circleMap 0 1 theta) = 0) := by
    intro hZero
    exact Complex.slitPlane_ne_zero hArgMem
      (Complex.abs.eq_zero.mp hZero)
  rw [angularCirclePoint_sub_root_abs_eq center rho radius theta hRadius]
  rw [Real.log_mul hRadius.ne' hArgAbs]
  rfl

theorem linearFactor_angularIntervalIntegrable
    (center rho : Complex)
    (radius : Real)
    (hRadius : 0 < radius)
    (hInside : Complex.abs (rho - center) < radius) :
    TS275.Goldbach.AngularIntervalIntegrable
      (fun z => Real.log (Complex.abs (z - rho))) center radius := by
  unfold TS275.Goldbach.AngularIntervalIntegrable
  apply IntervalIntegrable.congr
    ((intervalIntegrable_const.add
      (unitDiskBoundaryLog_intervalIntegrable
        (normalizedLinearRoot center rho radius)
        (normalizedLinearRoot_abs_lt_one
          center rho radius hRadius hInside))))
  filter_upwards [] with theta
  exact (linearFactor_boundaryLog_eq
    center rho radius theta hRadius hInside).symm

theorem linearFactor_angularCircleAverage_eq
    (center rho : Complex)
    (radius : Real)
    (hRadius : 0 < radius)
    (hInside : Complex.abs (rho - center) < radius) :
    TS275.Goldbach.angularCircleAverage
        (fun z => Real.log (Complex.abs (z - rho))) center radius =
      Real.log radius := by
  unfold TS275.Goldbach.angularCircleAverage
  rw [intervalIntegral.integral_congr
    (fun theta _ =>
      linearFactor_boundaryLog_eq center rho radius theta hRadius hInside)]
  rw [intervalIntegral.integral_add]
  case hf => exact intervalIntegrable_const
  case hg =>
    exact unitDiskBoundaryLog_intervalIntegrable
      (normalizedLinearRoot center rho radius)
      (normalizedLinearRoot_abs_lt_one center rho radius hRadius hInside)
  rw [unitDiskBoundaryLog_intervalIntegral_eq_zero
    (normalizedLinearRoot center rho radius)
    (normalizedLinearRoot_abs_lt_one center rho radius hRadius hInside)]
  rw [intervalIntegral.integral_const]
  field_simp [Real.pi_ne_zero]

/-- TS276 fills the linear-factor angular-average port of TS275. -/
noncomputable def linearFactorAngularAverageStatement
    (D : TS275.Goldbach.JensenFactorZeroData) :
    TS275.Goldbach.LinearFactorAngularAverageStatement D where
  intervalIntegrable := fun rho hRho =>
    linearFactor_angularIntervalIntegrable
      D.config.center rho D.config.averagingRadius
      D.config.averagingRadius_positive
      (D.factor_zero_mem_open_disk rho hRho)
  average_eq := fun rho hRho =>
    linearFactor_angularCircleAverage_eq
      D.config.center rho D.config.averagingRadius
      D.config.averagingRadius_positive
      (D.factor_zero_mem_open_disk rho hRho)

/-- Concrete ledger recording the completed TS276 port. -/
structure LinearFactorAngularAverageLedger where
  ts275_reduction :
    TS275.Goldbach.FiniteJensenPolynomialFactorizationReductionLedger

  linear_factor_statement :
    forall D : TS275.Goldbach.JensenFactorZeroData,
      TS275.Goldbach.LinearFactorAngularAverageStatement D

  nonvanishing_quotient_log_mean_not_proved : True
  buffered_factorization_not_constructed : True
  riemann_xi_not_defined : True
  zeta_counting_estimate_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

noncomputable def linearFactorAngularAverageLedger :
    LinearFactorAngularAverageLedger where
  ts275_reduction :=
    TS275.Goldbach.finiteJensenPolynomialFactorizationReductionLedger
  linear_factor_statement := linearFactorAngularAverageStatement
  nonvanishing_quotient_log_mean_not_proved := True.intro
  buffered_factorization_not_constructed := True.intro
  riemann_xi_not_defined := True.intro
  zeta_counting_estimate_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

def LinearFactorAngularAverageTarget : Prop :=
  Nonempty LinearFactorAngularAverageLedger

theorem linearFactorAngularAverageTarget :
    LinearFactorAngularAverageTarget :=
  Nonempty.intro linearFactorAngularAverageLedger

end Goldbach
end TS276
