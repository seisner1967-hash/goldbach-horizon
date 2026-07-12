import Mathlib.Tactic
import TS.Goldbach.Strong.TS276.LinearFactorAngularAverage

/-!
# TS277 - Nonvanishing Quotient Holomorphic Log Reduction

TS276 discharged the linear-factor angular average required by TS275.  This
sprint treats the remaining quotient port.  It proves unconditionally that
`log |g|` is angularly integrable for every buffered TS275 factorization.

For the exact mean-value identity, TS277 records a holomorphic logarithm `L`
on the buffered closed disk, with `exp (L z) = g z`.  Cauchy's formula gives
the complex angular mean of `L`; taking real parts and using
`log |exp w| = re w` gives the required logarithmic mean of `g`.

The locked Mathlib revision does not expose a theorem constructing this
holomorphic logarithm from analyticity and nonvanishing on a disk.  TS277
therefore names that construction as the next analytic statement instead of
hiding it behind a primitive declaration or a `True` slot.

No holomorphic-log construction, complete Jensen divisor theorem, concrete
Riemann xi function, zeta counting bound, explicit formula, Gallagher
estimate, OTSA bridge, or Goldbach statement is claimed.
-/

namespace TS277
namespace Goldbach

open MeasureTheory

/-- A buffered holomorphic logarithm of the quotient from TS275. -/
structure BufferedQuotientHolomorphicLogData
    (D : TS275.Goldbach.BufferedJensenFactorizationData) where
  logarithm : Complex -> Complex

  logarithm_analytic :
    AnalyticOnNhd Complex logarithm
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius)

  exp_logarithm_eq_g :
    forall z : Complex,
      Membership.mem
          (Metric.closedBall
            D.zeroData.config.center D.zeroData.config.analyticRadius) z ->
        Complex.exp (logarithm z) = D.g z

/-- The remaining construction statement after TS277. -/
def BufferedQuotientHolomorphicLogConstructionStatement : Prop :=
  forall D : TS275.Goldbach.BufferedJensenFactorizationData,
    Nonempty (BufferedQuotientHolomorphicLogData D)

/-- The TS275 angular parametrization is the Mathlib circle map. -/
theorem angularCirclePoint_eq_circleMap
    (center : Complex)
    (radius theta : Real) :
    TS275.Goldbach.angularCirclePoint center radius theta =
      circleMap center radius theta := by
  simp [TS275.Goldbach.angularCirclePoint, circleMap, mul_comm]

theorem angularCirclePoint_mem_analyticClosedBall
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (theta : Real) :
    Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius)
      (TS275.Goldbach.angularCirclePoint
        D.zeroData.config.center D.zeroData.config.averagingRadius theta) := by
  apply D.zeroData.config.averagingSphere_mem_analyticClosedBall
  exact TS275.Goldbach.angularCirclePoint_abs_sub_center
    D.zeroData.config.center D.zeroData.config.averagingRadius theta
    D.zeroData.config.averagingRadius_positive.le

theorem buffered_g_angular_continuous
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Continuous
      (fun theta : Real =>
        D.g
          (TS275.Goldbach.angularCirclePoint
            D.zeroData.config.center
            D.zeroData.config.averagingRadius theta)) := by
  rw [continuous_iff_continuousAt]
  intro theta
  have hPoint := (D.g_analytic _
    (angularCirclePoint_mem_analyticClosedBall D theta)).continuousAt
  have hParam :
      ContinuousAt
        (fun t : Real =>
          TS275.Goldbach.angularCirclePoint
            D.zeroData.config.center
            D.zeroData.config.averagingRadius t) theta := by
    unfold TS275.Goldbach.angularCirclePoint
    fun_prop
  exact hPoint.comp hParam

theorem buffered_g_angular_nonzero
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (theta : Real) :
    Not
      (D.g
        (TS275.Goldbach.angularCirclePoint
          D.zeroData.config.center
          D.zeroData.config.averagingRadius theta) = 0) :=
  D.g_nonzero _ (angularCirclePoint_mem_analyticClosedBall D theta)

theorem buffered_log_abs_g_angular_continuous
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Continuous
      (fun theta : Real =>
        Real.log
          (Complex.abs
            (D.g
              (TS275.Goldbach.angularCirclePoint
                D.zeroData.config.center
                D.zeroData.config.averagingRadius theta)))) := by
  rw [continuous_iff_continuousAt]
  intro theta
  have hG : ContinuousAt
      (fun t : Real =>
        D.g
          (TS275.Goldbach.angularCirclePoint
            D.zeroData.config.center
            D.zeroData.config.averagingRadius t)) theta :=
    (buffered_g_angular_continuous D).continuousAt
  have hLogAbs : ContinuousAt
      (fun z : Complex => Real.log (Complex.abs z))
      (D.g
        (TS275.Goldbach.angularCirclePoint
          D.zeroData.config.center
          D.zeroData.config.averagingRadius theta)) :=
    (Real.continuousAt_log
      (Complex.abs.ne_zero (buffered_g_angular_nonzero D theta))).comp
        Complex.continuous_abs.continuousAt
  have hComp : ContinuousAt
      (Function.comp
        (fun z : Complex => Real.log (Complex.abs z))
        (fun t : Real =>
          D.g
            (TS275.Goldbach.angularCirclePoint
              D.zeroData.config.center
              D.zeroData.config.averagingRadius t))) theta :=
    ContinuousAt.comp (f := fun t : Real =>
      D.g
        (TS275.Goldbach.angularCirclePoint
          D.zeroData.config.center
          D.zeroData.config.averagingRadius t)) hLogAbs hG
  simpa [Function.comp_apply] using hComp

/-- The integrability field of the TS275 quotient port is unconditional. -/
theorem buffered_log_abs_g_angularIntervalIntegrable
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS275.Goldbach.AngularIntervalIntegrable
      (fun z => Real.log (Complex.abs (D.g z)))
      D.zeroData.config.center D.zeroData.config.averagingRadius := by
  unfold TS275.Goldbach.AngularIntervalIntegrable
  exact (buffered_log_abs_g_angular_continuous D).intervalIntegrable
    0 (2 * Real.pi)

namespace BufferedQuotientHolomorphicLogData

theorem logarithm_continuousOn_averagingClosedBall
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    ContinuousOn H.logarithm
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.averagingRadius) := by
  intro z hz
  exact (H.logarithm_analytic z
    (D.zeroData.config.averagingClosedBall_subset_analyticClosedBall hz)).continuousAt.continuousWithinAt

theorem logarithm_differentiableAt_averagingBall
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.ball
        D.zeroData.config.center D.zeroData.config.averagingRadius) z) :
    DifferentiableAt Complex H.logarithm z := by
  have hzClosed : Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.averagingRadius) z :=
    Metric.ball_subset_closedBall hz
  exact (H.logarithm_analytic z
    (D.zeroData.config.averagingClosedBall_subset_analyticClosedBall hzClosed)).differentiableAt

theorem logarithm_angular_continuous
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    Continuous
      (fun theta : Real =>
        H.logarithm
          (circleMap D.zeroData.config.center
            D.zeroData.config.averagingRadius theta)) := by
  rw [continuous_iff_continuousAt]
  intro theta
  have hMem := circleMap_mem_closedBall
    D.zeroData.config.center
    D.zeroData.config.averagingRadius_positive.le theta
  have hAnalyticMem :=
    D.zeroData.config.averagingClosedBall_subset_analyticClosedBall hMem
  exact ((H.logarithm_analytic _ hAnalyticMem).continuousAt.comp
    (continuous_circleMap
      D.zeroData.config.center D.zeroData.config.averagingRadius).continuousAt)

theorem logarithm_angularIntervalIntegrable
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    IntervalIntegrable
      (fun theta : Real =>
        H.logarithm
          (circleMap D.zeroData.config.center
            D.zeroData.config.averagingRadius theta))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  H.logarithm_angular_continuous.intervalIntegrable 0 (2 * Real.pi)

end BufferedQuotientHolomorphicLogData

/-- General circle parametrization identity needed for Cauchy's formula. -/
theorem circleIntegral_sub_center_inv_mul_eq_I_mul_intervalIntegral
    (center : Complex)
    (radius : Real)
    (hRadius : 0 < radius)
    (f : Complex -> Complex) :
    circleIntegral
        (fun z : Complex => Inv.inv (z - center) * f z)
        center radius =
      Complex.I *
        intervalIntegral
          (fun theta : Real => f (circleMap center radius theta))
          0 (2 * Real.pi) MeasureTheory.volume := by
  have hRadiusComplex : Not ((radius : Complex) = 0) := by
    exact_mod_cast hRadius.ne'
  unfold circleIntegral
  calc
    intervalIntegral
        (fun theta : Real =>
          deriv (circleMap center radius) theta *
            (Inv.inv (circleMap center radius theta - center) *
              f (circleMap center radius theta)))
        0 (2 * Real.pi) MeasureTheory.volume =
      intervalIntegral
        (fun theta : Real =>
          Complex.I * f (circleMap center radius theta))
        0 (2 * Real.pi) MeasureTheory.volume := by
          apply intervalIntegral.integral_congr
          intro theta _
          change
            deriv (circleMap center radius) theta *
                (Inv.inv (circleMap center radius theta - center) *
                  f (circleMap center radius theta)) =
              Complex.I * f (circleMap center radius theta)
          rw [deriv_circleMap]
          simp only [circleMap, smul_eq_mul, zero_add, add_sub_cancel_left]
          field_simp [hRadiusComplex, Complex.exp_ne_zero]
          ring
    _ = Complex.I *
        intervalIntegral
          (fun theta : Real => f (circleMap center radius theta))
          0 (2 * Real.pi) MeasureTheory.volume := by
          exact intervalIntegral.integral_const_mul Complex.I _

theorem logarithm_circleIntegral_cauchy
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    circleIntegral
        (fun z : Complex =>
          Inv.inv (z - D.zeroData.config.center) * H.logarithm z)
        D.zeroData.config.center D.zeroData.config.averagingRadius =
      (2 * Real.pi * Complex.I) *
        H.logarithm D.zeroData.config.center := by
  have hCauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      (E := Complex)
      (R := D.zeroData.config.averagingRadius)
      (c := D.zeroData.config.center)
      (f := H.logarithm)
      (s := ({D.zeroData.config.center} : Set Complex))
      D.zeroData.config.averagingRadius_positive
      (Set.countable_singleton D.zeroData.config.center)
      H.logarithm_continuousOn_averagingClosedBall
      (fun z hz => H.logarithm_differentiableAt_averagingBall z hz.1)
  simpa [smul_eq_mul] using hCauchy

theorem logarithm_intervalIntegral_eq_center
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    intervalIntegral
        (fun theta : Real =>
          H.logarithm
            (circleMap D.zeroData.config.center
              D.zeroData.config.averagingRadius theta))
        0 (2 * Real.pi) MeasureTheory.volume =
      (2 * Real.pi : Complex) *
        H.logarithm D.zeroData.config.center := by
  have hCauchy := logarithm_circleIntegral_cauchy H
  rw [circleIntegral_sub_center_inv_mul_eq_I_mul_intervalIntegral
    D.zeroData.config.center D.zeroData.config.averagingRadius
    D.zeroData.config.averagingRadius_positive H.logarithm] at hCauchy
  let J := intervalIntegral
    (fun theta : Real =>
      H.logarithm
        (circleMap D.zeroData.config.center
          D.zeroData.config.averagingRadius theta))
    0 (2 * Real.pi) MeasureTheory.volume
  let V := (2 * Real.pi : Complex) *
    H.logarithm D.zeroData.config.center
  change J = V
  have hCauchy' : Complex.I * J = Complex.I * V := by
    calc
      Complex.I * J = (2 * Real.pi * Complex.I) *
          H.logarithm D.zeroData.config.center := hCauchy
      _ = Complex.I * V := by simp [V]; ring
  have hProduct : Complex.I * (J - V) = 0 := by
    rw [mul_sub, hCauchy', sub_self]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hProduct).resolve_left Complex.I_ne_zero)

theorem logarithm_normalizedAngularAverage_eq_center
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    (1 / (2 * Real.pi) : Complex) *
        intervalIntegral
          (fun theta : Real =>
            H.logarithm
              (circleMap D.zeroData.config.center
                D.zeroData.config.averagingRadius theta))
          0 (2 * Real.pi) MeasureTheory.volume =
      H.logarithm D.zeroData.config.center := by
  rw [logarithm_intervalIntegral_eq_center H]
  have hTwoPi : Not ((2 * Real.pi : Complex) = 0) := by
    have hTwoPiReal : Not ((2 * Real.pi : Real) = 0) :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    exact_mod_cast hTwoPiReal
  field_simp [hTwoPi]

theorem log_abs_g_eq_logarithm_re
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius) z) :
    Real.log (Complex.abs (D.g z)) = (H.logarithm z).re := by
  rw [<- H.exp_logarithm_eq_g z hz]
  rw [Complex.abs_exp, Real.log_exp]

theorem logarithm_re_intervalIntegral_eq
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    intervalIntegral
        (fun theta : Real =>
          (H.logarithm
            (circleMap D.zeroData.config.center
              D.zeroData.config.averagingRadius theta)).re)
        0 (2 * Real.pi) MeasureTheory.volume =
      (intervalIntegral
        (fun theta : Real =>
          H.logarithm
            (circleMap D.zeroData.config.center
              D.zeroData.config.averagingRadius theta))
        0 (2 * Real.pi) MeasureTheory.volume).re := by
  have hMap := Complex.reCLM.intervalIntegral_comp_comm
    H.logarithm_angularIntervalIntegrable
  simpa [Complex.reCLM_apply] using hMap

theorem quotientLog_angularCircleAverage_eq
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    TS275.Goldbach.angularCircleAverage
        (fun z => Real.log (Complex.abs (D.g z)))
        D.zeroData.config.center D.zeroData.config.averagingRadius =
      Real.log (Complex.abs (D.g D.zeroData.config.center)) := by
  have hCenterMem := D.center_mem_analyticClosedBall
  have hCenterLog := log_abs_g_eq_logarithm_re H _ hCenterMem
  have hComplexMean := logarithm_normalizedAngularAverage_eq_center H
  have hRealMean := congrArg Complex.re hComplexMean
  unfold TS275.Goldbach.angularCircleAverage
  rw [intervalIntegral.integral_congr
    (fun theta _ =>
      log_abs_g_eq_logarithm_re H _
        (angularCirclePoint_mem_analyticClosedBall D theta))]
  rw [intervalIntegral.integral_congr
    (fun theta _ => by
      rw [angularCirclePoint_eq_circleMap])]
  rw [logarithm_re_intervalIntegral_eq H]
  rw [hCenterLog]
  simpa [Complex.mul_re] using hRealMean

/-- Conditional constructor for the remaining TS275 quotient port. -/
noncomputable def nonvanishingQuotientAngularAverageStatement
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (H : BufferedQuotientHolomorphicLogData D) :
    TS275.Goldbach.NonvanishingQuotientAngularAverageStatement D where
  intervalIntegrable := buffered_log_abs_g_angularIntervalIntegrable D
  average_eq := quotientLog_angularCircleAverage_eq H

/-- Concrete TS277 ledger. -/
structure NonvanishingQuotientHolomorphicLogReductionLedger where
  ts276_linear_factor : TS276.Goldbach.LinearFactorAngularAverageLedger

  quotient_integrability :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      TS275.Goldbach.AngularIntervalIntegrable
        (fun z => Real.log (Complex.abs (D.g z)))
        D.zeroData.config.center D.zeroData.config.averagingRadius

  conditional_constructor :
    forall (D : TS275.Goldbach.BufferedJensenFactorizationData),
      BufferedQuotientHolomorphicLogData D ->
        TS275.Goldbach.NonvanishingQuotientAngularAverageStatement D

  holomorphic_log_construction_open :
    BufferedQuotientHolomorphicLogConstructionStatement ->
      forall D : TS275.Goldbach.BufferedJensenFactorizationData,
        TS275.Goldbach.NonvanishingQuotientAngularAverageStatement D

  buffered_factorization_not_constructed : True
  riemann_xi_not_defined : True
  zeta_counting_estimate_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

noncomputable def nonvanishingQuotientHolomorphicLogReductionLedger :
    NonvanishingQuotientHolomorphicLogReductionLedger where
  ts276_linear_factor := TS276.Goldbach.linearFactorAngularAverageLedger
  quotient_integrability := buffered_log_abs_g_angularIntervalIntegrable
  conditional_constructor := fun _ H =>
    nonvanishingQuotientAngularAverageStatement H
  holomorphic_log_construction_open := fun hConstruction D =>
    nonvanishingQuotientAngularAverageStatement
      (Classical.choice (hConstruction D))
  buffered_factorization_not_constructed := True.intro
  riemann_xi_not_defined := True.intro
  zeta_counting_estimate_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

def NonvanishingQuotientHolomorphicLogReductionTarget : Prop :=
  Nonempty NonvanishingQuotientHolomorphicLogReductionLedger

theorem nonvanishingQuotientHolomorphicLogReductionTarget :
    NonvanishingQuotientHolomorphicLogReductionTarget :=
  Nonempty.intro nonvanishingQuotientHolomorphicLogReductionLedger

end Goldbach
end TS277
