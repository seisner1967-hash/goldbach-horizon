import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.Calculus.MeanValue
import TS.Goldbach.Strong.TS278.HolomorphicPrimitiveOnBallBackport

/-!
# TS279 - Buffered Quotient Holomorphic Log Construction

TS277 reduced the nonvanishing quotient mean-value theorem to the existence
of a holomorphic logarithm on the buffered closed disk.  TS278 supplied the
missing primitive theorem on an open ball.  This sprint closes that gap.

For each buffered TS275 factorization, analyticity and nonvanishing hold on a
neighborhood of every point of the compact analytic closed disk.  A uniform
metric thickening therefore gives a larger concentric open ball on which both
properties hold.  TS278 is applied there to `deriv g / g`.

If `P' = g' / g`, then `g * exp (-P)` has derivative zero and is constant on
the enlarged ball.  The normalized function

`P z - P center + Complex.log (g center)`

is consequently a holomorphic logarithm of `g`.  Notice that its center value
is `Complex.log (g center)`, not zero unless `g center = 1`.

No concrete buffered factorization, Riemann xi function, effective zeta
count, explicit formula, Gallagher estimate, OTSA bridge, or Goldbach theorem
is supplied.
-/

noncomputable section

namespace TS279
namespace Goldbach

open Complex Metric Set Topology

/-- Points where the buffered quotient is both analytic and nonzero. -/
def bufferedAnalyticNonzeroSet
    (D : TS275.Goldbach.BufferedJensenFactorizationData) : Set Complex :=
  {z : Complex |
    And (AnalyticAt Complex D.g z) (Not (D.g z = 0))}

theorem bufferedAnalyticNonzeroSet_isOpen
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    IsOpen (bufferedAnalyticNonzeroSet D) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  change Filter.Eventually
    (fun w : Complex =>
      And (AnalyticAt Complex D.g w) (Not (D.g w = 0))) (nhds z)
  exact Filter.Eventually.and
    hz.1.eventually_analyticAt
    (hz.1.continuousAt.eventually_ne hz.2)

theorem analyticClosedBall_subset_bufferedAnalyticNonzeroSet
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius <=
      bufferedAnalyticNonzeroSet D := by
  intro z hz
  exact And.intro (D.g_analytic z hz) (D.g_nonzero z hz)

/-- A concentric open ball strictly larger than the TS275 analytic disk. -/
structure BufferedAnalyticNonzeroNeighborhoodData
    (D : TS275.Goldbach.BufferedJensenFactorizationData) where
  extendedRadius : Real

  analyticRadius_lt_extendedRadius :
    D.zeroData.config.analyticRadius < extendedRadius

  g_analytic :
    AnalyticOnNhd Complex D.g
      (Metric.ball D.zeroData.config.center extendedRadius)

  g_nonzero :
    forall z : Complex,
      Membership.mem
          (Metric.ball D.zeroData.config.center extendedRadius) z ->
        Not (D.g z = 0)

theorem bufferedAnalyticNonzeroNeighborhoodData_exists
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Nonempty (BufferedAnalyticNonzeroNeighborhoodData D) := by
  have hCompact := isCompact_closedBall
    D.zeroData.config.center D.zeroData.config.analyticRadius
  have hExists := hCompact.exists_thickening_subset_open
    (bufferedAnalyticNonzeroSet_isOpen D)
    (analyticClosedBall_subset_bufferedAnalyticNonzeroSet D)
  let delta : Real := Classical.choose hExists
  have hDelta : 0 < delta := (Classical.choose_spec hExists).1
  have hThickening := (Classical.choose_spec hExists).2
  have hRadiusNonnegative : 0 <= D.zeroData.config.analyticRadius :=
    D.zeroData.config.analyticRadius_positive.le
  have hBallSubset :
      Metric.ball D.zeroData.config.center
          (delta + D.zeroData.config.analyticRadius) <=
        bufferedAnalyticNonzeroSet D := by
    rw [<- thickening_closedBall hDelta hRadiusNonnegative]
    exact hThickening
  refine Nonempty.intro
    { extendedRadius := delta + D.zeroData.config.analyticRadius
      analyticRadius_lt_extendedRadius := by linarith
      g_analytic := fun z hz => (hBallSubset hz).1
      g_nonzero := fun z hz => (hBallSubset hz).2 }

namespace BufferedAnalyticNonzeroNeighborhoodData

theorem extendedRadius_positive
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    0 < N.extendedRadius :=
  D.zeroData.config.analyticRadius_positive.trans
    N.analyticRadius_lt_extendedRadius

theorem analyticClosedBall_subset_extendedBall
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius <=
      Metric.ball D.zeroData.config.center N.extendedRadius :=
  Metric.closedBall_subset_ball N.analyticRadius_lt_extendedRadius

end BufferedAnalyticNonzeroNeighborhoodData

/-- The logarithmic derivative to which TS278 is applied. -/
def bufferedLogarithmicDerivative
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    Complex -> Complex :=
  fun z : Complex => deriv D.g z / D.g z

theorem bufferedLogarithmicDerivative_analytic
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    AnalyticOnNhd Complex (bufferedLogarithmicDerivative D)
      (Metric.ball D.zeroData.config.center N.extendedRadius) := by
  exact N.g_analytic.deriv.div N.g_analytic N.g_nonzero

theorem bufferedLogarithmicDerivative_differentiable
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    DifferentiableOn Complex (bufferedLogarithmicDerivative D)
      (Metric.ball D.zeroData.config.center N.extendedRadius) :=
  (bufferedLogarithmicDerivative_analytic N).differentiableOn

/-- The TS278 wedge primitive of the logarithmic derivative. -/
def bufferedLogarithmicPrimitive
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) : Complex -> Complex :=
  Classical.choose
    (TS278.Goldbach.differentiableOn_holomorphicExactOn_ball
      (bufferedLogarithmicDerivative_differentiable N))

theorem bufferedLogarithmicPrimitive_hasDerivAt
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.ball D.zeroData.config.center N.extendedRadius) z) :
    HasDerivAt (bufferedLogarithmicPrimitive N)
      (bufferedLogarithmicDerivative D z) z :=
  Classical.choose_spec
    (TS278.Goldbach.differentiableOn_holomorphicExactOn_ball
      (bufferedLogarithmicDerivative_differentiable N)) z hz

theorem bufferedLogarithmicPrimitive_differentiable
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    DifferentiableOn Complex (bufferedLogarithmicPrimitive N)
      (Metric.ball D.zeroData.config.center N.extendedRadius) := by
  intro z hz
  exact (bufferedLogarithmicPrimitive_hasDerivAt N z hz).differentiableAt.differentiableWithinAt

/-- The quotient remaining after exponentiating the negative primitive. -/
def primitiveCorrectedQuotient
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) : Complex -> Complex :=
  fun z : Complex =>
    D.g z * Complex.exp (-(bufferedLogarithmicPrimitive N z))

theorem primitiveCorrectedQuotient_hasDerivAt_zero
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.ball D.zeroData.config.center N.extendedRadius) z) :
    HasDerivAt (primitiveCorrectedQuotient N) 0 z := by
  have hG : HasDerivAt D.g (deriv D.g z) z :=
    (N.g_analytic z hz).differentiableAt.hasDerivAt
  have hP := bufferedLogarithmicPrimitive_hasDerivAt N z hz
  have hExp := hP.neg.cexp
  have hProduct := hG.mul hExp
  apply hProduct.congr_deriv
  unfold bufferedLogarithmicDerivative
  have hGNonzero := N.g_nonzero z hz
  field_simp
  ring

theorem primitiveCorrectedQuotient_differentiable
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    DifferentiableOn Complex (primitiveCorrectedQuotient N)
      (Metric.ball D.zeroData.config.center N.extendedRadius) := by
  intro z hz
  exact (primitiveCorrectedQuotient_hasDerivAt_zero N z hz).differentiableAt.differentiableWithinAt

theorem primitiveCorrectedQuotient_fderivWithin_eq_zero
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.ball D.zeroData.config.center N.extendedRadius) z) :
    fderivWithin Complex (primitiveCorrectedQuotient N)
      (Metric.ball D.zeroData.config.center N.extendedRadius) z = 0 := by
  rw [fderivWithin_of_isOpen isOpen_ball hz]
  have hFDeriv :=
    (primitiveCorrectedQuotient_hasDerivAt_zero N z hz).hasFDerivAt.fderiv
  calc
    fderiv Complex (primitiveCorrectedQuotient N) z =
        ContinuousLinearMap.smulRight 1 0 := hFDeriv
    _ = 0 := by
      ext
      simp

theorem primitiveCorrectedQuotient_eq_center
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.ball D.zeroData.config.center N.extendedRadius) z) :
    primitiveCorrectedQuotient N z =
      primitiveCorrectedQuotient N D.zeroData.config.center := by
  exact Convex.is_const_of_fderivWithin_eq_zero
      (convex_ball D.zeroData.config.center N.extendedRadius)
      (primitiveCorrectedQuotient_differentiable N)
      (primitiveCorrectedQuotient_fderivWithin_eq_zero N)
      hz (Metric.mem_ball_self N.extendedRadius_positive)

/-- The normalized logarithm produced from the TS278 primitive. -/
def bufferedQuotientHolomorphicLogarithm
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) : Complex -> Complex :=
  fun z : Complex =>
    bufferedLogarithmicPrimitive N z -
      bufferedLogarithmicPrimitive N D.zeroData.config.center +
      Complex.log (D.g D.zeroData.config.center)

theorem bufferedQuotientHolomorphicLogarithm_analytic
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D) :
    AnalyticOnNhd Complex (bufferedQuotientHolomorphicLogarithm N)
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius) := by
  have hDifferentiable : DifferentiableOn Complex
      (bufferedQuotientHolomorphicLogarithm N)
      (Metric.ball D.zeroData.config.center N.extendedRadius) := by
    unfold bufferedQuotientHolomorphicLogarithm
    exact
      ((bufferedLogarithmicPrimitive_differentiable N).sub_const _).add_const _
  exact (hDifferentiable.analyticOnNhd isOpen_ball).mono
    N.analyticClosedBall_subset_extendedBall

theorem bufferedQuotientHolomorphicLogarithm_exp_eq_g
    {D : TS275.Goldbach.BufferedJensenFactorizationData}
    (N : BufferedAnalyticNonzeroNeighborhoodData D)
    (z : Complex)
    (hz : Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius) z) :
    Complex.exp (bufferedQuotientHolomorphicLogarithm N z) = D.g z := by
  have hzExtended := N.analyticClosedBall_subset_extendedBall hz
  have hConstant := primitiveCorrectedQuotient_eq_center N z hzExtended
  have hCenterClosed : Membership.mem
      (Metric.closedBall
        D.zeroData.config.center D.zeroData.config.analyticRadius)
      D.zeroData.config.center := by
    simp [D.zeroData.config.analyticRadius_positive.le]
  have hCenterNonzero := D.g_nonzero D.zeroData.config.center hCenterClosed
  have hTransport := congrArg
    (fun q : Complex =>
      q * Complex.exp (bufferedLogarithmicPrimitive N z)) hConstant
  have hNormalized :
      Complex.exp
          (bufferedLogarithmicPrimitive N z -
            bufferedLogarithmicPrimitive N D.zeroData.config.center) *
        D.g D.zeroData.config.center = D.g z := by
    simpa [primitiveCorrectedQuotient, Complex.exp_sub,
      Complex.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hTransport.symm
  unfold bufferedQuotientHolomorphicLogarithm
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log hCenterNonzero]
  simpa [Complex.exp_sub, div_eq_mul_inv] using hNormalized

/-- TS279 constructs the exact logarithm data demanded by TS277. -/
noncomputable def bufferedQuotientHolomorphicLogData
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS277.Goldbach.BufferedQuotientHolomorphicLogData D := by
  let N : BufferedAnalyticNonzeroNeighborhoodData D :=
    Classical.choice (bufferedAnalyticNonzeroNeighborhoodData_exists D)
  exact
    { logarithm := bufferedQuotientHolomorphicLogarithm N
      logarithm_analytic := bufferedQuotientHolomorphicLogarithm_analytic N
      exp_logarithm_eq_g :=
        bufferedQuotientHolomorphicLogarithm_exp_eq_g N }

theorem bufferedQuotientHolomorphicLogConstructionStatement :
    TS277.Goldbach.BufferedQuotientHolomorphicLogConstructionStatement := by
  intro D
  exact Nonempty.intro (bufferedQuotientHolomorphicLogData D)

theorem nonvanishingQuotientAngularAverageStatement
    (D : TS275.Goldbach.BufferedJensenFactorizationData) :
    TS275.Goldbach.NonvanishingQuotientAngularAverageStatement D :=
  TS277.Goldbach.nonvanishingQuotientAngularAverageStatement
    (bufferedQuotientHolomorphicLogData D)

/-- After TS276 and TS279, only the circle norm bound remains for TS274. -/
theorem finiteJensenBoundaryEstimate_of_boundaryNorm
    (D : TS275.Goldbach.BufferedJensenFactorizationData)
    (M : Real)
    (HBoundary :
      TS275.Goldbach.BoundaryNormOnAveragingSphereStatement D M) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData D.f M :=
  TS275.Goldbach.finiteJensenBoundaryEstimate_of_factorization_and_angularMeans
    D M
    (TS276.Goldbach.linearFactorAngularAverageStatement D.zeroData)
    (nonvanishingQuotientAngularAverageStatement D)
    HBoundary

structure BufferedQuotientHolomorphicLogConstructionLedger where
  ts278_primitive :
    TS278.Goldbach.HolomorphicPrimitiveOnBallBackportLedger

  uniform_buffered_neighborhood_constructed :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      Nonempty (BufferedAnalyticNonzeroNeighborhoodData D)

  buffered_logarithm_constructed :
    TS277.Goldbach.BufferedQuotientHolomorphicLogConstructionStatement

  quotient_angular_average_proved :
    forall D : TS275.Goldbach.BufferedJensenFactorizationData,
      TS275.Goldbach.NonvanishingQuotientAngularAverageStatement D

  finite_jensen_reduced_to_boundary_norm :
    forall (D : TS275.Goldbach.BufferedJensenFactorizationData) (M : Real),
      TS275.Goldbach.BoundaryNormOnAveragingSphereStatement D M ->
        TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
          D.zeroData.toJensenInnerZeroData.toFiniteJensenDiskData D.f M

  concrete_buffered_factorization_not_constructed : True
  finite_jensen_boundary_norm_bound_not_proved : True
  concrete_riemann_xi_not_defined : True
  zero_counting_bound_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def bufferedQuotientHolomorphicLogConstructionLedger :
    BufferedQuotientHolomorphicLogConstructionLedger where
  ts278_primitive := TS278.Goldbach.holomorphicPrimitiveOnBallBackportLedger
  uniform_buffered_neighborhood_constructed :=
    bufferedAnalyticNonzeroNeighborhoodData_exists
  buffered_logarithm_constructed :=
    bufferedQuotientHolomorphicLogConstructionStatement
  quotient_angular_average_proved :=
    nonvanishingQuotientAngularAverageStatement
  finite_jensen_reduced_to_boundary_norm :=
    finiteJensenBoundaryEstimate_of_boundaryNorm
  concrete_buffered_factorization_not_constructed := True.intro
  finite_jensen_boundary_norm_bound_not_proved := True.intro
  concrete_riemann_xi_not_defined := True.intro
  zero_counting_bound_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def BufferedQuotientHolomorphicLogConstructionTarget : Prop :=
  Nonempty BufferedQuotientHolomorphicLogConstructionLedger

theorem bufferedQuotientHolomorphicLogConstructionTarget :
    BufferedQuotientHolomorphicLogConstructionTarget :=
  Nonempty.intro bufferedQuotientHolomorphicLogConstructionLedger

end Goldbach
end TS279
