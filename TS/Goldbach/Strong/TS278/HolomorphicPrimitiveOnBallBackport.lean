import Mathlib.Tactic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import TS.Goldbach.Strong.TS277.NonvanishingQuotientHolomorphicLogReduction

/-!
# TS278 - Holomorphic Primitive on a Ball Backport

The locked Mathlib revision contains Cauchy-Goursat on rectangles but does not
yet expose the later `HasPrimitives` layer.  This sprint backports the part
needed by TS277: every complex-differentiable function on an open ball has a
primitive there.

The primitive is the integral along the axis-parallel wedge from the center to
the endpoint.  Rectangle Cauchy-Goursat makes nearby wedge differences local,
and the real and imaginary interval-integral derivatives give the complex
derivative.

This module proves a primitive only on an open ball.  It does not extend local
analyticity or nonvanishing uniformly beyond a closed ball, construct the
TS277 logarithm, instantiate Riemann xi, prove a zeta counting estimate, or
claim the explicit formula, Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS278
namespace Goldbach

open Complex MeasureTheory Metric Set Topology

/-- The horizontal-then-vertical integral from `z` to `w`. -/
def holomorphicWedgeIntegral
    (z w : Complex)
    (f : Complex -> Complex) : Complex :=
  intervalIntegral
      (fun x : Real => f (x + z.im * Complex.I)) z.re w.re volume +
    Complex.I *
      (intervalIntegral
        (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume)

theorem holomorphicWedgeIntegral_add_reverse
    (z w : Complex)
    (f : Complex -> Complex) :
    holomorphicWedgeIntegral z w f +
        holomorphicWedgeIntegral w z f =
      intervalIntegral
          (fun x : Real => f (x + z.im * Complex.I)) z.re w.re volume -
        intervalIntegral
          (fun x : Real => f (x + w.im * Complex.I)) z.re w.re volume +
        Complex.I *
          (intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume) -
        Complex.I *
          (intervalIntegral
            (fun y : Real => f (z.re + y * Complex.I)) z.im w.im volume) := by
  simp [holomorphicWedgeIntegral,
    intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg,
    mul_comm]
  abel

/-- Rectangle conservativity, stated using the local wedge integral. -/
def HolomorphicConservativeOn
  (f : Complex -> Complex)
  (U : Set Complex) : Prop :=
  forall z w : Complex,
    Complex.Rectangle z w <= U ->
      holomorphicWedgeIntegral z w f =
        -holomorphicWedgeIntegral w z f

/-- Existence of a complex primitive on a set. -/
def HolomorphicExactOn
    (f : Complex -> Complex)
    (U : Set Complex) : Prop :=
  exists F : Complex -> Complex,
    forall z : Complex,
      Membership.mem U z -> HasDerivAt F (f z) z

theorem differentiableOn_holomorphicConservativeOn
    {f : Complex -> Complex}
    {U : Set Complex}
    (hf : DifferentiableOn Complex f U) :
    HolomorphicConservativeOn f U := by
  intro z w hzw
  rw [<- add_eq_zero_iff_eq_neg, holomorphicWedgeIntegral_add_reverse]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f z w (hf.mono hzw)

section Geometry

variable {c z w : Complex} {r x y : Real}

theorem re_add_center_im_mem_ball
    (hz : Membership.mem (Metric.ball c r) z) :
    Membership.mem (Metric.ball c r) (z.re + c.im * Complex.I) := by
  suffices
      dist (z.re + c.im * Complex.I) c <= dist z c by
    exact lt_of_le_of_lt this hz
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im,
    Real.le_sqrt (by positivity) (by positivity),
    Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]

theorem horizontal_point_mem_ball
    (hx : Membership.mem
      (Set.Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) x) :
    Membership.mem (Metric.ball c r) (x + z.im * Complex.I) := by
  let localRadius := r - dist z c
  have hx' : norm (x - z.re : Real) < localRadius := by
    rw [Real.norm_eq_abs, abs_lt]
    dsimp [localRadius]
    constructor <;> nlinarith [hx.1, hx.2]
  have hLocal : dist (x + z.im * Complex.I) z < localRadius := by
    simpa [Complex.dist_eq_re_im, Real.sqrt_sq_eq_abs,
      Real.norm_eq_abs] using hx'
  exact mem_of_subset_of_mem
    (Metric.ball_subset_ball' (by simp [localRadius])) hLocal

theorem vertical_point_mem_closedBall
    (hz : Membership.mem (Metric.closedBall c r) z)
    (hy : Membership.mem (Set.uIoc c.im z.im) y) :
    Membership.mem (Metric.closedBall c r) (z.re + y * Complex.I) := by
  refine le_trans ?_ (Metric.mem_closedBall.mp hz)
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im,
    Real.le_sqrt (by positivity) (by positivity),
    Real.sq_sqrt (by positivity)]
  suffices (y - c.im) ^ 2 <= (z.im - c.im) ^ 2 by
    simpa
  cases Set.mem_uIoc.mp hy <;> nlinarith

theorem horizontal_segment_mem_ball
    {a1 a2 b : Real}
    (ha1 : Membership.mem (Metric.ball c r) (a1 + b * Complex.I))
    (ha2 : Membership.mem (Metric.ball c r) (a2 + b * Complex.I)) :
    Set.MapsTo
      (fun t : Real => t + b * Complex.I)
      (Set.uIcc a1 a2) (Metric.ball c r) := by
  intro t ht
  apply (convex_ball c r).segment_subset ha1 ha2
  have htSegment : Membership.mem (segment Real a1 a2) t := by
    simpa [segment_eq_uIcc] using ht
  rw [segment_eq_image'] at htSegment
  let u : Real := Classical.choose htSegment
  have hu : Membership.mem (Set.Icc (0 : Real) 1) u :=
    (Classical.choose_spec htSegment).1
  have htu : a1 + u * (a2 - a1) = t :=
    (Classical.choose_spec htSegment).2
  rw [segment_eq_image']
  refine Exists.intro u (And.intro hu ?_)
  rw [<- htu]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem vertical_segment_mem_ball
    {a b1 b2 : Real}
    (hb1 : Membership.mem (Metric.ball c r) (a + b1 * Complex.I))
    (hb2 : Membership.mem (Metric.ball c r) (a + b2 * Complex.I)) :
    Set.MapsTo
      (fun t : Real => a + t * Complex.I)
      (Set.uIcc b1 b2) (Metric.ball c r) := by
  intro t ht
  apply (convex_ball c r).segment_subset hb1 hb2
  have htSegment : Membership.mem (segment Real b1 b2) t := by
    simpa [segment_eq_uIcc] using ht
  rw [segment_eq_image'] at htSegment
  let u : Real := Classical.choose htSegment
  have hu : Membership.mem (Set.Icc (0 : Real) 1) u :=
    (Classical.choose_spec htSegment).1
  have htu : b1 + u * (b2 - b1) = t :=
    (Classical.choose_spec htSegment).2
  rw [segment_eq_image']
  refine Exists.intro u (And.intro hu ?_)
  rw [<- htu]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem nearby_vertical_segment_mem_ball
    (hw : Membership.mem (Metric.ball z (r - dist z c)) w) :
    Set.MapsTo
      (fun t : Real => w.re + t * Complex.I)
      (Set.uIcc z.im w.im) (Metric.ball c r) := by
  have hFirst : Membership.mem (Metric.ball c r)
      (w.re + z.im * Complex.I) := by
    apply mem_of_subset_of_mem
      (Metric.ball_subset_ball' (by simp) :
        Metric.ball z (r - dist z c) <= Metric.ball c r)
    exact re_add_center_im_mem_ball hw
  have hSecond : Membership.mem (Metric.ball c r)
      (w.re + w.im * Complex.I) := by
    apply mem_of_subset_of_mem
      (Metric.ball_subset_ball' (by simp) :
        Metric.ball z (r - dist z c) <= Metric.ball c r)
    simpa using hw
  exact vertical_segment_mem_ball hFirst hSecond

end Geometry

section LocalDerivative

variable {c z : Complex} {r : Real} {f : Complex -> Complex}

theorem conservative_eventually_wedge_difference
    (hContinuous : ContinuousOn f (Metric.ball c r))
    (hz : Membership.mem (Metric.ball c r) z)
    (hConservative : HolomorphicConservativeOn f (Metric.ball c r)) :
    Filter.EventuallyEq (nhds z)
      (fun w : Complex =>
        holomorphicWedgeIntegral c w f - holomorphicWedgeIntegral c z f)
      (fun w : Complex => holomorphicWedgeIntegral z w f) := by
  apply Metric.eventually_nhds_iff_ball.mpr
  refine Exists.intro (r - dist z c) ?_
  refine And.intro (by simpa using hz) ?_
  intro w hw
  let i1 := intervalIntegral
    (fun x : Real => f (x + c.im * Complex.I)) c.re w.re volume
  let i2 := Complex.I * (intervalIntegral
    (fun y : Real => f (w.re + y * Complex.I)) c.im w.im volume)
  let i3 := intervalIntegral
    (fun x : Real => f (x + c.im * Complex.I)) c.re z.re volume
  let i4 := Complex.I * (intervalIntegral
    (fun y : Real => f (z.re + y * Complex.I)) c.im z.im volume)
  let i5 := intervalIntegral
    (fun x : Real => f (x + z.im * Complex.I)) z.re w.re volume
  let i6 := Complex.I * (intervalIntegral
    (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume)
  let i7 := intervalIntegral
    (fun x : Real => f (x + c.im * Complex.I)) z.re w.re volume
  let i8 := Complex.I * (intervalIntegral
    (fun y : Real => f (w.re + y * Complex.I)) c.im z.im volume)
  have hBall : Metric.ball z (r - dist z c) <= Metric.ball c r :=
    Metric.ball_subset_ball' (by simp)
  have hwc : Membership.mem (Metric.ball c r) w :=
    mem_of_subset_of_mem hBall hw
  have hHorizontal : forall a1 a2 b : Real,
      Membership.mem (Metric.ball c r) (a1 + b * Complex.I) ->
      Membership.mem (Metric.ball c r) (a2 + b * Complex.I) ->
      IntervalIntegrable
        (fun x : Real => f (x + b * Complex.I)) volume a1 a2 := by
    intro a1 a2 b ha1 ha2
    exact ((hContinuous.mono
        (horizontal_segment_mem_ball ha1 ha2).image_subset).comp
      (by fun_prop) (Set.mapsTo_image _ _)).intervalIntegrable
  have hVertical : forall a b1 b2 : Real,
      Membership.mem (Metric.ball c r) (a + b1 * Complex.I) ->
      Membership.mem (Metric.ball c r) (a + b2 * Complex.I) ->
      IntervalIntegrable
        (fun y : Real => f (a + y * Complex.I)) volume b1 b2 := by
    intro a b1 b2 hb1 hb2
    exact ((hContinuous.mono
        (vertical_segment_mem_ball hb1 hb2).image_subset).comp
      (by fun_prop) (Set.mapsTo_image _ _)).intervalIntegrable
  have hi1 : i1 = i3 + i7 := by
    have hLeft := hHorizontal c.re z.re c.im
      (re_add_center_im_mem_ball
        (Metric.mem_ball_self (pos_of_mem_ball hz)))
      (re_add_center_im_mem_ball hz)
    have hRight := hHorizontal z.re w.re c.im
      (re_add_center_im_mem_ball hz)
      (re_add_center_im_mem_ball hwc)
    exact (intervalIntegral.integral_add_adjacent_intervals hLeft hRight).symm
  have hi2 : i2 = i8 + i6 := by
    dsimp [i2, i8, i6]
    change Complex.I *
        intervalIntegral
          (fun y : Real => f (w.re + y * Complex.I)) c.im w.im volume =
      Complex.I *
          intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) c.im z.im volume +
        Complex.I *
          intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume
    have hLower := hVertical w.re c.im z.im
      (re_add_center_im_mem_ball hwc)
      (mem_of_subset_of_mem hBall (re_add_center_im_mem_ball hw))
    have hUpper := hVertical w.re z.im w.im
      (mem_of_subset_of_mem hBall (re_add_center_im_mem_ball hw))
      (by simpa using hwc)
    rw [<- mul_add]
    exact congrArg (fun q : Complex => Complex.I * q)
      (intervalIntegral.integral_add_adjacent_intervals hLower hUpper).symm
  have hi0 : i7 - i5 + i8 - i4 = 0 := by
    have hwz : Membership.mem (Metric.ball c r)
        (w.re + z.im * Complex.I) :=
      mem_of_subset_of_mem hBall (re_add_center_im_mem_ball hw)
    have hwcim : Membership.mem (Metric.ball c r)
        (w.re + c.im * Complex.I) := re_add_center_im_mem_ball hwc
    have hRectangle :
        Complex.Rectangle
          (z.re + c.im * Complex.I) (w.re + z.im * Complex.I)
        <= Metric.ball c r := by
      intro q hq
      rw [Complex.Rectangle, Complex.mem_reProdIm] at hq
      have hqRe : Membership.mem (Set.uIcc z.re w.re) q.re := by
        simpa using hq.1
      have hqIm : Membership.mem (Set.uIcc c.im z.im) q.im := by
        simpa using hq.2
      have hHorizontalPoint : Membership.mem (Metric.ball c r)
          (q.re + c.im * Complex.I) :=
        horizontal_segment_mem_ball
          (re_add_center_im_mem_ball hz) hwcim hqRe
      have hTopPoint : Membership.mem (Metric.ball c r)
          (q.re + z.im * Complex.I) :=
        horizontal_segment_mem_ball (by simpa using hz) hwz hqRe
      have hVerticalPoint : Membership.mem (Metric.ball c r)
          (q.re + q.im * Complex.I) :=
        vertical_segment_mem_ball hHorizontalPoint hTopPoint hqIm
      simpa using hVerticalPoint
    simpa [<- add_eq_zero_iff_eq_neg,
      holomorphicWedgeIntegral_add_reverse] using
      hConservative (z.re + c.im * Complex.I)
        (w.re + z.im * Complex.I) hRectangle
  change i1 + i2 - (i3 + i4) = i5 + i6
  rw [hi1, hi2]
  linear_combination hi0

theorem horizontal_wedge_error_isLittleO
    (hContinuous : ContinuousOn f (Metric.ball c r))
    (hz : Membership.mem (Metric.ball c r) z) :
    Asymptotics.IsLittleO (nhds z)
      (fun w : Complex =>
        intervalIntegral
            (fun x : Real => f (x + z.im * Complex.I)) z.re w.re volume -
          ((w - z).re : Complex) * f z)
      (fun w : Complex => w - z) := by
  have hReal : Asymptotics.IsLittleO (nhds z.re)
      (fun x : Real =>
        intervalIntegral
            (fun t : Real => f (t + z.im * Complex.I)) z.re x volume -
          ((x - z.re : Real) : Complex) * f z)
      (fun x : Real => x - z.re) := by
    let localRadius := r - dist z c
    have hRadius : 0 < localRadius := by
      simpa only [Metric.mem_ball, sub_pos, localRadius] using hz
    let s : Set Real := Set.Ioo (z.re - localRadius) (z.re + localRadius)
    have hzre : Membership.mem s z.re := by simp [s, hRadius]
    have hCont : ContinuousOn
        (fun x : Real => f (x + z.im * Complex.I)) s :=
      hContinuous.comp
        (continuous_ofReal.add
          (continuous_const.mul continuous_const)).continuousOn
        (fun _ hx => horizontal_point_mem_ball hx)
    have hInt1 : IntervalIntegrable
        (fun x : Real => f (x + z.im * Complex.I)) volume z.re z.re :=
      ContinuousOn.intervalIntegrable (hCont.mono (by simpa))
    have hInt2 : StronglyMeasurableAtFilter
        (fun x : Real => f (x + z.im * Complex.I)) (nhds z.re) :=
      hCont.stronglyMeasurableAtFilter isOpen_Ioo _ hzre
    have hInt3 : ContinuousAt
        (fun x : Real => f (x + z.im * Complex.I)) z.re :=
      isOpen_Ioo.continuousOn_iff.mp hCont hzre
    simpa using
      (intervalIntegral.integral_hasDerivAt_right hInt1 hInt2 hInt3).isLittleO
  have hReBound : Asymptotics.IsBigO (nhds z)
      (fun w : Complex => w.re - z.re)
      (fun w : Complex => w - z) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with w
    simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs (w - z)
  exact (hReal.comp_tendsto (continuous_re.tendsto z)).trans_isBigO hReBound

theorem vertical_wedge_error_isLittleO
    (hContinuous : ContinuousOn f (Metric.ball c r))
    (hz : Membership.mem (Metric.ball c r) z) :
    Asymptotics.IsLittleO (nhds z)
      (fun w : Complex =>
        intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume -
          ((w - z).im : Complex) * f z)
      (fun w : Complex => w - z) := by
  have hReduced : Asymptotics.IsLittleO (nhds z)
      (fun w : Complex => intervalIntegral
        (fun y : Real => f (w.re + y * Complex.I) - f z)
        z.im w.im volume)
      (fun w : Complex => w - z) := by
    have hPoint : Asymptotics.IsLittleO (nhds z)
        (fun w : Complex => f w - f z)
        (fun _ : Complex => (1 : Real)) := by
      rw [Asymptotics.isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
      exact hContinuous.continuousAt
        (_root_.mem_nhds_iff.mpr
          (Exists.intro (Metric.ball c r)
            (And.intro (le_refl _) (And.intro isOpen_ball hz))))
    rw [Asymptotics.IsLittleO] at hPoint
    rw [Asymptotics.IsLittleO]
    intro epsilon hEpsilon
    have hPoint' := hPoint hEpsilon
    simp only [Asymptotics.isBigOWith_iff, norm_one, mul_one] at hPoint'
    simp only [Asymptotics.isBigOWith_iff]
    have hUniform : Filter.Eventually (fun w : Complex =>
        forall y : Real,
          Membership.mem (Set.uIoc z.im w.im) y ->
          norm (f (w.re + y * Complex.I) - f z) <= epsilon)
        (nhds z) := by
      rw [Metric.nhds_basis_closedBall.eventually_iff] at hPoint'
      rw [Metric.nhds_basis_closedBall.eventually_iff]
      let radius : Real := Classical.choose hPoint'
      have hRadius : 0 < radius := (Classical.choose_spec hPoint').1
      have hBound := (Classical.choose_spec hPoint').2
      refine Exists.intro radius (And.intro hRadius ?_)
      intro w hw y hy
      exact hBound (vertical_point_mem_closedBall hw hy)
    filter_upwards [hUniform] with w hw
    calc
      norm (intervalIntegral
          (fun y : Real => f (w.re + y * Complex.I) - f z)
          z.im w.im volume) <=
          epsilon * norm (w.im - z.im) :=
        intervalIntegral.norm_integral_le_of_norm_le_const hw
      _ = epsilon * norm ((w - z).im) := by simp
      _ <= epsilon * norm (w - z) :=
        (mul_le_mul_iff_of_pos_left hEpsilon).mpr
          (by simpa [Complex.norm_eq_abs] using Complex.abs_im_le_abs (w - z))
  have hEq : Filter.EventuallyEq (nhds z)
      (fun w : Complex => intervalIntegral
        (fun y : Real => f (w.re + y * Complex.I) - f z)
        z.im w.im volume)
      (fun w : Complex =>
        intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume -
          ((w - z).im : Complex) * f z) := by
    apply Metric.eventually_nhds_iff_ball.mpr
    refine Exists.intro (r - dist z c) ?_
    refine And.intro (by simpa using hz) ?_
    intro w hw
    have hInt : IntervalIntegrable
        (fun y : Real => f (w.re + y * Complex.I)) volume z.im w.im :=
      ((hContinuous.mono
          (nearby_vertical_segment_mem_ball hw).image_subset).comp
        (by fun_prop) (Set.mapsTo_image _ _)).intervalIntegrable
    calc
      intervalIntegral
          (fun y : Real => f (w.re + y * Complex.I) - f z)
          z.im w.im volume =
        intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume -
          intervalIntegral (fun _ : Real => f z) z.im w.im volume :=
        intervalIntegral.integral_sub hInt intervalIntegrable_const
      _ = intervalIntegral
            (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume -
          ((w - z).im : Complex) * f z := by
        simp
  exact hReduced.congr' hEq (Filter.EventuallyEq.rfl)

theorem conservative_hasDerivAt_wedgeIntegral
    (hContinuous : ContinuousOn f (Metric.ball c r))
    (hz : Membership.mem (Metric.ball c r) z)
    (hConservative : HolomorphicConservativeOn f (Metric.ball c r)) :
    HasDerivAt (fun w : Complex => holomorphicWedgeIntegral c w f)
      (f z) z := by
  rw [hasDerivAt_iff_isLittleO]
  have hSmall : Asymptotics.IsLittleO (nhds z)
      (fun w : Complex =>
        (intervalIntegral
            (fun x : Real => f (x + z.im * Complex.I)) z.re w.re volume -
          ((w - z).re : Complex) * f z) +
        Complex.I *
          (intervalIntegral
              (fun y : Real => f (w.re + y * Complex.I)) z.im w.im volume -
            ((w - z).im : Complex) * f z))
      (fun w : Complex => w - z) :=
    (horizontal_wedge_error_isLittleO hContinuous hz).add
      ((vertical_wedge_error_isLittleO hContinuous hz).const_smul_left
        Complex.I)
  apply hSmall.congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [conservative_eventually_wedge_difference
      hContinuous hz hConservative] with w hw
  rw [hw]
  unfold holomorphicWedgeIntegral
  rw [<- Complex.re_add_im (w - z)]
  simp only [smul_eq_mul]
  simp
  ring

end LocalDerivative

/-- The generic primitive statement isolated by TS278. -/
def HolomorphicPrimitiveOnBallStatement : Prop :=
  forall (f : Complex -> Complex) (c : Complex) (r : Real),
    DifferentiableOn Complex f (Metric.ball c r) ->
      HolomorphicExactOn f (Metric.ball c r)

theorem differentiableOn_holomorphicExactOn_ball
    {f : Complex -> Complex}
    {c : Complex}
    {r : Real}
    (hf : DifferentiableOn Complex f (Metric.ball c r)) :
    HolomorphicExactOn f (Metric.ball c r) := by
  refine Exists.intro
    (fun z : Complex => holomorphicWedgeIntegral c z f) ?_
  intro z hz
  exact conservative_hasDerivAt_wedgeIntegral
    hf.continuousOn hz (differentiableOn_holomorphicConservativeOn hf)

theorem holomorphicPrimitiveOnBallStatement :
    HolomorphicPrimitiveOnBallStatement := by
  intro f c r hf
  exact differentiableOn_holomorphicExactOn_ball hf

structure HolomorphicPrimitiveOnBallBackportLedger where
  ts277_reduction :
    TS277.Goldbach.NonvanishingQuotientHolomorphicLogReductionLedger

  primitive_on_open_ball_proved :
    HolomorphicPrimitiveOnBallStatement

  closed_ball_uniform_extension_not_proved : True
  quotient_logarithm_not_constructed : True
  complete_jensen_not_proved : True
  concrete_riemann_xi_not_defined : True
  zero_counting_bound_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def holomorphicPrimitiveOnBallBackportLedger :
    HolomorphicPrimitiveOnBallBackportLedger where
  ts277_reduction :=
    TS277.Goldbach.nonvanishingQuotientHolomorphicLogReductionLedger
  primitive_on_open_ball_proved := holomorphicPrimitiveOnBallStatement
  closed_ball_uniform_extension_not_proved := True.intro
  quotient_logarithm_not_constructed := True.intro
  complete_jensen_not_proved := True.intro
  concrete_riemann_xi_not_defined := True.intro
  zero_counting_bound_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def HolomorphicPrimitiveOnBallBackportTarget : Prop :=
  Nonempty HolomorphicPrimitiveOnBallBackportLedger

theorem holomorphicPrimitiveOnBallBackportTarget :
    HolomorphicPrimitiveOnBallBackportTarget :=
  Nonempty.intro holomorphicPrimitiveOnBallBackportLedger

end Goldbach
end TS278
