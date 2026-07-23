import Mathlib.Tactic
import TS.Goldbach.Strong.TS296.ConcreteStrongHeightXiQuotientLog

/-!
# TS297 - Xi/Zeta Horizontal Perron Bridge

TS296 constructs an exact finite factorization of xi and bounds `xi'/xi`
on the two horizontal sides.  This module performs the next structural step:
it passes exactly from `xi'/xi` to `-zeta'/zeta` and rewrites the concrete
Perron integrand.

The bridge uses the explicit local multiplier from TS290.  Away from the
real axis its reciprocal Gamma denominator is nonzero, so the identity

`xi = multiplier * zeta`

holds on a neighborhood and may be differentiated.  The resulting
completion correction is kept as an explicit logarithmic derivative; it is
not hidden in an anonymous remainder.

The top and bottom Perron integrands are then bounded pointwise by the exact
TS296 reciprocal load, the exact local logarithm sphere bound, and the exact
completion correction.  No asymptotic rate for these quantities is claimed.

This module does not prove a closed reciprocal-load rate, a
Borel-Caratheodory estimate, a left-side or right-cutoff estimate, Perron
inversion, the meromorphic residue theorem, an infinite explicit formula,
Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS297
namespace Goldbach

open Complex Filter Set Topology

/-- The explicit archimedean completion correction. -/
noncomputable def xiZetaCompletionLogDerivative
    (s : Complex) :
    Complex :=
  logDeriv TS290.Goldbach.xiZetaLocalMultiplier s

/-- The xi/zeta multiplier identity holds at every nonreal point. -/
theorem riemannXiCandidate_eq_localMultiplier_mul_riemannZeta_of_im_ne_zero
    {s : Complex}
    (hIm : Not (s.im = 0)) :
    TS282.Goldbach.riemannXiCandidate s =
      TS290.Goldbach.xiZetaLocalMultiplier s * riemannZeta s := by
  have hs0 : Not (s = 0) := by
    intro hs
    subst s
    exact hIm (by simp)
  have hs1 : Not (s = 1) := by
    intro hs
    subst s
    exact hIm (by simp)
  have hGamma :
      Not (TS282.Goldbach.completedRiemannZetaGammaInv s = 0) :=
    TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_im_ne_zero hIm
  rw [TS282.Goldbach.riemannXiCandidate_eq_completedRiemannZeta_mul
    hs0 hs1]
  rw [TS282.Goldbach.riemannZeta_eq_completed_mul_gammaInv hs0]
  unfold TS290.Goldbach.xiZetaLocalMultiplier
  field_simp [hGamma]
  ring

/-- The explicit multiplier is differentiable at every nonreal point. -/
theorem xiZetaLocalMultiplier_differentiableAt_of_im_ne_zero
    {s : Complex}
    (hIm : Not (s.im = 0)) :
    DifferentiableAt Complex TS290.Goldbach.xiZetaLocalMultiplier s := by
  unfold TS290.Goldbach.xiZetaLocalMultiplier
  exact
    (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2).div
      TS282.Goldbach.differentiable_completedRiemannZetaGammaInv.differentiableAt
      (TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_im_ne_zero hIm))

/-- The explicit multiplier is nonzero at every nonreal point. -/
theorem xiZetaLocalMultiplier_ne_zero_of_im_ne_zero
    {s : Complex}
    (hIm : Not (s.im = 0)) :
    Not (TS290.Goldbach.xiZetaLocalMultiplier s = 0) := by
  have hs0 : Not (s = 0) := by
    intro hs
    subst s
    exact hIm (by simp)
  have hs1 : Not (s = 1) := by
    intro hs
    subst s
    exact hIm (by simp)
  unfold TS290.Goldbach.xiZetaLocalMultiplier
  exact div_ne_zero
    (div_ne_zero
      (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num))
    (TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_im_ne_zero hIm)

/-- The multiplier identity holds on a full neighborhood of a nonreal point. -/
theorem riemannXiCandidate_eventuallyEq_localMultiplier_mul_riemannZeta_of_im_ne_zero
    {s : Complex}
    (hIm : Not (s.im = 0)) :
    Filter.Eventually
      (fun z =>
        TS282.Goldbach.riemannXiCandidate z =
          TS290.Goldbach.xiZetaLocalMultiplier z * riemannZeta z)
      (nhds s) := by
  have hOpen : IsOpen {z : Complex | Not (z.im = 0)} := by
    exact
      (isClosed_singleton.isOpen_compl.preimage Complex.continuous_im)
  have hEventually :
      Filter.Eventually (fun z : Complex => Not (z.im = 0)) (nhds s) :=
    hOpen.mem_nhds hIm
  filter_upwards [hEventually] with z hz
  exact
    riemannXiCandidate_eq_localMultiplier_mul_riemannZeta_of_im_ne_zero hz

/-- Exact logarithmic-derivative completion identity off the real axis. -/
theorem neg_riemannZeta_logDerivative_eq_completion_sub_xi
    {s : Complex}
    (hIm : Not (s.im = 0))
    (hZeta : Not (riemannZeta s = 0)) :
    -deriv riemannZeta s / riemannZeta s =
      xiZetaCompletionLogDerivative s -
        deriv TS282.Goldbach.riemannXiCandidate s /
          TS282.Goldbach.riemannXiCandidate s := by
  have hMultiplier :
      Not (TS290.Goldbach.xiZetaLocalMultiplier s = 0) :=
    xiZetaLocalMultiplier_ne_zero_of_im_ne_zero hIm
  have hXiPoint :=
    riemannXiCandidate_eq_localMultiplier_mul_riemannZeta_of_im_ne_zero hIm
  have hXi :
      Not (TS282.Goldbach.riemannXiCandidate s = 0) := by
    rw [hXiPoint]
    exact mul_ne_zero hMultiplier hZeta
  have hMultiplierDiff :
      DifferentiableAt Complex TS290.Goldbach.xiZetaLocalMultiplier s :=
    xiZetaLocalMultiplier_differentiableAt_of_im_ne_zero hIm
  have hs1 : Not (s = 1) := by
    intro hs
    subst s
    exact hIm (by simp)
  have hZetaDiff : DifferentiableAt Complex riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hEventually :
      Filter.EventuallyEq (nhds s)
        TS282.Goldbach.riemannXiCandidate
        (fun z =>
          TS290.Goldbach.xiZetaLocalMultiplier z * riemannZeta z) :=
    riemannXiCandidate_eventuallyEq_localMultiplier_mul_riemannZeta_of_im_ne_zero
      hIm
  have hDeriv :
      deriv TS282.Goldbach.riemannXiCandidate s =
        deriv
          (fun z =>
            TS290.Goldbach.xiZetaLocalMultiplier z * riemannZeta z) s :=
    Filter.EventuallyEq.deriv_eq hEventually
  have hLogProduct :=
    logDeriv_mul s hMultiplier hZeta hMultiplierDiff hZetaDiff
  have hXiLog :
      logDeriv TS282.Goldbach.riemannXiCandidate s =
        logDeriv TS290.Goldbach.xiZetaLocalMultiplier s +
          logDeriv riemannZeta s := by
    calc
      logDeriv TS282.Goldbach.riemannXiCandidate s =
          logDeriv
            (fun z =>
              TS290.Goldbach.xiZetaLocalMultiplier z * riemannZeta z) s := by
        unfold logDeriv
        change
          deriv TS282.Goldbach.riemannXiCandidate s /
              TS282.Goldbach.riemannXiCandidate s =
            deriv
                (fun z =>
                  TS290.Goldbach.xiZetaLocalMultiplier z * riemannZeta z) s /
              (TS290.Goldbach.xiZetaLocalMultiplier s * riemannZeta s)
        rw [hDeriv, hXiPoint]
      _ =
          logDeriv TS290.Goldbach.xiZetaLocalMultiplier s +
            logDeriv riemannZeta s := hLogProduct
  unfold xiZetaCompletionLogDerivative
  rw [neg_div]
  change
    -(logDeriv riemannZeta s) =
      logDeriv TS290.Goldbach.xiZetaLocalMultiplier s -
        logDeriv TS282.Goldbach.riemannXiCandidate s
  rw [hXiLog]
  ring

/-- The top horizontal point used by TS296. -/
noncomputable def topHorizontalPoint
    (T : Nat)
    (sigma : Real) :
    Complex :=
  TS296.Goldbach.strongHeightTopCenter T sigma

/-- The bottom horizontal point used by TS296. -/
noncomputable def bottomHorizontalPoint
    (T : Nat)
    (sigma : Real) :
    Complex :=
  TS296.Goldbach.strongHeightBottomCenter T sigma

theorem topHorizontalPoint_im_ne_zero
    {T : Nat}
    (hT : 1 <= T)
    (sigma : Real) :
    Not ((topHorizontalPoint T sigma).im = 0) := by
  unfold topHorizontalPoint TS296.Goldbach.strongHeightTopCenter
  simp only [add_im, ofReal_im, mul_im, I_im, I_re, ofReal_re,
    mul_one, mul_zero, zero_add]
  simpa using ne_of_gt (TS296.Goldbach.strongHeightTau_pos hT)

theorem bottomHorizontalPoint_im_ne_zero
    {T : Nat}
    (hT : 1 <= T)
    (sigma : Real) :
    Not ((bottomHorizontalPoint T sigma).im = 0) := by
  unfold bottomHorizontalPoint TS296.Goldbach.strongHeightBottomCenter
  simp only [sub_im, ofReal_im, mul_im, I_im, I_re, ofReal_re,
    mul_one, mul_zero, zero_sub, neg_eq_zero]
  simpa using ne_of_gt (TS296.Goldbach.strongHeightTau_pos hT)

theorem riemannXiCandidate_ne_zero_top_center
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Not
      (TS282.Goldbach.riemannXiCandidate (topHorizontalPoint T sigma) = 0) := by
  apply TS296.Goldbach.riemannXiCandidate_ne_zero_on_top_ball T hT sigma
  rw [Metric.mem_closedBall]
  exact (dist_self _).trans_le
    (div_nonneg (TS296.Goldbach.strongHeightDelta_pos T).le (by norm_num))

theorem riemannXiCandidate_ne_zero_bottom_center
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Not
      (TS282.Goldbach.riemannXiCandidate (bottomHorizontalPoint T sigma) = 0) := by
  apply TS296.Goldbach.riemannXiCandidate_ne_zero_on_bottom_ball T hT sigma
  rw [Metric.mem_closedBall]
  exact (dist_self _).trans_le
    (div_nonneg (TS296.Goldbach.strongHeightDelta_pos T).le (by norm_num))

theorem riemannZeta_ne_zero_of_im_ne_zero_of_xi_ne_zero
    {s : Complex}
    (hIm : Not (s.im = 0))
    (hXi : Not (TS282.Goldbach.riemannXiCandidate s = 0)) :
    Not (riemannZeta s = 0) := by
  intro hZeta
  apply hXi
  rw [riemannXiCandidate_eq_localMultiplier_mul_riemannZeta_of_im_ne_zero hIm,
    hZeta]
  simp

theorem riemannZeta_ne_zero_top_center
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Not (riemannZeta (topHorizontalPoint T sigma) = 0) :=
  riemannZeta_ne_zero_of_im_ne_zero_of_xi_ne_zero
    (topHorizontalPoint_im_ne_zero hT sigma)
    (riemannXiCandidate_ne_zero_top_center T hT sigma)

theorem riemannZeta_ne_zero_bottom_center
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Not (riemannZeta (bottomHorizontalPoint T sigma) = 0) :=
  riemannZeta_ne_zero_of_im_ne_zero_of_xi_ne_zero
    (bottomHorizontalPoint_im_ne_zero hT sigma)
    (riemannXiCandidate_ne_zero_bottom_center T hT sigma)

/-- Exact top-side `-zeta'/zeta` decomposition with the TS296 quotient. -/
theorem neg_riemannZeta_logDerivative_eq_finite_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    -deriv riemannZeta (topHorizontalPoint T sigma) /
        riemannZeta (topHorizontalPoint T sigma) =
      xiZetaCompletionLogDerivative (topHorizontalPoint T sigma) -
        TS295.Goldbach.finiteZeroLogDerivativeSum T
          (topHorizontalPoint T sigma) -
        deriv (TS296.Goldbach.heightXiQuotient T)
            (topHorizontalPoint T sigma) /
          TS296.Goldbach.heightXiQuotient T
            (topHorizontalPoint T sigma) := by
  have hCompletion :=
    neg_riemannZeta_logDerivative_eq_completion_sub_xi
      (topHorizontalPoint_im_ne_zero hT sigma)
      (riemannZeta_ne_zero_top_center T hT sigma)
  have hXi :=
    TS296.Goldbach.heightXiQuotient_logDerivative_identity_top T hT sigma
  calc
    -deriv riemannZeta (topHorizontalPoint T sigma) /
          riemannZeta (topHorizontalPoint T sigma) =
        xiZetaCompletionLogDerivative (topHorizontalPoint T sigma) -
          deriv TS282.Goldbach.riemannXiCandidate
              (topHorizontalPoint T sigma) /
            TS282.Goldbach.riemannXiCandidate
              (topHorizontalPoint T sigma) := hCompletion
    _ =
        xiZetaCompletionLogDerivative (topHorizontalPoint T sigma) -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T
              (topHorizontalPoint T sigma) +
            deriv (TS296.Goldbach.heightXiQuotient T)
                (topHorizontalPoint T sigma) /
              TS296.Goldbach.heightXiQuotient T
                (topHorizontalPoint T sigma)) := by
      rw [show
        deriv TS282.Goldbach.riemannXiCandidate
              (topHorizontalPoint T sigma) /
            TS282.Goldbach.riemannXiCandidate
              (topHorizontalPoint T sigma) =
          TS295.Goldbach.finiteZeroLogDerivativeSum T
              (topHorizontalPoint T sigma) +
            deriv (TS296.Goldbach.heightXiQuotient T)
                (topHorizontalPoint T sigma) /
              TS296.Goldbach.heightXiQuotient T
                (topHorizontalPoint T sigma) by
        simpa [topHorizontalPoint] using hXi]
    _ = _ := by ring

/-- Exact bottom-side `-zeta'/zeta` decomposition with the TS296 quotient. -/
theorem neg_riemannZeta_logDerivative_eq_finite_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    -deriv riemannZeta (bottomHorizontalPoint T sigma) /
        riemannZeta (bottomHorizontalPoint T sigma) =
      xiZetaCompletionLogDerivative (bottomHorizontalPoint T sigma) -
        TS295.Goldbach.finiteZeroLogDerivativeSum T
          (bottomHorizontalPoint T sigma) -
        deriv (TS296.Goldbach.heightXiQuotient T)
            (bottomHorizontalPoint T sigma) /
          TS296.Goldbach.heightXiQuotient T
            (bottomHorizontalPoint T sigma) := by
  have hCompletion :=
    neg_riemannZeta_logDerivative_eq_completion_sub_xi
      (bottomHorizontalPoint_im_ne_zero hT sigma)
      (riemannZeta_ne_zero_bottom_center T hT sigma)
  have hXi :=
    TS296.Goldbach.heightXiQuotient_logDerivative_identity_bottom T hT sigma
  calc
    -deriv riemannZeta (bottomHorizontalPoint T sigma) /
          riemannZeta (bottomHorizontalPoint T sigma) =
        xiZetaCompletionLogDerivative (bottomHorizontalPoint T sigma) -
          deriv TS282.Goldbach.riemannXiCandidate
              (bottomHorizontalPoint T sigma) /
            TS282.Goldbach.riemannXiCandidate
              (bottomHorizontalPoint T sigma) := hCompletion
    _ =
        xiZetaCompletionLogDerivative (bottomHorizontalPoint T sigma) -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T
              (bottomHorizontalPoint T sigma) +
            deriv (TS296.Goldbach.heightXiQuotient T)
                (bottomHorizontalPoint T sigma) /
              TS296.Goldbach.heightXiQuotient T
                (bottomHorizontalPoint T sigma)) := by
      rw [show
        deriv TS282.Goldbach.riemannXiCandidate
              (bottomHorizontalPoint T sigma) /
            TS282.Goldbach.riemannXiCandidate
              (bottomHorizontalPoint T sigma) =
          TS295.Goldbach.finiteZeroLogDerivativeSum T
              (bottomHorizontalPoint T sigma) +
            deriv (TS296.Goldbach.heightXiQuotient T)
                (bottomHorizontalPoint T sigma) /
              TS296.Goldbach.heightXiQuotient T
                (bottomHorizontalPoint T sigma) by
        simpa [bottomHorizontalPoint] using hXi]
    _ = _ := by ring

/-- Exact pointwise top-side envelope for the zeta logarithmic derivative. -/
noncomputable def topZetaLogDerivativeEnvelope
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Real :=
  norm (xiZetaCompletionLogDerivative (topHorizontalPoint T sigma)) +
    TS296.Goldbach.strongHeightLoadEnvelope T +
      (TS296.Goldbach.topHeightXiQuotientLocalLogData T hT sigma).sphereBound /
        (TS296.Goldbach.topHeightXiQuotientLocalLogData T hT sigma).radius

/-- Exact pointwise bottom-side envelope for the zeta logarithmic derivative. -/
noncomputable def bottomZetaLogDerivativeEnvelope
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    Real :=
  norm (xiZetaCompletionLogDerivative (bottomHorizontalPoint T sigma)) +
    TS296.Goldbach.strongHeightLoadEnvelope T +
      (TS296.Goldbach.bottomHeightXiQuotientLocalLogData T hT sigma).sphereBound /
        (TS296.Goldbach.bottomHeightXiQuotientLocalLogData T hT sigma).radius

theorem neg_riemannZeta_logDerivative_norm_le_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm
        (-deriv riemannZeta (topHorizontalPoint T sigma) /
          riemannZeta (topHorizontalPoint T sigma)) <=
      topZetaLogDerivativeEnvelope T hT sigma := by
  have hCompletion :=
    neg_riemannZeta_logDerivative_eq_completion_sub_xi
      (topHorizontalPoint_im_ne_zero hT sigma)
      (riemannZeta_ne_zero_top_center T hT sigma)
  rw [hCompletion]
  unfold topZetaLogDerivativeEnvelope topHorizontalPoint
  calc
    norm
        (xiZetaCompletionLogDerivative
            (TS296.Goldbach.strongHeightTopCenter T sigma) -
          deriv TS282.Goldbach.riemannXiCandidate
              (TS296.Goldbach.strongHeightTopCenter T sigma) /
            TS282.Goldbach.riemannXiCandidate
              (TS296.Goldbach.strongHeightTopCenter T sigma)) <=
        norm
            (xiZetaCompletionLogDerivative
              (TS296.Goldbach.strongHeightTopCenter T sigma)) +
          norm
            (deriv TS282.Goldbach.riemannXiCandidate
                (TS296.Goldbach.strongHeightTopCenter T sigma) /
              TS282.Goldbach.riemannXiCandidate
                (TS296.Goldbach.strongHeightTopCenter T sigma)) :=
      norm_sub_le _ _
    _ <=
        norm
            (xiZetaCompletionLogDerivative
              (TS296.Goldbach.strongHeightTopCenter T sigma)) +
          (TS296.Goldbach.strongHeightLoadEnvelope T +
            (TS296.Goldbach.topHeightXiQuotientLocalLogData T hT sigma).sphereBound /
              (TS296.Goldbach.topHeightXiQuotientLocalLogData T hT sigma).radius) :=
      add_le_add_left
        (TS296.Goldbach.riemannXiCandidate_logDerivative_norm_le_top
          T hT sigma) _
    _ =
        norm
            (xiZetaCompletionLogDerivative
              (TS296.Goldbach.strongHeightTopCenter T sigma)) +
          TS296.Goldbach.strongHeightLoadEnvelope T +
          (TS296.Goldbach.topHeightXiQuotientLocalLogData T hT sigma).sphereBound /
            (TS296.Goldbach.topHeightXiQuotientLocalLogData T hT sigma).radius := by
      ring

theorem neg_riemannZeta_logDerivative_norm_le_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm
        (-deriv riemannZeta (bottomHorizontalPoint T sigma) /
          riemannZeta (bottomHorizontalPoint T sigma)) <=
      bottomZetaLogDerivativeEnvelope T hT sigma := by
  have hCompletion :=
    neg_riemannZeta_logDerivative_eq_completion_sub_xi
      (bottomHorizontalPoint_im_ne_zero hT sigma)
      (riemannZeta_ne_zero_bottom_center T hT sigma)
  rw [hCompletion]
  unfold bottomZetaLogDerivativeEnvelope bottomHorizontalPoint
  calc
    norm
        (xiZetaCompletionLogDerivative
            (TS296.Goldbach.strongHeightBottomCenter T sigma) -
          deriv TS282.Goldbach.riemannXiCandidate
              (TS296.Goldbach.strongHeightBottomCenter T sigma) /
            TS282.Goldbach.riemannXiCandidate
              (TS296.Goldbach.strongHeightBottomCenter T sigma)) <=
        norm
            (xiZetaCompletionLogDerivative
              (TS296.Goldbach.strongHeightBottomCenter T sigma)) +
          norm
            (deriv TS282.Goldbach.riemannXiCandidate
                (TS296.Goldbach.strongHeightBottomCenter T sigma) /
              TS282.Goldbach.riemannXiCandidate
                (TS296.Goldbach.strongHeightBottomCenter T sigma)) :=
      norm_sub_le _ _
    _ <=
        norm
            (xiZetaCompletionLogDerivative
              (TS296.Goldbach.strongHeightBottomCenter T sigma)) +
          (TS296.Goldbach.strongHeightLoadEnvelope T +
            (TS296.Goldbach.bottomHeightXiQuotientLocalLogData T hT sigma).sphereBound /
              (TS296.Goldbach.bottomHeightXiQuotientLocalLogData T hT sigma).radius) :=
      add_le_add_left
        (TS296.Goldbach.riemannXiCandidate_logDerivative_norm_le_bottom
          T hT sigma) _
    _ =
        norm
            (xiZetaCompletionLogDerivative
              (TS296.Goldbach.strongHeightBottomCenter T sigma)) +
          TS296.Goldbach.strongHeightLoadEnvelope T +
          (TS296.Goldbach.bottomHeightXiQuotientLocalLogData T hT sigma).sphereBound /
            (TS296.Goldbach.bottomHeightXiQuotientLocalLogData T hT sigma).radius := by
      ring

/-- Exact top horizontal rewrite of the concrete TS293 Perron integrand. -/
theorem triangleSplinePerronIntegrand_eq_completed_top
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    TS293.Goldbach.triangleSplinePerronIntegrand x
        (topHorizontalPoint T sigma) =
      (xiZetaCompletionLogDerivative (topHorizontalPoint T sigma) -
          TS295.Goldbach.finiteZeroLogDerivativeSum T
            (topHorizontalPoint T sigma) -
          deriv (TS296.Goldbach.heightXiQuotient T)
              (topHorizontalPoint T sigma) /
            TS296.Goldbach.heightXiQuotient T
              (topHorizontalPoint T sigma)) *
        (x : Complex) ^ (topHorizontalPoint T sigma) *
          TS257.Goldbach.triangleSplineMellinKernel
            (topHorizontalPoint T sigma) := by
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
  rw [neg_riemannZeta_logDerivative_eq_finite_top T hT sigma]

/-- Exact bottom horizontal rewrite of the concrete TS293 Perron integrand. -/
theorem triangleSplinePerronIntegrand_eq_completed_bottom
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    TS293.Goldbach.triangleSplinePerronIntegrand x
        (bottomHorizontalPoint T sigma) =
      (xiZetaCompletionLogDerivative (bottomHorizontalPoint T sigma) -
          TS295.Goldbach.finiteZeroLogDerivativeSum T
            (bottomHorizontalPoint T sigma) -
          deriv (TS296.Goldbach.heightXiQuotient T)
              (bottomHorizontalPoint T sigma) /
            TS296.Goldbach.heightXiQuotient T
              (bottomHorizontalPoint T sigma)) *
        (x : Complex) ^ (bottomHorizontalPoint T sigma) *
          TS257.Goldbach.triangleSplineMellinKernel
            (bottomHorizontalPoint T sigma) := by
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
  rw [neg_riemannZeta_logDerivative_eq_finite_bottom T hT sigma]

theorem triangleSplinePerronIntegrand_norm_le_top
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm
        (TS293.Goldbach.triangleSplinePerronIntegrand x
          (topHorizontalPoint T sigma)) <=
      topZetaLogDerivativeEnvelope T hT sigma *
        norm ((x : Complex) ^ (topHorizontalPoint T sigma)) *
          norm
            (TS257.Goldbach.triangleSplineMellinKernel
              (topHorizontalPoint T sigma)) := by
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
  simp only [norm_mul]
  gcongr
  exact neg_riemannZeta_logDerivative_norm_le_top T hT sigma

theorem triangleSplinePerronIntegrand_norm_le_bottom
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    norm
        (TS293.Goldbach.triangleSplinePerronIntegrand x
          (bottomHorizontalPoint T sigma)) <=
      bottomZetaLogDerivativeEnvelope T hT sigma *
        norm ((x : Complex) ^ (bottomHorizontalPoint T sigma)) *
          norm
            (TS257.Goldbach.triangleSplineMellinKernel
              (bottomHorizontalPoint T sigma)) := by
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
  simp only [norm_mul]
  gcongr
  exact neg_riemannZeta_logDerivative_norm_le_bottom T hT sigma

structure XiZetaHorizontalPerronBridgeLedger where
  gamma_inverse_nonzero_off_real_axis : True
  xi_zeta_multiplier_identity_off_real_axis : True
  xi_to_zeta_log_derivative_identity : True
  exact_top_finite_quotient_decomposition : True
  exact_bottom_finite_quotient_decomposition : True
  top_perron_integrand_rewrite : True
  bottom_perron_integrand_rewrite : True
  top_pointwise_perron_bound : True
  bottom_pointwise_perron_bound : True

  reciprocal_load_rate_not_proved : True
  effective_log_sphere_rate_not_proved : True
  completion_correction_rate_not_proved : True
  integrated_horizontal_side_bound_not_proved : True
  left_boundary_not_estimated : True
  right_cutoff_not_estimated : True
  exceptional_inventory_not_completed : True
  perron_inversion_not_proved : True
  meromorphic_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def xiZetaHorizontalPerronBridgeLedger :
    XiZetaHorizontalPerronBridgeLedger where
  gamma_inverse_nonzero_off_real_axis := True.intro
  xi_zeta_multiplier_identity_off_real_axis := True.intro
  xi_to_zeta_log_derivative_identity := True.intro
  exact_top_finite_quotient_decomposition := True.intro
  exact_bottom_finite_quotient_decomposition := True.intro
  top_perron_integrand_rewrite := True.intro
  bottom_perron_integrand_rewrite := True.intro
  top_pointwise_perron_bound := True.intro
  bottom_pointwise_perron_bound := True.intro
  reciprocal_load_rate_not_proved := True.intro
  effective_log_sphere_rate_not_proved := True.intro
  completion_correction_rate_not_proved := True.intro
  integrated_horizontal_side_bound_not_proved := True.intro
  left_boundary_not_estimated := True.intro
  right_cutoff_not_estimated := True.intro
  exceptional_inventory_not_completed := True.intro
  perron_inversion_not_proved := True.intro
  meromorphic_residue_theorem_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

def XiZetaHorizontalPerronBridgeTarget : Prop :=
  Nonempty XiZetaHorizontalPerronBridgeLedger

theorem xiZetaHorizontalPerronBridgeTarget :
    XiZetaHorizontalPerronBridgeTarget :=
  Nonempty.intro xiZetaHorizontalPerronBridgeLedger

end Goldbach
end TS297
