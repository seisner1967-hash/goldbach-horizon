import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import TS.Goldbach.Strong.TS76.TriangleSplineIPPIntervalIntegralBridgeProof

namespace TS77
namespace MellinJackson

/-!
# TS77 - Triangle Spline IPP Affine Branch Proof

This sprint proves the two local affine integration-by-parts identities
recorded in TS73.

The proof first applies Mathlib's interval-integral integration-by-parts
theorem to the affine functions `1 + x` and `1 - x`, then transports the
result back through the branch formulae for `triangleSpline` and the a.e.
branch values of `triangleSplineDeriv`.

It does not yet perform the final TS74 recombination into the concrete
distributional contract.
-/

open MeasureTheory Set

/-- Complex-valued affine function `1 + x` on the left branch. -/
noncomputable def leftAffine (x : Real) : Complex :=
  ((1 : Real) + x : Real)

/-- Complex-valued affine function `1 - x` on the right branch. -/
noncomputable def rightAffine (x : Real) : Complex :=
  ((1 : Real) - x : Real)

/-- The concrete test derivative agrees pointwise with `HasDerivAt`. -/
theorem testFunction_hasDerivAt
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction)
    (x : Real) :
    HasDerivAt phi.toFun (phi.derivFun x) x := by
  have hdiff : DifferentiableAt Real phi.toFun x :=
    phi.contDiff_toFun.differentiable (by norm_num) x
  simpa [phi.deriv_agrees] using hdiff.hasDerivAt

/-- The derivative of `leftAffine` is `1`. -/
theorem leftAffine_hasDerivAt
    (x : Real) :
    HasDerivAt leftAffine (1 : Complex) x := by
  unfold leftAffine
  simpa [Complex.ofReal_add] using
    ((hasDerivAt_const (x := x) (c := (1 : Complex))).add
      (Complex.ofRealCLM.hasDerivAt (x := x)))

/-- The derivative of `rightAffine` is `-1`. -/
theorem rightAffine_hasDerivAt
    (x : Real) :
    HasDerivAt rightAffine (-1 : Complex) x := by
  unfold rightAffine
  simpa [Complex.ofReal_sub] using
    ((hasDerivAt_const (x := x) (c := (1 : Complex))).sub
      (Complex.ofRealCLM.hasDerivAt (x := x)))

/-- Integration by parts for the left affine branch in interval-integral form. -/
theorem left_affine_interval_ipp
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    TS75.MellinJackson.leftBranchIntervalIntegral
      (fun x : Real => leftAffine x * phi.derivFun x)
      =
    phi.toFun 0
      -
    TS75.MellinJackson.leftBranchIntervalIntegral
      (fun x : Real => (1 : Complex) * phi.toFun x) := by
  have h_ip :
      intervalIntegral
        (fun x : Real => leftAffine x * phi.derivFun x)
        (-1 : Real) 0 (volume : Measure Real)
        =
      leftAffine 0 * phi.toFun 0
        - leftAffine (-1) * phi.toFun (-1)
        -
      intervalIntegral
        (fun x : Real => (1 : Complex) * phi.toFun x)
        (-1 : Real) 0 (volume : Measure Real) := by
    exact
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := (-1 : Real))
        (b := 0)
        (u := leftAffine)
        (v := phi.toFun)
        (u' := fun _ : Real => (1 : Complex))
        (v' := phi.derivFun)
        (fun x _ => leftAffine_hasDerivAt x)
        (fun x _ => testFunction_hasDerivAt phi x)
        ((continuous_const : Continuous (fun _ : Real => (1 : Complex))).intervalIntegrable _ _)
        ((TS65.MellinJackson.testFunction_deriv_integrable phi).intervalIntegrable)
  simpa [
    TS75.MellinJackson.leftBranchIntervalIntegral,
    leftAffine
  ] using h_ip

/-- Integration by parts for the right affine branch in interval-integral form. -/
theorem right_affine_interval_ipp
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (fun x : Real => rightAffine x * phi.derivFun x)
      =
    - phi.toFun 0
      -
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (fun x : Real => (-1 : Complex) * phi.toFun x) := by
  have h_ip :
      intervalIntegral
        (fun x : Real => rightAffine x * phi.derivFun x)
        (0 : Real) 1 (volume : Measure Real)
        =
      rightAffine 1 * phi.toFun 1
        - rightAffine 0 * phi.toFun 0
        -
      intervalIntegral
        (fun x : Real => (-1 : Complex) * phi.toFun x)
        (0 : Real) 1 (volume : Measure Real) := by
    exact
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := (0 : Real))
        (b := 1)
        (u := rightAffine)
        (v := phi.toFun)
        (u' := fun _ : Real => (-1 : Complex))
        (v' := phi.derivFun)
        (fun x _ => rightAffine_hasDerivAt x)
        (fun x _ => testFunction_hasDerivAt phi x)
        ((continuous_const : Continuous (fun _ : Real => (-1 : Complex))).intervalIntegrable _ _)
        ((TS65.MellinJackson.testFunction_deriv_integrable phi).intervalIntegrable)
  simpa [
    TS75.MellinJackson.rightClosedBranchIntervalIntegral,
    rightAffine
  ] using h_ip

/-- On the left branch, the left IPP integrand agrees with the affine one. -/
theorem leftIPPIntegrand_eq_leftAffine_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    TS75.MellinJackson.leftBranchIntervalIntegral
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    TS75.MellinJackson.leftBranchIntervalIntegral
      (fun x : Real => leftAffine x * phi.derivFun x) := by
  unfold TS75.MellinJackson.leftBranchIntervalIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : Icc (-1 : Real) 0 x := by
    simpa [uIcc_of_le (by norm_num : (-1 : Real) <= 0)] using hx
  have hx_left : (-1 : Real) <= x := hxI.1
  have hx_right : x <= (0 : Real) := hxI.2
  have h_formula :
      TS42.MellinJackson.triangleSpline x = 1 + x :=
    TS56.MellinJackson.triangleSpline_eq_one_add_of_left hx_left hx_right
  simp [TS67.MellinJackson.leftIPPIntegrand, leftAffine, h_formula]

/-- On the right branch, the left IPP integrand agrees with the affine one. -/
theorem leftIPPIntegrand_eq_rightAffine_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (fun x : Real => rightAffine x * phi.derivFun x) := by
  unfold TS75.MellinJackson.rightClosedBranchIntervalIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : Icc (0 : Real) 1 x := by
    simpa [uIcc_of_le (by norm_num : (0 : Real) <= 1)] using hx
  have hx_left : (0 : Real) <= x := hxI.1
  have hx_right : x <= (1 : Real) := hxI.2
  have h_formula :
      TS42.MellinJackson.triangleSpline x = 1 - x :=
    TS56.MellinJackson.triangleSpline_eq_one_sub_of_right hx_left hx_right
  simp [TS67.MellinJackson.leftIPPIntegrand, rightAffine, h_formula]

/-- On the left branch, the right IPP integrand agrees a.e. with `1 * phi`. -/
theorem rightIPPIntegrand_eq_leftAffine_derivative_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    TS75.MellinJackson.leftBranchIntervalIntegral
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    TS75.MellinJackson.leftBranchIntervalIntegral
      (fun x : Real => (1 : Complex) * phi.toFun x) := by
  unfold TS75.MellinJackson.leftBranchIntervalIntegral
  have h_forward :
      Filter.Eventually
        (fun x : Real =>
          Ioc (-1 : Real) 0 x ->
            TS67.MellinJackson.rightIPPIntegrand phi x =
              (1 : Complex) * phi.toFun x)
        (ae (volume : Measure Real)) := by
    have hne :
        Filter.Eventually
          (fun x : Real => x = (0 : Real) -> False)
          (ae (volume : Measure Real)) := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with x hx_ne hx
    have hx0 : x < 0 := lt_of_le_of_ne hx.2 hx_ne
    have hder :
        TS42.MellinJackson.triangleSplineDeriv x = 1 :=
      TS43.MellinJackson.triangleSplineDeriv_eq_one_of_left hx.1 hx0
    simp [TS67.MellinJackson.rightIPPIntegrand, hder]
  have h_backward :
      Filter.Eventually
        (fun x : Real =>
          Ioc (0 : Real) (-1) x ->
            TS67.MellinJackson.rightIPPIntegrand phi x =
              (1 : Complex) * phi.toFun x)
        (ae (volume : Measure Real)) := by
    filter_upwards with x hx
    exfalso
    linarith [hx.1, hx.2]
  exact intervalIntegral.integral_congr_ae' h_forward h_backward

/-- On the right branch, the right IPP integrand agrees a.e. with `-1 * phi`. -/
theorem rightIPPIntegrand_eq_rightAffine_derivative_interval
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    TS75.MellinJackson.rightClosedBranchIntervalIntegral
      (fun x : Real => (-1 : Complex) * phi.toFun x) := by
  unfold TS75.MellinJackson.rightClosedBranchIntervalIntegral
  have h_forward :
      Filter.Eventually
        (fun x : Real =>
          Ioc (0 : Real) 1 x ->
            TS67.MellinJackson.rightIPPIntegrand phi x =
              (-1 : Complex) * phi.toFun x)
        (ae (volume : Measure Real)) := by
    have hne :
        Filter.Eventually
          (fun x : Real => x = (1 : Real) -> False)
          (ae (volume : Measure Real)) := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with x hx_ne hx
    have hx1 : x < 1 := lt_of_le_of_ne hx.2 hx_ne
    have hder :
        TS42.MellinJackson.triangleSplineDeriv x = -1 :=
      TS43.MellinJackson.triangleSplineDeriv_eq_neg_one_of_right hx.1 hx1
    simp [TS67.MellinJackson.rightIPPIntegrand, hder]
  have h_backward :
      Filter.Eventually
        (fun x : Real =>
          Ioc (1 : Real) 0 x ->
            TS67.MellinJackson.rightIPPIntegrand phi x =
              (-1 : Complex) * phi.toFun x)
        (ae (volume : Measure Real)) := by
    filter_upwards with x hx
    exfalso
    linarith [hx.1, hx.2]
  exact intervalIntegral.integral_congr_ae' h_forward h_backward

/-- The left affine branch IPP identity in the TS73 restricted-measure form. -/
theorem left_affine_ipp
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS69.MellinJackson.leftBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    phi.toFun 0
      -
    integral TS69.MellinJackson.leftBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  calc
    integral TS69.MellinJackson.leftBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
        =
      TS75.MellinJackson.leftBranchIntervalIntegral
        (TS67.MellinJackson.leftIPPIntegrand phi) := by
        exact TS76.MellinJackson.left_leftBranchMeasure_eq_interval phi
    _ =
      TS75.MellinJackson.leftBranchIntervalIntegral
        (fun x : Real => leftAffine x * phi.derivFun x) := by
        exact leftIPPIntegrand_eq_leftAffine_interval phi
    _ =
      phi.toFun 0
        -
      TS75.MellinJackson.leftBranchIntervalIntegral
        (fun x : Real => (1 : Complex) * phi.toFun x) := by
        exact left_affine_interval_ipp phi
    _ =
      phi.toFun 0
        -
      TS75.MellinJackson.leftBranchIntervalIntegral
        (TS67.MellinJackson.rightIPPIntegrand phi) := by
        rw [(rightIPPIntegrand_eq_leftAffine_derivative_interval phi).symm]
    _ =
      phi.toFun 0
        -
      integral TS69.MellinJackson.leftBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi) := by
        rw [(TS76.MellinJackson.right_leftBranchMeasure_eq_interval phi).symm]

/-- The right affine branch IPP identity in the TS73 restricted-measure form. -/
theorem right_affine_ipp
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral TS71.MellinJackson.rightClosedBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    - phi.toFun 0
      -
    integral TS71.MellinJackson.rightClosedBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  calc
    integral TS71.MellinJackson.rightClosedBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
        =
      TS75.MellinJackson.rightClosedBranchIntervalIntegral
        (TS67.MellinJackson.leftIPPIntegrand phi) := by
        exact TS76.MellinJackson.left_rightClosedBranchMeasure_eq_interval phi
    _ =
      TS75.MellinJackson.rightClosedBranchIntervalIntegral
        (fun x : Real => rightAffine x * phi.derivFun x) := by
        exact leftIPPIntegrand_eq_rightAffine_interval phi
    _ =
      - phi.toFun 0
        -
      TS75.MellinJackson.rightClosedBranchIntervalIntegral
        (fun x : Real => (-1 : Complex) * phi.toFun x) := by
        exact right_affine_interval_ipp phi
    _ =
      - phi.toFun 0
        -
      TS75.MellinJackson.rightClosedBranchIntervalIntegral
        (TS67.MellinJackson.rightIPPIntegrand phi) := by
        rw [(rightIPPIntegrand_eq_rightAffine_derivative_interval phi).symm]
    _ =
      - phi.toFun 0
        -
      integral TS71.MellinJackson.rightClosedBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi) := by
        rw [(TS76.MellinJackson.right_rightClosedBranchMeasure_eq_interval phi).symm]

/-- Concrete discharge of the TS73 affine branch IPP contract. -/
def triangleSplineIPPAffineBranchContract :
    TS73.MellinJackson.TriangleSplineIPPAffineBranchContract where
  left_affine_ipp := by
    intro phi
    exact left_affine_ipp phi
  right_affine_ipp := by
    intro phi
    exact right_affine_ipp phi

/-- Target proposition for the concrete TS77 affine branch IPP proof. -/
def TriangleSplineIPPAffineBranchProofTarget : Prop :=
  Nonempty TS73.MellinJackson.TriangleSplineIPPAffineBranchContract

/-- TS77 discharges the TS73 affine branch IPP target. -/
theorem triangleSplineIPPAffineBranchContractTarget :
    TS73.MellinJackson.TriangleSplineIPPAffineBranchContractTarget :=
  Nonempty.intro triangleSplineIPPAffineBranchContract

/-- TS77 also provides its local proof target. -/
theorem triangleSplineIPPAffineBranchProofTarget :
    TriangleSplineIPPAffineBranchProofTarget :=
  Nonempty.intro triangleSplineIPPAffineBranchContract

end MellinJackson
end TS77
