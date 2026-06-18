import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS166.TriangleSplineFourierIdentificationReduction

namespace TS167
namespace Goldbach

open MeasureTheory

/-!
# TS167 - Triangle Spline Convolution Route Probe

TS166 fixes the exact Fourier-identification target for the triangle spline.
This sprint probes the primary proof route: represent the triangle spline as
the self-convolution of a centered unit-width box.

The sprint defines the box function, its complex lift, and its manual Bochner
self-convolution.  It then compiles the exact local statements needed by this
route and proves that, if those statements are supplied, they imply the TS166
Fourier-identification statement.

No box integrability theorem, convolution identity, Fourier-convolution
exchange theorem, box Fourier evaluation, Plancherel theorem, or explicit
formula is claimed here.
-/

/-- Current status of the convolution route. -/
inductive ConvolutionRouteStatus where
  /-- The route has been stated and type-checked, but its analytic facts remain open. -/
  | apiProbe
  /-- Future status: Mathlib's convolution/Fourier API is usable for this route. -/
  | convolutionAvailable
  /-- Future status: the route is too hostile and TS168 should be used instead. -/
  | fallbackRequired
  deriving DecidableEq, Repr

/-- Centered unit-width box: indicator of `[-1/2, 1/2]`. -/
noncomputable def unitBoxFunction
    (x : Real) :
    Real :=
  if -(1 / 2 : Real) <= x /\ x <= (1 / 2 : Real) then 1 else 0

/-- Complex-valued box function for Mathlib Fourier. -/
noncomputable def unitBoxAsComplex
    (x : Real) :
    Complex :=
  (unitBoxFunction x : Complex)

/-- The non-squared scaled sinc profile expected as the Fourier transform of the box. -/
noncomputable def scaledSinc
    (scale xi : Real) :
    Real :=
  if scale * xi = 0 then 1 else Real.sin (scale * xi) / (scale * xi)

/-- The square of `scaledSinc` is the TS164 squared-sinc profile. -/
theorem scaledSinc_mul_self_eq_scaledSincSq
    (scale xi : Real) :
    (scaledSinc scale xi : Complex) *
        (scaledSinc scale xi : Complex) =
      (TS164.Goldbach.scaledSincSq scale xi : Complex) := by
  unfold scaledSinc TS164.Goldbach.scaledSincSq
  by_cases h : scale * xi = 0
  case pos =>
    simp [h]
  case neg =>
    simp [h, pow_two]

/--
Manual Bochner self-convolution of the centered box.

This avoids committing to a high-level Mathlib convolution API before TS167 has
probed which API shape is best suited to the discontinuous box.
-/
noncomputable def unitBoxSelfConvolution
    (x : Real) :
    Complex :=
  integral (volume : Measure Real)
    (fun y : Real => unitBoxAsComplex y * unitBoxAsComplex (x - y))

/--
Spatial convolution identity needed for the convolution route.

TS167 only states this identity.
-/
def BoxConvolutionEqualsTriangleSplineStatement : Prop :=
  forall x : Real,
    unitBoxSelfConvolution x =
      TS166.Goldbach.triangleSplineAsComplex x

/--
Box Fourier evaluation needed for the convolution route.

The expected profile is the non-squared scaled sinc at the Mathlib scale
selected in TS165.
-/
def BoxFourierEvaluationStatement : Prop :=
  forall xi : Real,
    Real.fourierIntegral unitBoxAsComplex xi =
      (scaledSinc TS165.Goldbach.mathlibFourierTargetScale xi : Complex)

/--
Fourier-convolution exchange specialized to the box self-convolution.

This is the core Mathlib API obligation for the primary route.
-/
def BoxFourierConvolutionExchangeStatement : Prop :=
  forall xi : Real,
    Real.fourierIntegral unitBoxSelfConvolution xi =
      Real.fourierIntegral unitBoxAsComplex xi *
        Real.fourierIntegral unitBoxAsComplex xi

/-- The convolution route, if discharged, implies the TS166 Fourier statement. -/
def ConvolutionRouteImpliesTS166Statement : Prop :=
  BoxConvolutionEqualsTriangleSplineStatement ->
    BoxFourierEvaluationStatement ->
      BoxFourierConvolutionExchangeStatement ->
        TS166.Goldbach.TriangleSplineFourierIdentificationStatement

/--
The three compiled local statements are sufficient for the TS166 target.

This theorem does not prove any analytic statement.  It proves that the route
is wired correctly: spatial convolution plus box Fourier evaluation plus
Fourier-convolution exchange yields the exact TS166 statement.
-/
theorem convolutionRoute_implies_ts166 :
    ConvolutionRouteImpliesTS166Statement := by
  intro h_spatial h_box h_exchange xi
  have h_fun :
      unitBoxSelfConvolution =
        TS166.Goldbach.triangleSplineAsComplex := by
    funext x
    exact h_spatial x
  unfold TS166.Goldbach.triangleSplineMathlibFourier
  unfold TS166.Goldbach.triangleSplineScaledSincCandidate
  calc
    Real.fourierIntegral TS166.Goldbach.triangleSplineAsComplex xi =
        Real.fourierIntegral unitBoxSelfConvolution xi := by
          rw [<- h_fun]
    _ =
        Real.fourierIntegral unitBoxAsComplex xi *
          Real.fourierIntegral unitBoxAsComplex xi := by
          exact h_exchange xi
    _ =
        (scaledSinc TS165.Goldbach.mathlibFourierTargetScale xi : Complex) *
          (scaledSinc TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
          rw [h_box xi]
    _ =
        (TS164.Goldbach.scaledSincSq
          TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
          exact scaledSinc_mul_self_eq_scaledSincSq
            TS165.Goldbach.mathlibFourierTargetScale xi

/-- Ledger for the TS167 convolution-route probe. -/
structure TriangleSplineConvolutionRouteProbeLedger where
  status :
    ConvolutionRouteStatus

  status_eq :
    status = ConvolutionRouteStatus.apiProbe

  box_function_defined :
    True

  box_complex_lift_defined :
    True

  scaled_sinc_defined :
    True

  box_self_convolution_defined :
    True

  scaled_sinc_square_bridge :
    forall xi : Real,
      (scaledSinc TS165.Goldbach.mathlibFourierTargetScale xi : Complex) *
          (scaledSinc TS165.Goldbach.mathlibFourierTargetScale xi : Complex) =
        (TS164.Goldbach.scaledSincSq
          TS165.Goldbach.mathlibFourierTargetScale xi : Complex)

  spatial_convolution_statement :
    Prop

  spatial_convolution_statement_eq :
    spatial_convolution_statement =
      BoxConvolutionEqualsTriangleSplineStatement

  box_fourier_statement :
    Prop

  box_fourier_statement_eq :
    box_fourier_statement =
      BoxFourierEvaluationStatement

  fourier_exchange_statement :
    Prop

  fourier_exchange_statement_eq :
    fourier_exchange_statement =
      BoxFourierConvolutionExchangeStatement

  route_implication_statement :
    Prop

  route_implication_statement_eq :
    route_implication_statement =
      ConvolutionRouteImpliesTS166Statement

  route_implication_proof :
    ConvolutionRouteImpliesTS166Statement

  box_integrability_not_claimed :
    True

  convolution_identity_not_claimed :
    True

  box_fourier_evaluation_not_claimed :
    True

  fourier_exchange_not_claimed :
    True

  ts166_identification_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS167 convolution-route probe ledger. -/
noncomputable def triangleSplineConvolutionRouteProbeLedger :
    TriangleSplineConvolutionRouteProbeLedger where
  status := ConvolutionRouteStatus.apiProbe
  status_eq := rfl
  box_function_defined := True.intro
  box_complex_lift_defined := True.intro
  scaled_sinc_defined := True.intro
  box_self_convolution_defined := True.intro
  scaled_sinc_square_bridge := by
    intro xi
    exact scaledSinc_mul_self_eq_scaledSincSq
      TS165.Goldbach.mathlibFourierTargetScale xi
  spatial_convolution_statement := BoxConvolutionEqualsTriangleSplineStatement
  spatial_convolution_statement_eq := rfl
  box_fourier_statement := BoxFourierEvaluationStatement
  box_fourier_statement_eq := rfl
  fourier_exchange_statement := BoxFourierConvolutionExchangeStatement
  fourier_exchange_statement_eq := rfl
  route_implication_statement := ConvolutionRouteImpliesTS166Statement
  route_implication_statement_eq := rfl
  route_implication_proof := convolutionRoute_implies_ts166
  box_integrability_not_claimed := True.intro
  convolution_identity_not_claimed := True.intro
  box_fourier_evaluation_not_claimed := True.intro
  fourier_exchange_not_claimed := True.intro
  ts166_identification_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS167. -/
def TriangleSplineConvolutionRouteProbeTarget : Prop :=
  Nonempty TriangleSplineConvolutionRouteProbeLedger

/-- The TS167 convolution-route probe target is populated. -/
theorem triangleSplineConvolutionRouteProbeTarget :
    TriangleSplineConvolutionRouteProbeTarget :=
  Nonempty.intro triangleSplineConvolutionRouteProbeLedger

end Goldbach
end TS167
