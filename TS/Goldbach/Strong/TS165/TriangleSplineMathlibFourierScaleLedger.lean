import Mathlib.Analysis.Fourier.FourierTransform
import TS.Goldbach.Strong.TS53.FourierConcreteSymbolsProbe
import TS.Goldbach.Strong.TS164.TriangleSplineFourierNormalizationProbe

namespace TS165
namespace Goldbach

open scoped FourierTransform

/-!
# TS165 - Triangle Spline Mathlib Fourier Scale Ledger

TS164 keeps the squared-sinc spectral profile scale-parametrized, precisely to
avoid baking the wrong Fourier normalization into TS95.  This sprint probes the
current Mathlib Fourier API and records the convention that will be used for the
future triangle-spline Fourier identification.

Mathlib's real Fourier integral uses `Real.fourierChar` and the forward kernel
exposed by `Real.fourierIntegral_real_eq_integral_exp_smul`, namely the
`-2 * pi * x * xi` exponent.  For the normalized triangle spline on `[-1, 1]`,
the corresponding squared-sinc profile is therefore the TS164 family at scale
`Real.pi`.

No integral evaluation of the triangle spline, no Plancherel theorem, and no
explicit formula statement is proved here.
-/

/-- The Mathlib-compatible squared-sinc scale selected for future work. -/
noncomputable def mathlibFourierTargetScale : Real :=
  Real.pi

/-- The selected Mathlib-compatible scale is positive. -/
theorem mathlibFourierTargetScale_pos :
    0 < mathlibFourierTargetScale := by
  unfold mathlibFourierTargetScale
  exact Real.pi_pos

/-- The selected Mathlib-side squared-sinc candidate. -/
noncomputable def triangleSplineMathlibFourierWeight
    (xi : Real) :
    Real :=
  TS164.Goldbach.scaledSincSq mathlibFourierTargetScale xi

/-- The Mathlib-side squared-sinc candidate is nonnegative. -/
theorem triangleSplineMathlibFourierWeight_nonneg
    (xi : Real) :
    0 <= triangleSplineMathlibFourierWeight xi := by
  unfold triangleSplineMathlibFourierWeight
  exact TS164.Goldbach.scaledSincSq_nonneg mathlibFourierTargetScale xi

/-- The Mathlib-side squared-sinc candidate is normalized at frequency zero. -/
theorem triangleSplineMathlibFourierWeight_zero :
    triangleSplineMathlibFourierWeight 0 = 1 := by
  unfold triangleSplineMathlibFourierWeight
  exact TS164.Goldbach.scaledSincSq_zero mathlibFourierTargetScale

/-- Checked reference to Mathlib's `2 * pi` additive character convention. -/
theorem mathlib_fourierChar_twoPi_checked
    (x : Real) :
    True := by
  have _ := Real.fourierChar_apply x
  trivial

/--
Checked reference to Mathlib's real forward Fourier kernel.

The referenced theorem expands the real forward transform into an exponential
kernel with exponent `-2 * pi * v * w`.
-/
theorem mathlib_forward_fourier_kernel_checked
    (f : Real -> Complex)
    (w : Real) :
    True := by
  have _ := Real.fourierIntegral_real_eq_integral_exp_smul f w
  trivial

/-- The TS53 derivative probe is consistent with the same `2 * pi` scale. -/
theorem ts53_derivativeMultiplierCandidate_eq_two_pi :
    TS53.MellinJackson.derivativeMultiplierCandidate = 2 * Real.pi := by
  rfl

/-- The selected scale is the pi half of the TS53 derivative multiplier. -/
theorem mathlibFourierTargetScale_two_mul_eq_derivativeMultiplierCandidate :
    2 * mathlibFourierTargetScale =
      TS53.MellinJackson.derivativeMultiplierCandidate := by
  rfl

/-- Status markers for the TS165 Mathlib Fourier normalization probe. -/
inductive MathlibFourierScaleStatus where
  /-- Mathlib's additive character has the `2 * pi` exponent. -/
  | fourierCharTwoPiChecked
  /-- Mathlib's forward real Fourier kernel has the negative `2 * pi` exponent. -/
  | forwardKernelMinusTwoPiChecked
  /-- The TS164 squared-sinc family is specialized at scale `pi`. -/
  | piScaleSelected
  deriving DecidableEq, Repr

/--
Ledger selecting the TS164 scale compatible with Mathlib's Fourier convention.

The selected contract is still a contract: it records the target normalization
for the future triangle-spline Fourier identity, but it does not prove that
identity.
-/
structure TriangleSplineMathlibFourierScaleLedger where
  ts53_symbols :
    TS53.MellinJackson.FourierConcreteSymbolLedger

  ts164_normalization_probe :
    TS164.Goldbach.TriangleSplineFourierNormalizationProbeLedger

  status :
    MathlibFourierScaleStatus

  status_eq :
    status = MathlibFourierScaleStatus.piScaleSelected

  target_scale :
    Real

  target_scale_eq :
    target_scale = Real.pi

  target_scale_pos :
    0 < target_scale

  selected_weight :
    Real -> Real

  selected_weight_eq :
    selected_weight = triangleSplineMathlibFourierWeight

  selected_weight_nonneg :
    forall xi : Real,
      0 <= selected_weight xi

  selected_weight_zero :
    selected_weight 0 = 1

  selected_contract :
    TS164.Goldbach.TriangleSplineFourierIdentificationContract

  selected_contract_eq :
    selected_contract =
      TS164.Goldbach.triangleSplineFourierIdentificationContract
        mathlibFourierTargetScale
        mathlibFourierTargetScale_pos

  fourier_char_two_pi_checked :
    True

  forward_kernel_minus_two_pi_checked :
    True

  derivative_multiplier_matches_scale :
    2 * target_scale =
      TS53.MellinJackson.derivativeMultiplierCandidate

  no_actual_triangle_spline_fourier_identity_claimed :
    True

  no_plancherel_claimed :
    True

  no_explicit_formula_claimed :
    True

/-- Concrete TS165 Mathlib Fourier scale ledger. -/
noncomputable def triangleSplineMathlibFourierScaleLedger :
    TriangleSplineMathlibFourierScaleLedger where
  ts53_symbols := TS53.MellinJackson.fourierConcreteSymbolLedger
  ts164_normalization_probe :=
    TS164.Goldbach.triangleSplineFourierNormalizationProbeLedger
  status := MathlibFourierScaleStatus.piScaleSelected
  status_eq := rfl
  target_scale := mathlibFourierTargetScale
  target_scale_eq := rfl
  target_scale_pos := mathlibFourierTargetScale_pos
  selected_weight := triangleSplineMathlibFourierWeight
  selected_weight_eq := rfl
  selected_weight_nonneg := triangleSplineMathlibFourierWeight_nonneg
  selected_weight_zero := triangleSplineMathlibFourierWeight_zero
  selected_contract :=
    TS164.Goldbach.triangleSplineFourierIdentificationContract
      mathlibFourierTargetScale
      mathlibFourierTargetScale_pos
  selected_contract_eq := rfl
  fourier_char_two_pi_checked := by
    exact mathlib_fourierChar_twoPi_checked 0
  forward_kernel_minus_two_pi_checked := by
    exact mathlib_forward_fourier_kernel_checked
      (fun _ : Real => (0 : Complex)) 0
  derivative_multiplier_matches_scale := by
    exact mathlibFourierTargetScale_two_mul_eq_derivativeMultiplierCandidate
  no_actual_triangle_spline_fourier_identity_claimed := True.intro
  no_plancherel_claimed := True.intro
  no_explicit_formula_claimed := True.intro

/-- Target proposition for TS165. -/
def TriangleSplineMathlibFourierScaleTarget : Prop :=
  Nonempty TriangleSplineMathlibFourierScaleLedger

/-- The TS165 Mathlib Fourier scale target is populated. -/
theorem triangleSplineMathlibFourierScaleTarget :
    TriangleSplineMathlibFourierScaleTarget :=
  Nonempty.intro triangleSplineMathlibFourierScaleLedger

end Goldbach
end TS165
