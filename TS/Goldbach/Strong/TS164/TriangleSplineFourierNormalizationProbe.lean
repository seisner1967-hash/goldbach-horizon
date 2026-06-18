import Mathlib.Tactic
import TS.Goldbach.Strong.TS163.TriangleSplineFourierWeightLedger

namespace TS164
namespace Goldbach

/-!
# TS164 - Triangle Spline Fourier Normalization Probe

TS163 installs a nonnegative squared-sinc spectral-weight candidate, but it
intentionally does not identify that candidate with Mathlib's Fourier transform
of the triangle spline.  The next immediate risk is a wrong Fourier
normalization constant.

This sprint therefore introduces a scale-parametrized squared-sinc family.  It
proves the scale-independent positivity and zero-frequency normalization, shows
that the TS163 candidate is the unit-scale member of the family, and records
the future Mathlib Fourier-identification contract.
-/

/--
Scale-parametrized squared sinc profile.

The parameter `scale` is left free so the later Mathlib Fourier API binding can
choose whether the correct argument is `xi`, `xi / 2`, `Real.pi * xi`,
`2 * Real.pi * xi`, or another normalization-compatible expression.
-/
noncomputable def scaledSincSq
    (scale xi : Real) :
    Real :=
  if scale * xi = 0 then 1
  else (Real.sin (scale * xi) / (scale * xi)) ^ 2

/-- Every scaled squared-sinc profile is nonnegative. -/
theorem scaledSincSq_nonneg
    (scale xi : Real) :
    0 <= scaledSincSq scale xi := by
  unfold scaledSincSq
  by_cases h : scale * xi = 0
  case pos =>
    simp [h]
  case neg =>
    simp [h, sq_nonneg]

/-- Every scaled squared-sinc profile is normalized to `1` at frequency `0`. -/
theorem scaledSincSq_zero
    (scale : Real) :
    scaledSincSq scale 0 = 1 := by
  simp [scaledSincSq]

/-- The TS163 spectral candidate is the unit-scale member of the scaled family. -/
theorem scaledSincSq_one_eq_triangleSplineFourierWeight :
    scaledSincSq 1 = TS163.Goldbach.triangleSplineFourierWeight := by
  funext xi
  simp [scaledSincSq, TS163.Goldbach.triangleSplineFourierWeight]

/-- Lift a scaled squared-sinc profile to complex spectral parameters. -/
noncomputable def scaledTriangleSplineSpectralWeight
    (scale : Real)
    (rho : Complex) :
    Real :=
  scaledSincSq scale rho.re

/-- The scaled complex-parameter spectral weight is nonnegative. -/
theorem scaledTriangleSplineSpectralWeight_nonneg
    (scale : Real)
    (rho : Complex) :
    0 <= scaledTriangleSplineSpectralWeight scale rho := by
  exact scaledSincSq_nonneg scale rho.re

/-- TS94 trace kernel using the triangle spline and a scaled spectral weight. -/
noncomputable def scaledTriangleSplineTraceKernel
    (scale : Real) :
    TS94.Goldbach.TraceKernel where
  kernel := TS42.MellinJackson.triangleSpline
  spectralWeight := scaledTriangleSplineSpectralWeight scale

/-- A scaled spectral weight supplies the TS94 nonnegativity field. -/
theorem scaledTriangleSplineTraceKernel_spectralWeight_nonneg
    (scale : Real)
    (rho : Complex) :
    0 <= (scaledTriangleSplineTraceKernel scale).spectralWeight rho := by
  exact scaledTriangleSplineSpectralWeight_nonneg scale rho

/--
TS94 kernel-data ledger for any scaled squared-sinc spectral-weight candidate.

As in TS163, normalization, decay, and spectral-sum convergence are still the
current TS94 local contracts.
-/
noncomputable def scaledTriangleSplineTraceKernelSpectralDataLedger
    (scale : Real) :
    TS94.Goldbach.TraceKernelSpectralDataLedger where
  traceKernel := scaledTriangleSplineTraceKernel scale
  kernel_nonneg := by
    intro t
    exact TS162.Goldbach.triangleSpline_nonneg t
  spectralWeight_nonneg := by
    intro rho
    exact scaledTriangleSplineTraceKernel_spectralWeight_nonneg scale rho
  normalization := True.intro
  decay := True.intro
  spectral_sum_converges := True.intro

/--
Contract for a future Fourier identification of the triangle spline.

The current sprint proves the algebraic shape of the candidate family.  The
actual identification with `Real.fourierIntegral`, including the correct scale,
is kept as an explicit contract.
-/
structure TriangleSplineFourierIdentificationContract where
  scale :
    Real

  scale_pos :
    0 < scale

  candidate_weight :
    Real -> Real

  candidate_weight_eq :
    candidate_weight = scaledSincSq scale

  candidate_nonneg :
    forall xi : Real,
      0 <= candidate_weight xi

  candidate_zero :
    candidate_weight 0 = 1

  spectral_weight :
    Complex -> Real

  spectral_weight_eq :
    spectral_weight = scaledTriangleSplineSpectralWeight scale

  spectral_weight_nonneg :
    forall rho : Complex,
      0 <= spectral_weight rho

  trace_kernel_ledger :
    TS94.Goldbach.TraceKernelSpectralDataLedger

  fourier_identification_obligation :
    True

  mathlib_normalization_obligation :
    True

  fourier_identity_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  normalization_constant_not_fixed :
    True

/-- Build the Fourier-identification contract for any positive scale. -/
noncomputable def triangleSplineFourierIdentificationContract
    (scale : Real)
    (hscale : 0 < scale) :
    TriangleSplineFourierIdentificationContract where
  scale := scale
  scale_pos := hscale
  candidate_weight := scaledSincSq scale
  candidate_weight_eq := rfl
  candidate_nonneg := scaledSincSq_nonneg scale
  candidate_zero := scaledSincSq_zero scale
  spectral_weight := scaledTriangleSplineSpectralWeight scale
  spectral_weight_eq := rfl
  spectral_weight_nonneg := scaledTriangleSplineSpectralWeight_nonneg scale
  trace_kernel_ledger := scaledTriangleSplineTraceKernelSpectralDataLedger scale
  fourier_identification_obligation := True.intro
  mathlib_normalization_obligation := True.intro
  fourier_identity_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  normalization_constant_not_fixed := True.intro

/-- Unit-scale contract, recording the current TS163 convention as one option. -/
noncomputable def triangleSplineUnitScaleFourierIdentificationContract :
    TriangleSplineFourierIdentificationContract :=
  triangleSplineFourierIdentificationContract 1 (by norm_num)

/-- Ledger for the Fourier-normalization probe. -/
structure TriangleSplineFourierNormalizationProbeLedger where
  ts163_weight :
    TS163.Goldbach.TriangleSplineFourierWeightLedger

  unit_scale_recovers_ts163 :
    scaledSincSq 1 = TS163.Goldbach.triangleSplineFourierWeight

  unit_scale_contract :
    TriangleSplineFourierIdentificationContract

  unit_scale_contract_eq :
    unit_scale_contract =
      triangleSplineUnitScaleFourierIdentificationContract

  arbitrary_positive_scale_contract :
    forall scale : Real,
      0 < scale -> TriangleSplineFourierIdentificationContract

  no_preferred_scale_selected :
    True

  fourier_identity_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS164 Fourier-normalization probe ledger. -/
noncomputable def triangleSplineFourierNormalizationProbeLedger :
    TriangleSplineFourierNormalizationProbeLedger where
  ts163_weight := TS163.Goldbach.triangleSplineFourierWeightLedger
  unit_scale_recovers_ts163 := scaledSincSq_one_eq_triangleSplineFourierWeight
  unit_scale_contract := triangleSplineUnitScaleFourierIdentificationContract
  unit_scale_contract_eq := rfl
  arbitrary_positive_scale_contract := by
    intro scale hscale
    exact triangleSplineFourierIdentificationContract scale hscale
  no_preferred_scale_selected := True.intro
  fourier_identity_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS164. -/
def TriangleSplineFourierNormalizationProbeTarget : Prop :=
  Nonempty TriangleSplineFourierNormalizationProbeLedger

/-- The TS164 Fourier-normalization probe target is populated. -/
theorem triangleSplineFourierNormalizationProbeTarget :
    TriangleSplineFourierNormalizationProbeTarget :=
  Nonempty.intro triangleSplineFourierNormalizationProbeLedger

end Goldbach
end TS164
