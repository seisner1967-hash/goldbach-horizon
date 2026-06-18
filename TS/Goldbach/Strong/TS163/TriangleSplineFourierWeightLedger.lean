import Mathlib.Tactic
import TS.Goldbach.Strong.TS162.TriangleSplineTraceKernelInstantiation

namespace TS163
namespace Goldbach

/-!
# TS163 - Triangle Spline Fourier Weight Ledger

TS162 installs the triangle spline as a concrete TS94 real trace kernel, using
a zero spectral weight to keep the first spectral-pivot sprint fail-closed.
This sprint replaces that zero placeholder by a natural nonnegative
Fourier-side candidate: a squared sinc profile on the real frequency
coordinate.

No theorem in this file identifies the candidate with the actual Mathlib
Fourier transform of the triangle spline.  That identification, Plancherel,
and the Riemann-von Mangoldt explicit formula remain explicit future
obligations.
-/

/--
Squared sinc candidate for the triangle-spline Fourier weight.

The normalization is intentionally left at the API level.  Future Fourier work
will decide whether the argument should be scaled by `Real.pi`, `2 * Real.pi`,
or the Mathlib normalization fixed by TS41/TS53.
-/
noncomputable def triangleSplineFourierWeight
    (xi : Real) :
    Real :=
  if xi = 0 then 1 else (Real.sin xi / xi) ^ 2

/-- The squared sinc candidate is nonnegative. -/
theorem triangleSplineFourierWeight_nonneg
    (xi : Real) :
    0 <= triangleSplineFourierWeight xi := by
  unfold triangleSplineFourierWeight
  by_cases hxi : xi = 0
  case pos =>
    simp [hxi]
  case neg =>
    simp [hxi, sq_nonneg]

/-- The squared sinc candidate is normalized to `1` at frequency `0`. -/
theorem triangleSplineFourierWeight_zero :
    triangleSplineFourierWeight 0 = 1 := by
  simp [triangleSplineFourierWeight]

/-- The squared sinc candidate is evaluated on complex parameters by real part. -/
noncomputable def triangleSplineSpectralWeight
    (rho : Complex) :
    Real :=
  triangleSplineFourierWeight rho.re

/-- The complex-parameter spectral-weight candidate is nonnegative. -/
theorem triangleSplineSpectralWeight_nonneg
    (rho : Complex) :
    0 <= triangleSplineSpectralWeight rho := by
  exact triangleSplineFourierWeight_nonneg rho.re

/--
TS94 trace kernel using the TS42 triangle spline and the nonnegative sinc-square
spectral-weight candidate.
-/
noncomputable def triangleSplineFourierTraceKernel :
    TS94.Goldbach.TraceKernel where
  kernel := TS42.MellinJackson.triangleSpline
  spectralWeight := triangleSplineSpectralWeight

/-- The nonnegative sinc-square candidate supplies the TS94 spectral field. -/
theorem triangleSplineFourierTraceKernel_spectralWeight_nonneg
    (rho : Complex) :
    0 <= triangleSplineFourierTraceKernel.spectralWeight rho := by
  exact triangleSplineSpectralWeight_nonneg rho

/--
Concrete TS94 kernel-data ledger with the triangle spline and nonzero
sinc-square spectral-weight candidate.

The real-kernel side is inherited from TS162.  The normalization, decay, and
spectral-sum convergence fields are still the TS94 local contracts.
-/
noncomputable def triangleSplineFourierTraceKernelSpectralDataLedger :
    TS94.Goldbach.TraceKernelSpectralDataLedger where
  traceKernel := triangleSplineFourierTraceKernel
  kernel_nonneg := by
    intro t
    exact TS162.Goldbach.triangleSpline_nonneg t
  spectralWeight_nonneg := by
    intro rho
    exact triangleSplineFourierTraceKernel_spectralWeight_nonneg rho
  normalization := True.intro
  decay := True.intro
  spectral_sum_converges := True.intro

/-- Target proposition for the TS163 nonzero spectral-weight kernel ledger. -/
def TriangleSplineFourierTraceKernelSpectralDataLedgerTarget : Prop :=
  Nonempty TS94.Goldbach.TraceKernelSpectralDataLedger

/-- The nonzero spectral-weight candidate supplies the TS94 ledger target. -/
theorem triangleSplineFourierTraceKernelSpectralDataLedgerTarget :
    TriangleSplineFourierTraceKernelSpectralDataLedgerTarget :=
  Nonempty.intro triangleSplineFourierTraceKernelSpectralDataLedger

/-- The TS163 ledger supplies the coarser TS94 kernel-data target. -/
theorem triangleSplineFourierTraceKernelSpectralDataTarget :
    TS94.Goldbach.TraceKernelSpectralDataTarget :=
  TS94.Goldbach.traceKernelSpectralDataTarget_of_ledgerTarget
    triangleSplineFourierTraceKernelSpectralDataLedgerTarget

/-- Named TS163 status markers. -/
inductive TriangleSplineFourierWeightStatus where
  | realKernelInheritedFromTS162
  | sincSquareCandidateInstalled
  | fourierIdentificationStillOpen
  deriving DecidableEq, Repr

/--
Ledger for the TS163 Fourier-weight candidate.

This is a functional bridge, not a Fourier theorem: it records a nonnegative
candidate spectral weight and names the remaining analytic contracts.
-/
structure TriangleSplineFourierWeightLedger where
  ts162_kernel :
    TS162.Goldbach.TriangleSplineTraceKernelInstantiationLedger

  status :
    TriangleSplineFourierWeightStatus

  status_eq :
    status =
      TriangleSplineFourierWeightStatus.sincSquareCandidateInstalled

  fourier_weight :
    Real -> Real

  fourier_weight_eq :
    fourier_weight = triangleSplineFourierWeight

  fourier_weight_nonneg :
    forall xi : Real,
      0 <= fourier_weight xi

  fourier_weight_zero :
    fourier_weight 0 = 1

  spectral_weight :
    Complex -> Real

  spectral_weight_eq :
    spectral_weight = triangleSplineSpectralWeight

  spectral_weight_nonneg :
    forall rho : Complex,
      0 <= spectral_weight rho

  trace_kernel_ledger :
    TS94.Goldbach.TraceKernelSpectralDataLedger

  trace_kernel_target :
    TS94.Goldbach.TraceKernelSpectralDataTarget

  fourier_transform_identification_required :
    True

  plancherel_required :
    True

  explicit_formula_required :
    True

  no_claim_of_actual_fourier_transform :
    True

  no_claim_of_plancherel :
    True

  no_claim_of_explicit_formula :
    True

/-- Concrete TS163 Fourier-weight candidate ledger. -/
noncomputable def triangleSplineFourierWeightLedger :
    TriangleSplineFourierWeightLedger where
  ts162_kernel := TS162.Goldbach.triangleSplineTraceKernelInstantiationLedger
  status := TriangleSplineFourierWeightStatus.sincSquareCandidateInstalled
  status_eq := rfl
  fourier_weight := triangleSplineFourierWeight
  fourier_weight_eq := rfl
  fourier_weight_nonneg := triangleSplineFourierWeight_nonneg
  fourier_weight_zero := triangleSplineFourierWeight_zero
  spectral_weight := triangleSplineSpectralWeight
  spectral_weight_eq := rfl
  spectral_weight_nonneg := triangleSplineSpectralWeight_nonneg
  trace_kernel_ledger := triangleSplineFourierTraceKernelSpectralDataLedger
  trace_kernel_target := triangleSplineFourierTraceKernelSpectralDataTarget
  fourier_transform_identification_required := True.intro
  plancherel_required := True.intro
  explicit_formula_required := True.intro
  no_claim_of_actual_fourier_transform := True.intro
  no_claim_of_plancherel := True.intro
  no_claim_of_explicit_formula := True.intro

/-- Target proposition for TS163. -/
def TriangleSplineFourierWeightTarget : Prop :=
  Nonempty TriangleSplineFourierWeightLedger

/-- The TS163 Fourier-weight candidate target is populated. -/
theorem triangleSplineFourierWeightTarget :
    TriangleSplineFourierWeightTarget :=
  Nonempty.intro triangleSplineFourierWeightLedger

end Goldbach
end TS163
