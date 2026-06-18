import Mathlib.Tactic
import TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
import TS.Goldbach.Strong.TS161.PhiPremortemSpectralPivotLedger

namespace TS162
namespace Goldbach

/-!
# TS162 - Triangle Spline Trace Kernel Instantiation

TS161 opens the spectral pivot after the phi-denominator pre-mortem.  This
sprint starts the pivot on the lowest-risk concrete front: it packages the
already defined triangle spline from TS42 as a TS94 trace kernel.

The spectral weight is deliberately the zero weight.  This makes the TS94
nonnegativity field concrete without claiming a Fourier transform, Plancherel,
or a Riemann-von Mangoldt explicit formula.  Those remain future TS95-side
analytic obligations.
-/

/-- The triangle spline is pointwise nonnegative. -/
theorem triangleSpline_nonneg
    (x : Real) :
    0 <= TS42.MellinJackson.triangleSpline x := by
  unfold TS42.MellinJackson.triangleSpline
  by_cases hs : -1 <= x /\ x <= 1
  case pos =>
    have h_abs : |x| <= 1 := abs_le.mpr hs
    simp [hs]
    linarith
  case neg =>
    simp [hs]

/-- The triangle spline has value `1` at the origin. -/
theorem triangleSpline_zero :
    TS42.MellinJackson.triangleSpline 0 = 1 := by
  rw [TS56.MellinJackson.triangleSpline_eq_one_sub_of_right]
  all_goals norm_num

/-- The triangle spline vanishes at and outside the boundary `|x| = 1`. -/
theorem triangleSpline_eq_zero_of_one_le_abs
    {x : Real}
    (hx : 1 <= |x|) :
    TS42.MellinJackson.triangleSpline x = 0 := by
  unfold TS42.MellinJackson.triangleSpline
  by_cases hs : -1 <= x /\ x <= 1
  case pos =>
    have h_abs_le : |x| <= 1 := abs_le.mpr hs
    have h_abs : |x| = 1 := le_antisymm h_abs_le hx
    simp [hs, h_abs]
  case neg =>
    simp [hs]

/-- TS94 trace kernel whose real kernel is the concrete triangle spline. -/
noncomputable def triangleSplineTraceKernel :
    TS94.Goldbach.TraceKernel where
  kernel := TS42.MellinJackson.triangleSpline
  spectralWeight := fun _rho => 0

/-- The zero spectral weight is nonnegative. -/
theorem triangleSplineTraceKernel_spectralWeight_nonneg
    (rho : Complex) :
    0 <= triangleSplineTraceKernel.spectralWeight rho := by
  simp [triangleSplineTraceKernel]

/--
Concrete TS94 kernel-data ledger supplied by the triangle spline.

Only the real-kernel nonnegativity and the nonnegative placeholder spectral
weight are substantive here.  TS94 currently records normalization, decay, and
spectral-sum convergence as local contracts, so those fields are discharged by
their present definitions.
-/
noncomputable def triangleSplineTraceKernelSpectralDataLedger :
    TS94.Goldbach.TraceKernelSpectralDataLedger where
  traceKernel := triangleSplineTraceKernel
  kernel_nonneg := by
    intro t
    exact triangleSpline_nonneg t
  spectralWeight_nonneg := by
    intro rho
    exact triangleSplineTraceKernel_spectralWeight_nonneg rho
  normalization := True.intro
  decay := True.intro
  spectral_sum_converges := True.intro

/-- Target proposition for the concrete triangle-spline kernel ledger. -/
def TriangleSplineTraceKernelSpectralDataLedgerTarget : Prop :=
  Nonempty TS94.Goldbach.TraceKernelSpectralDataLedger

/-- The triangle spline supplies the concrete TS94 kernel-data ledger target. -/
theorem triangleSplineTraceKernelSpectralDataLedgerTarget :
    TriangleSplineTraceKernelSpectralDataLedgerTarget :=
  Nonempty.intro triangleSplineTraceKernelSpectralDataLedger

/-- The triangle-spline ledger supplies the coarser TS94 kernel-data target. -/
theorem triangleSplineTraceKernelSpectralDataTarget :
    TS94.Goldbach.TraceKernelSpectralDataTarget :=
  TS94.Goldbach.traceKernelSpectralDataTarget_of_ledgerTarget
    triangleSplineTraceKernelSpectralDataLedgerTarget

/-- Named statuses for the spectral pivot activation. -/
inductive SpectralPivotActivationStatus where
  | phiPremortemArchived
  | triangleSplineKernelInstantiated
  | explicitFormulaStillRoadmap
  deriving DecidableEq, Repr

/--
Ledger recording the first concrete step of the spectral pivot.

It keeps TS161's phi pre-mortem in scope, installs the triangle spline as the
TS94 trace kernel, and explicitly leaves TS95 as a roadmap rather than a proved
explicit formula.
-/
structure TriangleSplineTraceKernelInstantiationLedger where
  phi_premortem :
    TS161.Goldbach.PhiPremortemSpectralPivotLedger

  activation_status :
    SpectralPivotActivationStatus

  activation_status_eq :
    activation_status =
      SpectralPivotActivationStatus.triangleSplineKernelInstantiated

  origin_value :
    TS42.MellinJackson.triangleSpline 0 = 1

  kernel_nonnegative :
    forall x : Real,
      0 <= TS42.MellinJackson.triangleSpline x

  kernel_vanishes_outside_unit_abs :
    forall x : Real,
      1 <= |x| -> TS42.MellinJackson.triangleSpline x = 0

  trace_kernel :
    TS94.Goldbach.TraceKernel

  trace_kernel_eq :
    trace_kernel = triangleSplineTraceKernel

  trace_kernel_ledger :
    TS94.Goldbach.TraceKernelSpectralDataLedger

  trace_kernel_target :
    TS94.Goldbach.TraceKernelSpectralDataTarget

  explicit_formula_front :
    TS95.Goldbach.ExplicitFormulaTraceBridgeRoadmapTarget

  no_claim_of_plancherel :
    True

  no_claim_of_explicit_formula :
    True

  no_claim_of_zeta_zero_sum_control :
    True

/-- Concrete TS162 activation ledger. -/
noncomputable def triangleSplineTraceKernelInstantiationLedger :
    TriangleSplineTraceKernelInstantiationLedger where
  phi_premortem := TS161.Goldbach.phiPremortemSpectralPivotLedger
  activation_status :=
    SpectralPivotActivationStatus.triangleSplineKernelInstantiated
  activation_status_eq := rfl
  origin_value := triangleSpline_zero
  kernel_nonnegative := triangleSpline_nonneg
  kernel_vanishes_outside_unit_abs := by
    intro x hx
    exact triangleSpline_eq_zero_of_one_le_abs hx
  trace_kernel := triangleSplineTraceKernel
  trace_kernel_eq := rfl
  trace_kernel_ledger := triangleSplineTraceKernelSpectralDataLedger
  trace_kernel_target := triangleSplineTraceKernelSpectralDataTarget
  explicit_formula_front :=
    TS95.Goldbach.explicitFormulaTraceBridgeRoadmapTarget
  no_claim_of_plancherel := True.intro
  no_claim_of_explicit_formula := True.intro
  no_claim_of_zeta_zero_sum_control := True.intro

/-- Target proposition for TS162. -/
def TriangleSplineTraceKernelInstantiationTarget : Prop :=
  Nonempty TriangleSplineTraceKernelInstantiationLedger

/-- The TS162 triangle-spline trace-kernel instantiation target is populated. -/
theorem triangleSplineTraceKernelInstantiationTarget :
    TriangleSplineTraceKernelInstantiationTarget :=
  Nonempty.intro triangleSplineTraceKernelInstantiationLedger

end Goldbach
end TS162
