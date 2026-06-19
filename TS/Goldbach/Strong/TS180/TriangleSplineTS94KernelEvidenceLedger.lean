import Mathlib.Tactic
import TS.Goldbach.Strong.TS163.TriangleSplineFourierWeightLedger
import TS.Goldbach.Strong.TS173.TriangleSplineFourierIdentificationDischarge
import TS.Goldbach.Strong.TS179.TriangleSplinePlancherelAPIProbe

namespace TS180
namespace Goldbach

open scoped ENNReal

/-!
# TS180 - Triangle Spline TS94 Kernel Evidence Ledger

TS179 records that the ready-made Plancherel API names are not exposed in the
current Mathlib surface and proves the final conditional consumption theorem:
if the concrete TS174 Plancherel isometry is supplied, then the pi-scale
squared-sinc spectral L2 energy has the exact value
`ENNReal.ofReal (Real.sqrt (2 / 3))`.

This sprint packages the triangle-spline evidence accumulated for the TS94
kernel side:

* TS162 installs the real triangle-spline trace kernel;
* TS163 installs the nonnegative sinc-square spectral-weight candidate;
* TS173 proves the pointwise Mathlib Fourier identification;
* TS177 proves the exact time-side L2 value;
* TS178 proves finite sinc-side L2 energy;
* TS179 proves the exact sinc-side value conditionally on the TS174
  Plancherel input.

TS180 does not prove unconditional Plancherel, zeta-zero summability, the
Riemann-von Mangoldt explicit formula, or Goldbach.
-/

/-- Status markers for the TS94 triangle-spline kernel evidence package. -/
inductive TriangleSplineTS94KernelEvidenceStatus where
  | realKernelInstalled
  | sincWeightInstalled
  | fourierIdentityProved
  | l2EvidencePackaged
  deriving DecidableEq, Repr

/--
Evidence ledger for using the triangle spline on the TS94 kernel front.

The field `ts94_local_trace_kernel_ledger` records the current TS94 local
kernel ledger supplied by TS163.  The stronger arithmetic statement that a
future zeta-zero spectral sum converges is deliberately not claimed here.
-/
structure TriangleSplineTS94KernelEvidenceLedger where
  ts162_kernel :
    TS162.Goldbach.TriangleSplineTraceKernelInstantiationLedger

  ts163_fourier_weight :
    TS163.Goldbach.TriangleSplineFourierWeightLedger

  status :
    TriangleSplineTS94KernelEvidenceStatus

  status_eq :
    status =
      TriangleSplineTS94KernelEvidenceStatus.l2EvidencePackaged

  ts94_local_trace_kernel_ledger :
    TS94.Goldbach.TraceKernelSpectralDataLedger

  ts94_local_trace_kernel_target :
    TS94.Goldbach.TraceKernelSpectralDataTarget

  fourier_identification :
    TS166.Goldbach.TriangleSplineFourierIdentificationStatement

  time_l2_energy_value :
    TS174.Goldbach.triangleSplineTimeL2Energy =
      ENNReal.ofReal (Real.sqrt (2 / 3))

  sinc_l2_energy_finite :
    TS174.Goldbach.triangleSplineSincL2Energy <
      (Top.top : ENNReal)

  conditional_sinc_l2_energy_value :
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement ->
      TS174.Goldbach.triangleSplineSincL2Energy =
        ENNReal.ofReal (Real.sqrt (2 / 3))

  plancherel_input :
    Prop

  plancherel_input_eq :
    plancherel_input =
      TS174.Goldbach.TriangleSplinePlancherelIsometryStatement

  ts94_kernel_front_available :
    True

  unconditional_plancherel_not_claimed :
    True

  zeta_zero_summability_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS180 TS94 kernel evidence ledger. -/
noncomputable def triangleSplineTS94KernelEvidenceLedger :
    TriangleSplineTS94KernelEvidenceLedger where
  ts162_kernel :=
    TS162.Goldbach.triangleSplineTraceKernelInstantiationLedger
  ts163_fourier_weight :=
    TS163.Goldbach.triangleSplineFourierWeightLedger
  status := TriangleSplineTS94KernelEvidenceStatus.l2EvidencePackaged
  status_eq := rfl
  ts94_local_trace_kernel_ledger :=
    TS163.Goldbach.triangleSplineFourierTraceKernelSpectralDataLedger
  ts94_local_trace_kernel_target :=
    TS163.Goldbach.triangleSplineFourierTraceKernelSpectralDataTarget
  fourier_identification :=
    TS173.Goldbach.triangleSplineFourierIdentification
  time_l2_energy_value :=
    TS177.Goldbach.triangleSplineTimeELpNormValue
  sinc_l2_energy_finite :=
    TS178.Goldbach.triangleSplineSincL2Energy_lt_top
  conditional_sinc_l2_energy_value :=
    TS179.Goldbach.triangleSplineSincL2Energy_eq_sqrt_two_thirds_of_plancherel
  plancherel_input :=
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement
  plancherel_input_eq := rfl
  ts94_kernel_front_available := True.intro
  unconditional_plancherel_not_claimed := True.intro
  zeta_zero_summability_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS180. -/
def TriangleSplineTS94KernelEvidenceTarget : Prop :=
  Nonempty TriangleSplineTS94KernelEvidenceLedger

/-- The TS180 TS94 triangle-spline evidence target is populated. -/
theorem triangleSplineTS94KernelEvidenceTarget :
    TriangleSplineTS94KernelEvidenceTarget :=
  Nonempty.intro triangleSplineTS94KernelEvidenceLedger

end Goldbach
end TS180
