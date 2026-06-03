import Mathlib.Tactic
import TS.Goldbach.Strong.TS91.DualLargeSieveVarianceBoundProof

namespace TS92
namespace Goldbach

/-!
# TS92 - Spectral Trace Roadmap

TS32 isolates the trace majorant `Ct <= 1/2` as a rational contract. This
sprint opens the spectral side of that contract: kernel data, zeta-zero data,
and an explicit-formula bridge.

No zeta-zero estimate is proved here. The analytic content remains in the
local `SpectralTraceMajorantContract`. If that contract is supplied, it
mechanically produces the TS32 trace contract and then feeds the TS91
scale-transfer assembly.
-/

/-- Kernel-side data expected by the future spectral trace analysis. -/
structure TraceKernelSpectralData where
  kernel_normalization_ready :
    True

  positivity_control_ready :
    True

  decay_control_ready :
    True

/-- Zeta-zero side data expected by the future explicit-formula trace analysis. -/
structure ZetaZeroFamily where
  zero_family_ready :
    True

  multiplicity_accounting_ready :
    True

  symmetry_accounting_ready :
    True

/-- Explicit-formula bridge between the kernel trace and the zeta-zero sum. -/
structure ExplicitFormulaTraceBridge where
  von_mangoldt_formula_ready :
    True

  zero_sum_trace_bridge_ready :
    True

  residual_error_control_ready :
    True

/-- Roadmap ledger for the spectral trace front. -/
structure SpectralTraceRoadmap where
  kernel_data_required :
    True

  zeta_zero_family_required :
    True

  explicit_formula_bridge_required :
    True

  rational_trace_majorant_required :
    True

/-- Concrete roadmap ledger for TS92. -/
def spectralTraceRoadmap :
    SpectralTraceRoadmap where
  kernel_data_required := True.intro
  zeta_zero_family_required := True.intro
  explicit_formula_bridge_required := True.intro
  rational_trace_majorant_required := True.intro

/--
Spectral trace majorant contract.

This is the local analytic obligation for the `Ct` front. The first three
fields record the future spectral/exact-formula infrastructure. The rational
fields are exactly what TS32 needs to build `TraceMajorantContract`.
-/
structure SpectralTraceMajorantContract where
  kernel :
    TraceKernelSpectralData

  zeros :
    ZetaZeroFamily

  explicitFormula :
    ExplicitFormulaTraceBridge

  Ct_bound :
    Rat

  Ct_pos :
    0 < Ct_bound

  Ct_le_half :
    Ct_bound <= 1 / 2

/-- A spectral trace contract supplies the TS32 trace majorant contract. -/
def traceMajorantContract_of_spectralTrace
    (H : SpectralTraceMajorantContract) :
    TS32.Goldbach.TraceMajorantContract where
  Ct_bound := H.Ct_bound
  Ct_pos := H.Ct_pos
  Ct_le_half := H.Ct_le_half

/-- Target proposition for the TS92 roadmap ledger. -/
def SpectralTraceRoadmapTarget : Prop :=
  Nonempty SpectralTraceRoadmap

/-- Target proposition for the spectral trace majorant contract. -/
def SpectralTraceMajorantContractTarget : Prop :=
  Nonempty SpectralTraceMajorantContract

/-- The TS92 roadmap ledger is populated. -/
theorem spectralTraceRoadmapTarget :
    SpectralTraceRoadmapTarget :=
  Nonempty.intro spectralTraceRoadmap

/-- A spectral trace target supplies the TS32 trace target. -/
theorem traceMajorantContractTarget_of_spectralTraceTarget
    (H : SpectralTraceMajorantContractTarget) :
    Nonempty TS32.Goldbach.TraceMajorantContract := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (traceMajorantContract_of_spectralTrace h)

/--
Spectral trace plus Mellin-tail final contracts give the final TS84 OTSA
majorant API target, using the TS91 scale-transfer package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_spectralTrace_mellin
    (Ht : SpectralTraceMajorantContractTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  TS91.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin
    (traceMajorantContractTarget_of_spectralTraceTarget Ht)
    Hm

/--
Adding Brun-Titchmarsh leaves spectral trace and Mellin-tail final contracts as
the remaining inputs for the TS25 padded-scale analytic infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_spectralTrace_mellin
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : SpectralTraceMajorantContractTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS91.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin
    HBT
    (traceMajorantContractTarget_of_spectralTraceTarget Ht)
    Hm

end Goldbach
end TS92
