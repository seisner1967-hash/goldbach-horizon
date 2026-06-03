import Mathlib.Tactic
import TS.Goldbach.Strong.TS101.SelbergDivisorAlgebraLedger

namespace TS102
namespace Goldbach

/-!
# TS102 - Horizon Root Assembly

TS98 records the three final root inputs of the current architecture. TS101
refines the arithmetic input down to divisor-algebra infrastructure. This
sprint packages the root-level consequences of those terminal inputs.

No Brun-Titchmarsh theorem, Selberg sieve theorem, explicit formula, zeta-zero
estimate, Plancherel theorem, Sobolev-slot recognition, or Fourier-tail estimate
is proved here. The hard analytic content remains exactly the three terminal
input packages.
-/

/--
Roadmap marker for the root assembly layer.

The real mathematical inputs live in `HorizonRootAssemblyInputs`.
-/
structure HorizonRootAssemblyRoadmap where
  selberg_divisor_input_required :
    True

  explicit_trace_input_required :
    True

  mellin_tail_input_required :
    True

  padded_scale_output_required :
    True

  candidate_v3_output_required :
    True

/-- Concrete roadmap marker for TS102. -/
def horizonRootAssemblyRoadmap :
    HorizonRootAssemblyRoadmap where
  selberg_divisor_input_required := True.intro
  explicit_trace_input_required := True.intro
  mellin_tail_input_required := True.intro
  padded_scale_output_required := True.intro
  candidate_v3_output_required := True.intro

/--
The three terminal input packages for the root assembly.

Compared with TS98, the arithmetic input is the refined TS101
divisor-algebra infrastructure target rather than the coarser TS97
Brun-Titchmarsh wrapper.
-/
structure HorizonRootAssemblyInputs where
  selbergDivisor :
    TS101.Goldbach.SelbergDivisorAlgebraInfrastructureTarget

  explicitTrace :
    TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget

  mellinTail :
    TS83.MellinJackson.MellinTailFinalAPIContractsTarget

/--
Root-level output package produced by the three terminal inputs.

This object records the current top of the architecture: final inputs, padded
scale-transfer APIs, the full TS25 padded infrastructure, and the conditional
candidate-v3 OTSA certificate/register/provenance surfaces.
-/
structure HorizonRootAssembly where
  finalInputs :
    TS98.Goldbach.FinalHorizonInputsTarget

  paddedScaleTransfer :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget

  paddedScaleInfrastructure :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure

  finalMajorants :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget

  candidateV3Certificate :
    Nonempty TS26.Goldbach.OTSARationalCertificate

  candidateV3Register :
    Nonempty TS28.Goldbach.LabelledOTSAConstantRegister

  candidateV3Provenance :
    Nonempty TS29.Goldbach.OTSAConstantProvenanceRegister

  scaledAdmissible :
    Nonempty
      { C : TS23.Goldbach.ScaledOTSAConstants //
        TS23.Goldbach.ScaledOTSAAdmissible C }

/-- Target proposition for the TS102 roadmap marker. -/
def HorizonRootAssemblyRoadmapTarget : Prop :=
  Nonempty HorizonRootAssemblyRoadmap

/-- Target proposition for the three terminal root input packages. -/
def HorizonRootAssemblyInputsTarget : Prop :=
  Nonempty HorizonRootAssemblyInputs

/-- Target proposition for the root output package. -/
def HorizonRootAssemblyTarget : Prop :=
  Nonempty HorizonRootAssembly

/-- The TS102 roadmap marker is populated. -/
theorem horizonRootAssemblyRoadmapTarget :
    HorizonRootAssemblyRoadmapTarget :=
  Nonempty.intro horizonRootAssemblyRoadmap

/--
TS102 terminal inputs supply the TS98 final root input package.
-/
theorem finalHorizonInputsTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS101.Goldbach.finalHorizonInputsTarget_of_selbergDivisor_trace_mellin
    H.selbergDivisor
    H.explicitTrace
    H.mellinTail

/--
TS102 terminal inputs supply the TS84 padded final API package.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS101.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergDivisor_trace_mellin
    H.selbergDivisor
    H.explicitTrace
    H.mellinTail

/--
TS102 terminal inputs supply the full TS25 padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS101.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergDivisor_trace_mellin
    H.selbergDivisor
    H.explicitTrace
    H.mellinTail

/--
A padded final API package exposes its final OTSA majorant API package.
-/
theorem finalMajorantsTarget_of_paddedScaleTransferTarget
    (H : TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.majorants

/--
TS102 terminal inputs expose the final OTSA majorant API package.
-/
theorem finalMajorantsTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  finalMajorantsTarget_of_paddedScaleTransferTarget
    (paddedScaleTransferFinalAPIContractsTarget_of_rootAssemblyInputs H)

/--
TS102 terminal inputs supply the candidate-v3 rational certificate target.
-/
theorem candidateV3CertificateTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    Nonempty TS26.Goldbach.OTSARationalCertificate :=
  TS84.Goldbach.OTSACert_candidate_v3_target_of_finalAPIContractsTarget
    (finalMajorantsTarget_of_rootAssemblyInputs H)

/--
TS102 terminal inputs supply the candidate-v3 labelled register target.
-/
theorem candidateV3RegisterTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    Nonempty TS28.Goldbach.LabelledOTSAConstantRegister :=
  TS84.Goldbach.OTSARegister_candidate_v3_target_of_finalAPIContractsTarget
    (finalMajorantsTarget_of_rootAssemblyInputs H)

/--
TS102 terminal inputs supply the candidate-v3 provenance target.
-/
theorem candidateV3ProvenanceTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    Nonempty TS29.Goldbach.OTSAConstantProvenanceRegister :=
  TS84.Goldbach.OTSAProvenance_candidate_v3_target_of_finalAPIContractsTarget
    (finalMajorantsTarget_of_rootAssemblyInputs H)

/--
TS102 terminal inputs supply a scaled OTSA admissibility surface.
-/
theorem scaledOTSAAdmissibleTarget_of_rootAssemblyInputs
    (H : HorizonRootAssemblyInputs) :
    Nonempty
      { C : TS23.Goldbach.ScaledOTSAConstants //
        TS23.Goldbach.ScaledOTSAAdmissible C } :=
  TS84.Goldbach.scaledOTSAAdmissibleTarget_of_finalAPIContractsTarget
    (finalMajorantsTarget_of_rootAssemblyInputs H)

/--
The three terminal inputs assemble the current Horizon root output package.
-/
theorem horizonRootAssembly_of_inputs
    (H : HorizonRootAssemblyInputs) :
    HorizonRootAssembly where
  finalInputs :=
    finalHorizonInputsTarget_of_rootAssemblyInputs H
  paddedScaleTransfer :=
    paddedScaleTransferFinalAPIContractsTarget_of_rootAssemblyInputs H
  paddedScaleInfrastructure :=
    paddedScaleAnalyticInfrastructureTarget_of_rootAssemblyInputs H
  finalMajorants :=
    finalMajorantsTarget_of_rootAssemblyInputs H
  candidateV3Certificate :=
    candidateV3CertificateTarget_of_rootAssemblyInputs H
  candidateV3Register :=
    candidateV3RegisterTarget_of_rootAssemblyInputs H
  candidateV3Provenance :=
    candidateV3ProvenanceTarget_of_rootAssemblyInputs H
  scaledAdmissible :=
    scaledOTSAAdmissibleTarget_of_rootAssemblyInputs H

/--
A nonempty TS102 terminal input package supplies the root output package.
-/
theorem horizonRootAssemblyTarget_of_inputsTarget
    (H : HorizonRootAssemblyInputsTarget) :
    HorizonRootAssemblyTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (horizonRootAssembly_of_inputs h)

end Goldbach
end TS102
