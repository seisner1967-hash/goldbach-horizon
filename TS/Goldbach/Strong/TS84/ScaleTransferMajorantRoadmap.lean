import Mathlib.Tactic
import TS.Goldbach.Strong.TS25.PaddedScaleOTSAFeasibility
import TS.Goldbach.Strong.TS83.MellinTailFinalAPIGapLedger

namespace TS84
namespace Goldbach

/-!
# TS84 - Scale Transfer Majorant Roadmap

The Mellin-tail route is architecturally closed by TS83, modulo explicit
external API contracts. This sprint opens the next OTSA pillar: the
scale-transfer factor `Cscale`.

TS84 does not prove a Gallagher/large-sieve scale transfer theorem. It records
the exact local contracts needed to turn a padded TS24 scale-to-OTSA control
into the TS33 rational majorant contract `Cscale <= 2`, and then shows how this
contract combines with the TS83 Mellin-tail package and the TS32 trace contract
to feed the final TS33/TS25 assembly layers.
-/

/--
Roadmap ledger for the scale-transfer front.

The local spline analysis is no longer part of this front. The remaining
scale-transfer work is to provide a concrete TS23 scale control for the padded
TS24 scale and a rational majorant `Cscale <= 2` compatible with that control.
-/
structure ScaleTransferMajorantRoadmap where
  uses_padded_closed_form_scale :
    True

  scale_to_otsa_control_required :
    True

  rational_scale_majorant_required :
    True

  final_otsa_assembly_required :
    True

/-- Concrete roadmap ledger for the scale-transfer front. -/
def scaleTransferMajorantRoadmap :
    ScaleTransferMajorantRoadmap where
  uses_padded_closed_form_scale := True.intro
  scale_to_otsa_control_required := True.intro
  rational_scale_majorant_required := True.intro
  final_otsa_assembly_required := True.intro

/--
API contracts needed to instantiate the TS33 scale-transfer majorant.

The field `Cscale_matches_control` ties the rational bound used by the OTSA
certificate to the real constant carried by the TS23 scale-transfer control.
-/
structure ScaleTransferMajorantAPIContracts where
  scaleControl :
    TS23.Goldbach.ScaleToOTSAControl
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale

  Cscale_bound :
    Rat

  Cscale_pos :
    0 < Cscale_bound

  Cscale_le_two :
    Cscale_bound <= 2

  Cscale_matches_control :
    (Cscale_bound : Real) = scaleControl.Cscale

/-- The scale-transfer API contracts give the TS33 rational majorant contract. -/
def scaleTransferMajorantContract_of_apiContracts
    (H : ScaleTransferMajorantAPIContracts) :
    TS33.Goldbach.ScaleTransferMajorantContract where
  Cscale_bound := H.Cscale_bound
  Cscale_pos := H.Cscale_pos
  Cscale_le_two := H.Cscale_le_two

/--
Final majorant API contracts for the OTSA v3 rational package.

This combines:
- the TS32 trace contract `Ct <= 1/2`;
- the TS83 final Mellin-tail API package, which conditionally yields `Cm <= 1`;
- the TS84 scale-transfer API package, which conditionally yields `Cscale <= 2`.
-/
structure OTSAFinalMajorantAPIContracts where
  trace :
    TS32.Goldbach.TraceMajorantContract

  mellin :
    TS83.MellinJackson.MellinTailFinalAPIContracts

  scale :
    ScaleTransferMajorantAPIContracts

/-- Extract the TS33 Mellin-tail contract from a TS83 final API package. -/
noncomputable def mellinTailMajorantContract_of_finalAPIContracts
    (H : TS83.MellinJackson.MellinTailFinalAPIContracts) :
    TS33.Goldbach.MellinTailMajorantContract :=
  Classical.choice
    (TS83.MellinJackson.mellinTailContractTarget_of_finalAPIContractsTarget
      (Nonempty.intro H))

/-- Extract the TS33 scale-transfer contract from the TS84 API package. -/
def scaleTransferMajorantContract_of_finalAPIContracts
    (H : OTSAFinalMajorantAPIContracts) :
    TS33.Goldbach.ScaleTransferMajorantContract :=
  scaleTransferMajorantContract_of_apiContracts H.scale

/-- The final API contracts supply the TS33 candidate-v3 rational certificate. -/
noncomputable def OTSACert_candidate_v3_of_finalAPIContracts
    (H : OTSAFinalMajorantAPIContracts) :
    TS26.Goldbach.OTSARationalCertificate :=
  TS33.Goldbach.OTSACert_candidate_v3
    H.trace
    (mellinTailMajorantContract_of_finalAPIContracts H.mellin)
    (scaleTransferMajorantContract_of_finalAPIContracts H)

/-- The final API contracts supply the TS28 labelled candidate-v3 register. -/
noncomputable def OTSARegister_candidate_v3_of_finalAPIContracts
    (H : OTSAFinalMajorantAPIContracts) :
    TS28.Goldbach.LabelledOTSAConstantRegister :=
  TS33.Goldbach.OTSARegister_candidate_v3
    H.trace
    (mellinTailMajorantContract_of_finalAPIContracts H.mellin)
    (scaleTransferMajorantContract_of_finalAPIContracts H)

/-- The final API contracts supply the TS29 candidate-v3 provenance register. -/
noncomputable def OTSAProvenance_candidate_v3_of_finalAPIContracts
    (H : OTSAFinalMajorantAPIContracts) :
    TS29.Goldbach.OTSAConstantProvenanceRegister :=
  TS33.Goldbach.OTSAProvenance_candidate_v3
    H.trace
    (mellinTailMajorantContract_of_finalAPIContracts H.mellin)
    (scaleTransferMajorantContract_of_finalAPIContracts H)

/-- Final majorant API contracts feed the TS23 scaled admissibility target. -/
theorem scaledOTSAAdmissible_of_finalAPIContracts
    (H : OTSAFinalMajorantAPIContracts) :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat
        (OTSACert_candidate_v3_of_finalAPIContracts H)) := by
  unfold OTSACert_candidate_v3_of_finalAPIContracts
  exact
    TS33.Goldbach.candidate_v3_scaledOTSAAdmissible
      H.trace
      (mellinTailMajorantContract_of_finalAPIContracts H.mellin)
      (scaleTransferMajorantContract_of_finalAPIContracts H)

/--
Final padded-scale API contracts.

Adding a Brun-Titchmarsh interval input to the final majorant contracts produces
the full TS25 padded-scale analytic infrastructure.
-/
structure PaddedScaleTransferFinalAPIContracts where
  BT :
    TS22.Goldbach.BrunTitchmarshNatIntervalBound

  majorants :
    OTSAFinalMajorantAPIContracts

/--
The final padded-scale API contracts supply the TS25 padded-scale
infrastructure.
-/
noncomputable def paddedScaleAnalyticInfrastructure_of_finalAPIContracts
    (H : PaddedScaleTransferFinalAPIContracts) :
    TS25.Goldbach.PaddedScaleAnalyticInfrastructure where
  BT := H.BT
  scaleControl := H.majorants.scale.scaleControl
  constants :=
    TS26.Goldbach.scaledConstantsOfRat
      (OTSACert_candidate_v3_of_finalAPIContracts H.majorants)
  Cscale_matches := by
    change (H.majorants.scale.Cscale_bound : Real) =
      H.majorants.scale.scaleControl.Cscale
    exact H.majorants.scale.Cscale_matches_control
  admissible :=
    scaledOTSAAdmissible_of_finalAPIContracts H.majorants

/-- Target proposition for the scale-transfer roadmap. -/
def ScaleTransferMajorantRoadmapTarget : Prop :=
  Nonempty ScaleTransferMajorantRoadmap

/-- Target proposition for the scale-transfer API contracts. -/
def ScaleTransferMajorantAPIContractsTarget : Prop :=
  Nonempty ScaleTransferMajorantAPIContracts

/-- Target proposition for the final OTSA majorant API contracts. -/
def OTSAFinalMajorantAPIContractsTarget : Prop :=
  Nonempty OTSAFinalMajorantAPIContracts

/-- Target proposition for the final padded-scale API contracts. -/
def PaddedScaleTransferFinalAPIContractsTarget : Prop :=
  Nonempty PaddedScaleTransferFinalAPIContracts

/-- The TS84 roadmap ledger is populated. -/
theorem scaleTransferMajorantRoadmapTarget :
    ScaleTransferMajorantRoadmapTarget :=
  Nonempty.intro scaleTransferMajorantRoadmap

/-- Scale-transfer API contracts supply the TS33 scale-transfer contract. -/
theorem scaleTransferMajorantContractTarget_of_apiContractsTarget
    (H : ScaleTransferMajorantAPIContractsTarget) :
    Nonempty TS33.Goldbach.ScaleTransferMajorantContract := by
  cases H with
  | intro h =>
      exact Nonempty.intro (scaleTransferMajorantContract_of_apiContracts h)

/-- Final OTSA API contracts supply the TS32 trace target. -/
theorem traceMajorantContractTarget_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    Nonempty TS32.Goldbach.TraceMajorantContract := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.trace

/-- Final OTSA API contracts supply the TS83 Mellin-tail final target. -/
theorem mellinTailFinalAPIContractsTarget_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    TS83.MellinJackson.MellinTailFinalAPIContractsTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.mellin

/-- Final OTSA API contracts supply the TS84 scale-transfer contract target. -/
theorem scaleTransferMajorantContractTarget_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    Nonempty TS33.Goldbach.ScaleTransferMajorantContract := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (scaleTransferMajorantContract_of_finalAPIContracts h)

/-- Final OTSA API contracts supply the TS33 candidate-v3 certificate target. -/
theorem OTSACert_candidate_v3_target_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    Nonempty TS26.Goldbach.OTSARationalCertificate := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (OTSACert_candidate_v3_of_finalAPIContracts h)

/-- Final OTSA API contracts supply the TS28 candidate-v3 register target. -/
theorem OTSARegister_candidate_v3_target_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    Nonempty TS28.Goldbach.LabelledOTSAConstantRegister := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (OTSARegister_candidate_v3_of_finalAPIContracts h)

/-- Final OTSA API contracts supply the TS29 candidate-v3 provenance target. -/
theorem OTSAProvenance_candidate_v3_target_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    Nonempty TS29.Goldbach.OTSAConstantProvenanceRegister := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (OTSAProvenance_candidate_v3_of_finalAPIContracts h)

/-- Final OTSA API contracts supply a TS23 scaled admissibility certificate. -/
theorem scaledOTSAAdmissibleTarget_of_finalAPIContractsTarget
    (H : OTSAFinalMajorantAPIContractsTarget) :
    Nonempty
      { C : TS23.Goldbach.ScaledOTSAConstants //
        TS23.Goldbach.ScaledOTSAAdmissible C } := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          { val := TS26.Goldbach.scaledConstantsOfRat
              (OTSACert_candidate_v3_of_finalAPIContracts h),
            property := scaledOTSAAdmissible_of_finalAPIContracts h }

/-- Final padded-scale contracts supply the TS25 padded-scale infrastructure. -/
theorem paddedScaleAnalyticInfrastructureTarget_of_finalAPIContractsTarget
    (H : PaddedScaleTransferFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (paddedScaleAnalyticInfrastructure_of_finalAPIContracts h)

end Goldbach
end TS84
