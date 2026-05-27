import Mathlib.Tactic
import TS.Goldbach.Strong.TS28.OTSAConstantsCandidate

namespace TS29
namespace Goldbach

/--
Source status for an OTSA rational upper bound.

This metadata lives in Lean so that placeholders, narrative bounds, numerical
experiments, analytic derivations, and Lean-certified constants remain
distinguishable.
-/
inductive ConstantProvenance where
  | placeholder
  | narrative_source
  | numerical_experiment
  | analytic_derivation
  | lean_certified
  deriving DecidableEq, Repr

/-- A sourced rational upper bound for one OTSA constant. -/
structure SourcedRatBound where
  value : Rat
  provenance : ConstantProvenance
  label : String

/-- Provenance register for the four OTSA constants. -/
structure OTSAConstantProvenanceRegister where
  Ck : SourcedRatBound
  Ct : SourcedRatBound
  Cm : SourcedRatBound
  Cscale : SourcedRatBound
  packageStatus : TS28.Goldbach.ConstantStatus

/--
Candidate-v0 provenance register.

Only `Ck` currently has a narrative source. The other constants remain
placeholders until trace, Mellin-tail, and scale-transfer majorants are sourced.
-/
def OTSAProvenance_candidate_v0 : OTSAConstantProvenanceRegister where
  Ck :=
    { value := 3 / 50
      provenance := ConstantProvenance.narrative_source
      label := "Ck candidate: spectral/KLMN narrative bound C0 ~= 0.058, rounded to 3/50" }
  Ct :=
    { value := 1
      provenance := ConstantProvenance.placeholder
      label := "Ct placeholder: trace contribution bound not yet sourced" }
  Cm :=
    { value := 1
      provenance := ConstantProvenance.placeholder
      label := "Cm placeholder: Mellin-tail bound not yet sourced" }
  Cscale :=
    { value := 1
      provenance := ConstantProvenance.placeholder
      label := "Cscale placeholder: padded-scale transfer cost not yet sourced" }
  packageStatus := TS28.Goldbach.ConstantStatus.analytic_candidate

/-- The candidate-v0 provenance package is not certified. -/
theorem candidate_v0_not_certified :
    Not (OTSAProvenance_candidate_v0.packageStatus =
      TS28.Goldbach.ConstantStatus.certified) := by
  decide

/-- Candidate v0 records `Ck` as a narrative-source bound. -/
theorem candidate_v0_Ck_provenance :
    OTSAProvenance_candidate_v0.Ck.provenance =
      ConstantProvenance.narrative_source :=
  rfl

/-- Candidate v0 records `Ct` as a placeholder. -/
theorem candidate_v0_Ct_placeholder :
    OTSAProvenance_candidate_v0.Ct.provenance =
      ConstantProvenance.placeholder :=
  rfl

/-- Candidate v0 records `Cm` as a placeholder. -/
theorem candidate_v0_Cm_placeholder :
    OTSAProvenance_candidate_v0.Cm.provenance =
      ConstantProvenance.placeholder :=
  rfl

/-- Candidate v0 records `Cscale` as a placeholder. -/
theorem candidate_v0_Cscale_placeholder :
    OTSAProvenance_candidate_v0.Cscale.provenance =
      ConstantProvenance.placeholder :=
  rfl

end Goldbach
end TS29
