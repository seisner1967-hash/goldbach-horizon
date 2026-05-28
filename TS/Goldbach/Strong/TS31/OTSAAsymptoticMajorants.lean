import Mathlib.Tactic
import TS.Goldbach.Strong.TS29.OTSAConstantProvenance

namespace TS31
namespace Goldbach

/-!
# TS31 - OTSA Asymptotic Majorants

This sprint records the first asymptotic-majorant candidate package after the
TS29 provenance ledger. It is intentionally not a final certificate: the
pipeline is checked by exact rational arithmetic, while the source status keeps
unsourced constants visibly marked as placeholders.
-/

/-- Candidate v1 spectral-kernel majorant. -/
def Ck_v1 : Rat :=
  3 / 50

/-- Candidate v1 trace-contribution majorant. -/
def Ct_v1 : Rat :=
  1

/-- Candidate v1 Mellin-tail majorant. -/
def Cm_v1 : Rat :=
  1

/-- Candidate v1 padded-scale transfer majorant. -/
def Cscale_v1 : Rat :=
  1

/-- Exact rational value of the current scaled OTSA candidate. -/
theorem candidate_v1_scaled_value :
    Cscale_v1 * (Ck_v1 * Ct_v1 + Cm_v1) = 53 / 50 := by
  norm_num [Ck_v1, Ct_v1, Cm_v1, Cscale_v1]

/-- The current candidate has a large margin below the TS23 threshold `26`. -/
theorem candidate_v1_scaled_le_26 :
    Cscale_v1 * (Ck_v1 * Ct_v1 + Cm_v1) <= 26 := by
  norm_num [Ck_v1, Ct_v1, Cm_v1, Cscale_v1]

/--
Candidate v1 OTSA rational certificate.

The inequality is certified, but the provenance register below still marks
`Ct`, `Cm`, and `Cscale` as placeholders.
-/
def OTSACert_candidate_v1 : TS26.Goldbach.OTSARationalCertificate where
  Ck := Ck_v1
  Ct := Ct_v1
  Cm := Cm_v1
  Cscale := Cscale_v1
  Ck_pos := by norm_num [Ck_v1]
  Ct_pos := by norm_num [Ct_v1]
  Cm_pos := by norm_num [Cm_v1]
  Cscale_pos := by norm_num [Cscale_v1]
  admissible_rat := candidate_v1_scaled_le_26

/-- Labelled TS28 register for candidate v1. -/
def OTSARegister_candidate_v1 : TS28.Goldbach.LabelledOTSAConstantRegister where
  label := "OTSA asymptotic majorants candidate v1"
  status := TS28.Goldbach.ConstantStatus.analytic_candidate
  sourceNote :=
    "Candidate v1: Ck=3/50 is the padded narrative spectral bound; Ct, Cm, and Cscale remain placeholders pending trace, Mellin-tail, and scale-transfer derivations."
  cert := OTSACert_candidate_v1

/--
Candidate-v1 provenance register.

Only `Ck` is currently attached to a narrative source. The remaining entries
are intentionally placeholders until asymptotic derivations or Lean-certified
majorants are supplied.
-/
def OTSAProvenance_candidate_v1 :
    TS29.Goldbach.OTSAConstantProvenanceRegister where
  Ck :=
    { value := Ck_v1
      provenance := TS29.Goldbach.ConstantProvenance.narrative_source
      label := "Ck <= 3/50, rounded upward from the spectral narrative bound C0 ~= 0.058" }
  Ct :=
    { value := Ct_v1
      provenance := TS29.Goldbach.ConstantProvenance.placeholder
      label := "Ct placeholder pending trace contribution derivation" }
  Cm :=
    { value := Cm_v1
      provenance := TS29.Goldbach.ConstantProvenance.placeholder
      label := "Cm placeholder pending Mellin-tail derivation" }
  Cscale :=
    { value := Cscale_v1
      provenance := TS29.Goldbach.ConstantProvenance.placeholder
      label := "Cscale placeholder pending padded-scale transfer derivation" }
  packageStatus := TS28.Goldbach.ConstantStatus.analytic_candidate

/-- Candidate v1 is not a final certified constant package. -/
theorem candidate_v1_not_certified :
    Not (OTSAProvenance_candidate_v1.packageStatus =
      TS28.Goldbach.ConstantStatus.certified) := by
  decide

/-- Candidate v1 records `Ck` as a narrative-source bound. -/
theorem candidate_v1_Ck_provenance :
    OTSAProvenance_candidate_v1.Ck.provenance =
      TS29.Goldbach.ConstantProvenance.narrative_source :=
  rfl

/-- Candidate v1 records `Ct` as a placeholder. -/
theorem candidate_v1_Ct_placeholder :
    OTSAProvenance_candidate_v1.Ct.provenance =
      TS29.Goldbach.ConstantProvenance.placeholder :=
  rfl

/-- Candidate v1 records `Cm` as a placeholder. -/
theorem candidate_v1_Cm_placeholder :
    OTSAProvenance_candidate_v1.Cm.provenance =
      TS29.Goldbach.ConstantProvenance.placeholder :=
  rfl

/-- Candidate v1 records `Cscale` as a placeholder. -/
theorem candidate_v1_Cscale_placeholder :
    OTSAProvenance_candidate_v1.Cscale.provenance =
      TS29.Goldbach.ConstantProvenance.placeholder :=
  rfl

/-- The candidate-v1 certificate proves the TS23 admissibility inequality. -/
theorem candidate_v1_scaledOTSAAdmissible :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat OTSACert_candidate_v1) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat OTSACert_candidate_v1

/-- The labelled candidate-v1 register also feeds TS23 through TS26. -/
theorem candidate_v1_register_scaledOTSAAdmissible :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat OTSARegister_candidate_v1.cert) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat OTSARegister_candidate_v1.cert

end Goldbach
end TS31
