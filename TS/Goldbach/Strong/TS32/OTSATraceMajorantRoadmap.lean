import Mathlib.Tactic
import TS.Goldbach.Strong.TS31.OTSAAsymptoticMajorants

namespace TS32
namespace Goldbach

/-!
# TS32 - OTSA Trace Majorant Roadmap

This sprint isolates the trace-contribution target for the OTSA constant
ledger. It does not prove the trace estimate. Instead, it records the local
contract that would upgrade the trace placeholder and checks, by exact rational
arithmetic, that any trace bound `Ct <= 1/2` remains far below the TS23
admissibility threshold.
-/

/--
Analytic contract for the OTSA trace contribution.

A future proof of the smoothed explicit-formula trace estimate should
instantiate this structure. The structure itself is an explicit local
obligation, not a hidden proof of the trace bound.
-/
structure TraceMajorantContract where
  Ct_bound : Rat
  Ct_pos : 0 < Ct_bound
  Ct_le_half : Ct_bound <= 1 / 2

/-- Target value for the trace contribution majorant. -/
def Ct_target_v2 : Rat :=
  1 / 2

/-- Candidate v2 keeps the v1 spectral-kernel majorant. -/
def Ck_v2 : Rat :=
  TS31.Goldbach.Ck_v1

/-- Candidate v2 keeps the v1 Mellin-tail placeholder. -/
def Cm_v2 : Rat :=
  TS31.Goldbach.Cm_v1

/-- Candidate v2 keeps the v1 scale-transfer placeholder. -/
def Cscale_v2 : Rat :=
  TS31.Goldbach.Cscale_v1

/-- Exact target value if the trace bound is instantiated as `Ct = 1/2`. -/
theorem candidate_v2_target_scaled_value :
    Cscale_v2 * (Ck_v2 * Ct_target_v2 + Cm_v2) = 103 / 100 := by
  norm_num [Cscale_v2, Ck_v2, Ct_target_v2, Cm_v2,
    TS31.Goldbach.Cscale_v1, TS31.Goldbach.Ck_v1, TS31.Goldbach.Cm_v1]

/-- Any trace majorant satisfying `Ct <= 1/2` is OTSA-admissible with v2 constants. -/
theorem candidate_v2_scaled_le_26
    (H : TraceMajorantContract) :
    Cscale_v2 * (Ck_v2 * H.Ct_bound + Cm_v2) <= 26 := by
  have hCt : H.Ct_bound <= (1 / 2 : Rat) := H.Ct_le_half
  norm_num [Cscale_v2, Ck_v2, Cm_v2,
    TS31.Goldbach.Cscale_v1, TS31.Goldbach.Ck_v1, TS31.Goldbach.Cm_v1]
  nlinarith

/-- Candidate v2 OTSA rational certificate, conditional on the trace contract. -/
def OTSACert_candidate_v2
    (H : TraceMajorantContract) :
    TS26.Goldbach.OTSARationalCertificate where
  Ck := Ck_v2
  Ct := H.Ct_bound
  Cm := Cm_v2
  Cscale := Cscale_v2
  Ck_pos := by norm_num [Ck_v2, TS31.Goldbach.Ck_v1]
  Ct_pos := H.Ct_pos
  Cm_pos := by norm_num [Cm_v2, TS31.Goldbach.Cm_v1]
  Cscale_pos := by norm_num [Cscale_v2, TS31.Goldbach.Cscale_v1]
  admissible_rat := candidate_v2_scaled_le_26 H

/-- Labelled TS28 register for conditional candidate v2. -/
def OTSARegister_candidate_v2
    (H : TraceMajorantContract) :
    TS28.Goldbach.LabelledOTSAConstantRegister where
  label := "OTSA trace-majorant candidate v2"
  status := TS28.Goldbach.ConstantStatus.analytic_candidate
  sourceNote :=
    "Conditional candidate v2: if a future trace analysis supplies Ct <= 1/2, the rational OTSA admissibility inequality is certified. Cm and Cscale remain placeholders."
  cert := OTSACert_candidate_v2 H

/--
Conditional candidate-v2 provenance register.

The trace entry is deliberately marked as a numerical experiment until the
analytic contract is instantiated by a sourced derivation or Lean proof.
-/
def OTSAProvenance_candidate_v2
    (H : TraceMajorantContract) :
    TS29.Goldbach.OTSAConstantProvenanceRegister where
  Ck := TS31.Goldbach.OTSAProvenance_candidate_v1.Ck
  Ct :=
    { value := H.Ct_bound
      provenance := TS29.Goldbach.ConstantProvenance.numerical_experiment
      label := "Ct target v2: conditional trace majorant Ct <= 1/2, pending analytic derivation" }
  Cm := TS31.Goldbach.OTSAProvenance_candidate_v1.Cm
  Cscale := TS31.Goldbach.OTSAProvenance_candidate_v1.Cscale
  packageStatus := TS28.Goldbach.ConstantStatus.analytic_candidate

/-- Candidate v2 is not a final certified constant package. -/
theorem candidate_v2_not_certified
    (H : TraceMajorantContract) :
    Not ((OTSAProvenance_candidate_v2 H).packageStatus =
      TS28.Goldbach.ConstantStatus.certified) := by
  intro h
  cases h

/-- Candidate v2 records `Ct` as conditional numerical evidence, not certification. -/
theorem candidate_v2_Ct_is_conditional
    (H : TraceMajorantContract) :
    (OTSAProvenance_candidate_v2 H).Ct.provenance =
      TS29.Goldbach.ConstantProvenance.numerical_experiment :=
  rfl

/-- Conditional candidate v2 feeds TS23 through TS26. -/
theorem candidate_v2_scaledOTSAAdmissible
    (H : TraceMajorantContract) :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat
        (OTSACert_candidate_v2 H)) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat
    (OTSACert_candidate_v2 H)

/-- The labelled conditional candidate-v2 register also feeds TS23 through TS26. -/
theorem candidate_v2_register_scaledOTSAAdmissible
    (H : TraceMajorantContract) :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat
        (OTSARegister_candidate_v2 H).cert) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat
    (OTSARegister_candidate_v2 H).cert

end Goldbach
end TS32
