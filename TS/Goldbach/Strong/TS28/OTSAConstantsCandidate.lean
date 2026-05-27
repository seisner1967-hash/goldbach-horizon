import Mathlib.Tactic
import TS.Goldbach.Strong.TS27.OTSAConstantRegister

namespace TS28
namespace Goldbach

/--
Status tag for rational OTSA constant registers.

This separates plumbing tests, analytic candidates, and fully certified
constant packages.
-/
inductive ConstantStatus where
  | smoke_test
  | analytic_candidate
  | certified
  deriving DecidableEq, Repr

/--
Labelled rational OTSA constant register with a typed status.

The certificate field is still checked by TS26. The status records how much
analytic provenance is attached to the rational bounds.
-/
structure LabelledOTSAConstantRegister where
  label : String
  status : ConstantStatus
  sourceNote : String
  cert : TS26.Goldbach.OTSARationalCertificate

/--
Candidate v0 spectral-kernel constant.

This keeps the narrative upper bound `C0 ~= 0.058` padded to `3/50`.
-/
def Ck_candidate_v0 : Rat :=
  3 / 50

/--
Candidate v0 trace constant.

This remains a placeholder until a trace-control source is registered.
-/
def Ct_candidate_v0 : Rat :=
  1

/--
Candidate v0 Mellin-tail constant.

This remains a placeholder until a Mellin-tail source is registered.
-/
def Cm_candidate_v0 : Rat :=
  1

/--
Candidate v0 scale-transfer constant.

This remains a placeholder until a scale-to-OTSA source is registered.
-/
def Cscale_candidate_v0 : Rat :=
  1

/--
Candidate v0 OTSA rational certificate.

This is not a final certificate: the rational inequality is certified, but the
analytic provenance of `Ct`, `Cm`, and `Cscale` is still to be supplied.
-/
def OTSACert_candidate_v0 : TS26.Goldbach.OTSARationalCertificate where
  Ck := Ck_candidate_v0
  Ct := Ct_candidate_v0
  Cm := Cm_candidate_v0
  Cscale := Cscale_candidate_v0
  Ck_pos := by norm_num [Ck_candidate_v0]
  Ct_pos := by norm_num [Ct_candidate_v0]
  Cm_pos := by norm_num [Cm_candidate_v0]
  Cscale_pos := by norm_num [Cscale_candidate_v0]
  admissible_rat := by
    norm_num [Ck_candidate_v0, Ct_candidate_v0, Cm_candidate_v0, Cscale_candidate_v0]

/-- Labelled candidate-v0 register. -/
def OTSARegister_candidate_v0 : LabelledOTSAConstantRegister where
  label := "OTSA candidate constants v0"
  status := ConstantStatus.analytic_candidate
  sourceNote :=
    "Candidate only: Ck=3/50 follows the narrative C0 ~= 0.058; Ct, Cm, and Cscale must be replaced by sourced rational majorants before certification."
  cert := OTSACert_candidate_v0

/-- The candidate-v0 certificate proves the TS23 admissibility inequality. -/
theorem candidate_v0_scaledOTSAAdmissible :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat OTSACert_candidate_v0) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat OTSACert_candidate_v0

/-- The candidate-v0 register carries the expected analytic-candidate status. -/
theorem candidate_v0_status :
    OTSARegister_candidate_v0.status = ConstantStatus.analytic_candidate :=
  rfl

/-- The candidate-v0 register also feeds TS23 through TS26. -/
theorem candidate_v0_register_scaledOTSAAdmissible :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat OTSARegister_candidate_v0.cert) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat OTSARegister_candidate_v0.cert

end Goldbach
end TS28
