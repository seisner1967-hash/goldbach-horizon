import Mathlib.Tactic
import TS.Goldbach.Strong.TS32.OTSATraceMajorantRoadmap

namespace TS33
namespace Goldbach

/-!
# TS33 - OTSA Final Majorants Roadmap

This sprint packages the last two asymptotic OTSA majorant targets:
the Mellin-tail contribution and the scale-transfer cost. It remains a
roadmap, not a final analytic proof: the constants are accepted only through
explicit local contracts.
-/

/--
Analytic contract for the Mellin-tail contribution.

A future proof of the smoothed Mellin tail estimate should instantiate this
structure with a rational upper bound `Cm <= 1`.
-/
structure MellinTailMajorantContract where
  Cm_bound : Rat
  Cm_pos : 0 < Cm_bound
  Cm_le_one : Cm_bound <= 1

/--
Analytic contract for the scale-transfer contribution.

This records the cost of transporting the padded short-interval scale into the
OTSA residual layer. A future scale-transfer proof should instantiate this
structure with `Cscale <= 2`.
-/
structure ScaleTransferMajorantContract where
  Cscale_bound : Rat
  Cscale_pos : 0 < Cscale_bound
  Cscale_le_two : Cscale_bound <= 2

/-- Candidate v3 keeps the TS32 spectral-kernel majorant. -/
def Ck_v3 : Rat :=
  TS32.Goldbach.Ck_v2

/-- Candidate v3 uses the TS32 trace target. -/
def Ct_target_v3 : Rat :=
  TS32.Goldbach.Ct_target_v2

/-- Candidate v3 target for the Mellin-tail majorant. -/
def Cm_target_v3 : Rat :=
  1

/-- Candidate v3 target for the scale-transfer majorant. -/
def Cscale_target_v3 : Rat :=
  2

/-- Exact target value if all v3 targets are saturated. -/
theorem candidate_v3_target_scaled_value :
    Cscale_target_v3 * (Ck_v3 * Ct_target_v3 + Cm_target_v3) = 103 / 50 := by
  norm_num [Cscale_target_v3, Ck_v3, Ct_target_v3, Cm_target_v3,
    TS32.Goldbach.Ck_v2, TS32.Goldbach.Ct_target_v2, TS31.Goldbach.Ck_v1]

/-- The saturated v3 target remains far below the TS23 threshold `26`. -/
theorem candidate_v3_target_scaled_le_26 :
    Cscale_target_v3 * (Ck_v3 * Ct_target_v3 + Cm_target_v3) <= 26 := by
  rw [candidate_v3_target_scaled_value]
  norm_num

/--
Any constants satisfying the three v3 contracts are OTSA-admissible.

This is pure rational arithmetic. The analytic work is isolated in the three
contract structures.
-/
theorem candidate_v3_scaled_le_26
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    Hs.Cscale_bound * (Ck_v3 * Ht.Ct_bound + Hm.Cm_bound) <= 26 := by
  have hInner :
      Ck_v3 * Ht.Ct_bound + Hm.Cm_bound <= 103 / 100 := by
    have hCt : Ht.Ct_bound <= (1 / 2 : Rat) := Ht.Ct_le_half
    have hCm : Hm.Cm_bound <= (1 : Rat) := Hm.Cm_le_one
    norm_num [Ck_v3, TS32.Goldbach.Ck_v2, TS31.Goldbach.Ck_v1] at *
    nlinarith
  have hInner_nonneg :
      0 <= Ck_v3 * Ht.Ct_bound + Hm.Cm_bound := by
    have hk_nonneg : 0 <= Ck_v3 := by
      norm_num [Ck_v3, TS32.Goldbach.Ck_v2, TS31.Goldbach.Ck_v1]
    exact add_nonneg
      (mul_nonneg hk_nonneg (le_of_lt Ht.Ct_pos))
      (le_of_lt Hm.Cm_pos)
  have hProd :
      Hs.Cscale_bound * (Ck_v3 * Ht.Ct_bound + Hm.Cm_bound) <=
        (2 : Rat) * (103 / 100) := by
    exact mul_le_mul Hs.Cscale_le_two hInner hInner_nonneg
      (by norm_num : (0 : Rat) <= 2)
  nlinarith

/-- Candidate v3 OTSA rational certificate, conditional on the three contracts. -/
def OTSACert_candidate_v3
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    TS26.Goldbach.OTSARationalCertificate where
  Ck := Ck_v3
  Ct := Ht.Ct_bound
  Cm := Hm.Cm_bound
  Cscale := Hs.Cscale_bound
  Ck_pos := by norm_num [Ck_v3, TS32.Goldbach.Ck_v2, TS31.Goldbach.Ck_v1]
  Ct_pos := Ht.Ct_pos
  Cm_pos := Hm.Cm_pos
  Cscale_pos := Hs.Cscale_pos
  admissible_rat := candidate_v3_scaled_le_26 Ht Hm Hs

/-- Labelled TS28 register for conditional candidate v3. -/
def OTSARegister_candidate_v3
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    TS28.Goldbach.LabelledOTSAConstantRegister where
  label := "OTSA final-majorants candidate v3"
  status := TS28.Goldbach.ConstantStatus.analytic_candidate
  sourceNote :=
    "Conditional candidate v3: trace, Mellin-tail, and scale-transfer majorants are supplied by explicit contracts. This is not a final certified package until those contracts are analytically instantiated."
  cert := OTSACert_candidate_v3 Ht Hm Hs

/--
Conditional candidate-v3 provenance register.

There are no raw placeholder constants in this package: the trace, Mellin-tail,
and scale-transfer entries are contract-supplied conditional bounds. They are
still not certified analytic derivations.
-/
def OTSAProvenance_candidate_v3
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    TS29.Goldbach.OTSAConstantProvenanceRegister where
  Ck := TS31.Goldbach.OTSAProvenance_candidate_v1.Ck
  Ct := (TS32.Goldbach.OTSAProvenance_candidate_v2 Ht).Ct
  Cm :=
    { value := Hm.Cm_bound
      provenance := TS29.Goldbach.ConstantProvenance.numerical_experiment
      label := "Cm conditional: Mellin-tail bound <= 1, pending analytic derivation" }
  Cscale :=
    { value := Hs.Cscale_bound
      provenance := TS29.Goldbach.ConstantProvenance.numerical_experiment
      label := "Cscale conditional: padded-scale transfer cost <= 2, pending analytic derivation" }
  packageStatus := TS28.Goldbach.ConstantStatus.analytic_candidate

/-- Candidate v3 is not a final certified constant package. -/
theorem candidate_v3_not_certified
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    Not ((OTSAProvenance_candidate_v3 Ht Hm Hs).packageStatus =
      TS28.Goldbach.ConstantStatus.certified) := by
  intro h
  cases h

/-- Candidate v3 records `Cm` as conditional numerical evidence. -/
theorem candidate_v3_Cm_is_conditional
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    (OTSAProvenance_candidate_v3 Ht Hm Hs).Cm.provenance =
      TS29.Goldbach.ConstantProvenance.numerical_experiment :=
  rfl

/-- Candidate v3 records `Cscale` as conditional numerical evidence. -/
theorem candidate_v3_Cscale_is_conditional
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    (OTSAProvenance_candidate_v3 Ht Hm Hs).Cscale.provenance =
      TS29.Goldbach.ConstantProvenance.numerical_experiment :=
  rfl

/-- Conditional candidate v3 feeds TS23 through TS26. -/
theorem candidate_v3_scaledOTSAAdmissible
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat
        (OTSACert_candidate_v3 Ht Hm Hs)) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat
    (OTSACert_candidate_v3 Ht Hm Hs)

/-- The labelled conditional candidate-v3 register also feeds TS23 through TS26. -/
theorem candidate_v3_register_scaledOTSAAdmissible
    (Ht : TS32.Goldbach.TraceMajorantContract)
    (Hm : MellinTailMajorantContract)
    (Hs : ScaleTransferMajorantContract) :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat
        (OTSARegister_candidate_v3 Ht Hm Hs).cert) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat
    (OTSARegister_candidate_v3 Ht Hm Hs).cert

end Goldbach
end TS33
