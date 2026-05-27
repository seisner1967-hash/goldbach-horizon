import Mathlib.Tactic
import TS.Goldbach.Strong.TS25.PaddedScaleOTSAFeasibility

namespace TS26
namespace Goldbach

/--
A rational certificate for the scaled OTSA admissibility inequality.

All constants are rational upper bounds. This avoids floating-point arithmetic
and keeps the certificate auditable by exact rational normalization.
-/
structure OTSARationalCertificate where
  Ck : Rat
  Ct : Rat
  Cm : Rat
  Cscale : Rat
  Ck_pos : 0 < Ck
  Ct_pos : 0 < Ct
  Cm_pos : 0 < Cm
  Cscale_pos : 0 < Cscale
  admissible_rat :
    Cscale * (Ck * Ct + Cm) <= 26

/-- Convert a rational certificate into the real constants used by TS23. -/
noncomputable def scaledConstantsOfRat
    (C : OTSARationalCertificate) :
    TS23.Goldbach.ScaledOTSAConstants where
  Ck := (C.Ck : Real)
  Ct := (C.Ct : Real)
  Cm := (C.Cm : Real)
  Cscale := (C.Cscale : Real)
  Ck_pos := by exact_mod_cast C.Ck_pos
  Ct_pos := by exact_mod_cast C.Ct_pos
  Cm_pos := by exact_mod_cast C.Cm_pos
  Cscale_pos := by exact_mod_cast C.Cscale_pos

/-- The real scaled constant is the cast of the rational scaled constant. -/
theorem scaledCoupledConstant_of_rat
    (C : OTSARationalCertificate) :
    TS23.Goldbach.scaledCoupledConstant (scaledConstantsOfRat C) =
      ((C.Cscale * (C.Ck * C.Ct + C.Cm) : Rat) : Real) := by
  unfold TS23.Goldbach.scaledCoupledConstant
  unfold scaledConstantsOfRat
  norm_num

/-- A rational certificate proves the real TS23 admissibility condition. -/
theorem scaledOTSAAdmissible_of_rat
    (C : OTSARationalCertificate) :
    TS23.Goldbach.ScaledOTSAAdmissible (scaledConstantsOfRat C) := by
  unfold TS23.Goldbach.ScaledOTSAAdmissible
  rw [scaledCoupledConstant_of_rat C]
  exact_mod_cast C.admissible_rat

end Goldbach
end TS26
