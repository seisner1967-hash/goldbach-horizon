import Mathlib.Tactic
import TS.Goldbach.Strong.TS26.OTSANumericalFeasibility

namespace TS27
namespace Goldbach

/--
A labelled register entry for rational OTSA constants.

The label and source note are documentation fields. The mathematical content is
the exact rational certificate carried by `cert`.
-/
structure OTSAConstantRegister where
  label : String
  status : String
  sourceNote : String
  cert : TS26.Goldbach.OTSARationalCertificate

/--
Smoke-test spectral-kernel constant.

This is deliberately not a final certified OTSA value. It records the narrative
candidate `Ck = 0.06 = 3/50` for testing the TS26 rational pipeline.
-/
def Ck_smoke_test : Rat :=
  3 / 50

/-- Smoke-test trace constant. Not a final certified OTSA value. -/
def Ct_smoke_test : Rat :=
  1

/-- Smoke-test Mellin-tail constant. Not a final certified OTSA value. -/
def Cm_smoke_test : Rat :=
  1

/-- Smoke-test scale-transfer constant. Not a final certified OTSA value. -/
def Cscale_smoke_test : Rat :=
  1

/--
A non-final rational certificate used only to verify the TS26 plumbing.

The admissibility check is exact:

  1 * ((3/50) * 1 + 1) = 53/50 <= 26.
-/
def OTSACert_smoke_test : TS26.Goldbach.OTSARationalCertificate where
  Ck := Ck_smoke_test
  Ct := Ct_smoke_test
  Cm := Cm_smoke_test
  Cscale := Cscale_smoke_test
  Ck_pos := by norm_num [Ck_smoke_test]
  Ct_pos := by norm_num [Ct_smoke_test]
  Cm_pos := by norm_num [Cm_smoke_test]
  Cscale_pos := by norm_num [Cscale_smoke_test]
  admissible_rat := by
    norm_num [Ck_smoke_test, Ct_smoke_test, Cm_smoke_test, Cscale_smoke_test]

/-- Registry entry for the non-final smoke-test constants. -/
def OTSARegister_smoke_test : OTSAConstantRegister where
  label := "OTSA smoke-test constants"
  status := "smoke_test_not_final"
  sourceNote :=
    "Pipeline test only: Ck=3/50 follows the narrative C0 ~= 0.058; Ct, Cm, and Cscale are placeholders."
  cert := OTSACert_smoke_test

/-- The smoke-test register yields a TS23 admissibility proof through TS26. -/
theorem smoke_test_scaledOTSAAdmissible :
    TS23.Goldbach.ScaledOTSAAdmissible
      (TS26.Goldbach.scaledConstantsOfRat OTSARegister_smoke_test.cert) :=
  TS26.Goldbach.scaledOTSAAdmissible_of_rat OTSARegister_smoke_test.cert

end Goldbach
end TS27
