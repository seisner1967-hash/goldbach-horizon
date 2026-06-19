import Mathlib.Tactic
import TS.Goldbach.Strong.TS166.TriangleSplineFourierIdentificationReduction
import TS.Goldbach.Strong.TS168.TriangleSplineBranchIntegralRouteProbe
import TS.Goldbach.Strong.TS169.TriangleSplineBranchClosedFormRecombination
import TS.Goldbach.Strong.TS170.TriangleSplineRightBranchIntegralEvaluation
import TS.Goldbach.Strong.TS171.TriangleSplineLeftBranchIntegralEvaluation
import TS.Goldbach.Strong.TS172.TriangleSplineFourierBranchSplit

namespace TS173
namespace Goldbach

/-!
# TS173 - Triangle Spline Fourier Identification Discharge

TS168 proved that four local branch-route obligations imply the TS166 Fourier
identification target.  TS169 through TS172 discharged those four obligations:
closed-form recombination, right branch evaluation, left branch evaluation, and
the global Fourier branch split.

This sprint applies the TS168 implication to those four proven blocks and
upgrades the TS166 Fourier-identification target from a compiled statement to a
Lean theorem.  It does not claim Plancherel, the Riemann-von Mangoldt explicit
formula, or any Goldbach conclusion.
-/

/--
The unconditional discharge of the TS166 Fourier identification statement.

This is pure logical assembly: it feeds the four TS169--TS172 proofs into the
TS168 branch-route implication.
-/
theorem triangleSplineFourierIdentification :
    TS166.Goldbach.TriangleSplineFourierIdentificationStatement := by
  exact
    TS168.Goldbach.branchIntegralRoute_implies_ts166
      TS172.Goldbach.branchSplitFourier
      TS171.Goldbach.leftBranchIntegralEvaluation
      TS170.Goldbach.rightBranchIntegralEvaluation
      TS169.Goldbach.branchClosedFormRecombination

/-- Ledger recording the successful Fourier-identification discharge. -/
structure TriangleSplineFourierIdentificationLedger where
  ts172_split_discharge :
    TS172.Goldbach.TriangleSplineFourierBranchSplitLedger

  fourier_identification :
    TS166.Goldbach.TriangleSplineFourierIdentificationStatement

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS173 Fourier-identification ledger. -/
noncomputable def triangleSplineFourierIdentificationLedger :
    TriangleSplineFourierIdentificationLedger where
  ts172_split_discharge :=
    TS172.Goldbach.triangleSplineFourierBranchSplitLedger
  fourier_identification := triangleSplineFourierIdentification
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS173. -/
def TriangleSplineFourierIdentificationTarget : Prop :=
  Nonempty TriangleSplineFourierIdentificationLedger

/-- The TS173 Fourier-identification target is populated. -/
theorem triangleSplineFourierIdentificationTarget :
    TriangleSplineFourierIdentificationTarget :=
  Nonempty.intro triangleSplineFourierIdentificationLedger

end Goldbach
end TS173
