import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import TS.Goldbach.Strong.TS54.FourierPlancherelGapLedger
import TS.Goldbach.Strong.TS173.TriangleSplineFourierIdentificationDischarge

namespace TS174
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS174 - Triangle Spline Plancherel Interface Probe

TS173 proves the pointwise Fourier identification of the triangle spline.  This
sprint checks that this identity can be consumed by the next energy/L2 layer.

The sprint deliberately does not prove a global Plancherel theorem and does not
open the Riemann-von Mangoldt explicit-formula front.  It names the spline-side
and sinc-side `eLpNorm` quantities, states the Plancherel isometry shape needed
for this concrete function, and proves that a supplied Plancherel statement
transports immediately to the pi-scale squared-sinc candidate using TS173.
-/

/-- L2 seminorm of the complexified triangle spline. -/
noncomputable def triangleSplineTimeL2Energy :
    ENNReal :=
  eLpNorm
    TS166.Goldbach.triangleSplineAsComplex
    2
    (volume : Measure Real)

/-- L2 seminorm of Mathlib's Fourier integral of the triangle spline. -/
noncomputable def triangleSplineFourierL2Energy :
    ENNReal :=
  eLpNorm
    TS166.Goldbach.triangleSplineMathlibFourier
    2
    (volume : Measure Real)

/-- L2 seminorm of the pi-scale squared-sinc candidate from TS166. -/
noncomputable def triangleSplineSincL2Energy :
    ENNReal :=
  eLpNorm
    TS166.Goldbach.triangleSplineScaledSincCandidate
    2
    (volume : Measure Real)

/--
Concrete Plancherel statement needed for the triangle spline.

TS174 only names this statement.  It is a future analytic input, not a theorem
proved here.
-/
def TriangleSplinePlancherelIsometryStatement : Prop :=
  triangleSplineFourierL2Energy =
    triangleSplineTimeL2Energy

/--
The TS173 pointwise Fourier identity identifies the L2 seminorm of the
Mathlib Fourier transform with the L2 seminorm of the pi-scale squared-sinc
candidate.
-/
theorem triangleSplineFourierL2Energy_eq_sincL2Energy :
    triangleSplineFourierL2Energy =
      triangleSplineSincL2Energy := by
  unfold triangleSplineFourierL2Energy triangleSplineSincL2Energy
  exact
    eLpNorm_congr_ae
      (Filter.Eventually.of_forall
        TS173.Goldbach.triangleSplineFourierIdentification)

/--
If the concrete Plancherel isometry is supplied, then the squared-sinc
candidate has the same L2 seminorm as the original triangle spline.
-/
theorem triangleSplineSincL2Energy_eq_timeL2Energy_of_plancherel
    (hplancherel : TriangleSplinePlancherelIsometryStatement) :
    triangleSplineSincL2Energy =
      triangleSplineTimeL2Energy := by
  calc
    triangleSplineSincL2Energy =
        triangleSplineFourierL2Energy :=
          triangleSplineFourierL2Energy_eq_sincL2Energy.symm
    _ =
        triangleSplineTimeL2Energy :=
          hplancherel

/-- Ledger for the TS174 Plancherel interface probe. -/
structure TriangleSplinePlancherelInterfaceProbeLedger where
  ts173_fourier_identification :
    TS173.Goldbach.TriangleSplineFourierIdentificationLedger

  legacy_plancherel_gap :
    TS54.MellinJackson.FourierPlancherelGapLedger

  time_l2_energy :
    ENNReal

  time_l2_energy_eq :
    time_l2_energy = triangleSplineTimeL2Energy

  fourier_l2_energy :
    ENNReal

  fourier_l2_energy_eq :
    fourier_l2_energy = triangleSplineFourierL2Energy

  sinc_l2_energy :
    ENNReal

  sinc_l2_energy_eq :
    sinc_l2_energy = triangleSplineSincL2Energy

  fourier_l2_matches_sinc_l2 :
    triangleSplineFourierL2Energy =
      triangleSplineSincL2Energy

  plancherel_statement :
    Prop

  plancherel_statement_eq :
    plancherel_statement =
      TriangleSplinePlancherelIsometryStatement

  plancherel_consumption :
    TriangleSplinePlancherelIsometryStatement ->
      triangleSplineSincL2Energy =
        triangleSplineTimeL2Energy

  plancherel_not_proved :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS174 Plancherel interface probe ledger. -/
noncomputable def triangleSplinePlancherelInterfaceProbeLedger :
    TriangleSplinePlancherelInterfaceProbeLedger where
  ts173_fourier_identification :=
    TS173.Goldbach.triangleSplineFourierIdentificationLedger
  legacy_plancherel_gap :=
    TS54.MellinJackson.fourierPlancherelGapLedger
  time_l2_energy := triangleSplineTimeL2Energy
  time_l2_energy_eq := rfl
  fourier_l2_energy := triangleSplineFourierL2Energy
  fourier_l2_energy_eq := rfl
  sinc_l2_energy := triangleSplineSincL2Energy
  sinc_l2_energy_eq := rfl
  fourier_l2_matches_sinc_l2 :=
    triangleSplineFourierL2Energy_eq_sincL2Energy
  plancherel_statement :=
    TriangleSplinePlancherelIsometryStatement
  plancherel_statement_eq := rfl
  plancherel_consumption :=
    triangleSplineSincL2Energy_eq_timeL2Energy_of_plancherel
  plancherel_not_proved := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS174. -/
def TriangleSplinePlancherelInterfaceProbeTarget : Prop :=
  Nonempty TriangleSplinePlancherelInterfaceProbeLedger

/-- The TS174 Plancherel interface probe target is populated. -/
theorem triangleSplinePlancherelInterfaceProbeTarget :
    TriangleSplinePlancherelInterfaceProbeTarget :=
  Nonempty.intro triangleSplinePlancherelInterfaceProbeLedger

end Goldbach
end TS174
