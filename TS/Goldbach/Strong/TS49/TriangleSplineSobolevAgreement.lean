import Mathlib.Tactic
import TS.Goldbach.Strong.TS48.BoundedSupportSnormLemma
import TS.Goldbach.Strong.TS41.FourierAPIProbe

namespace TS49
namespace MellinJackson

open MeasureTheory

/-!
# TS49 - Triangle Spline Sobolev Agreement

This sprint isolates the Sobolev-agreement step in the triangle-spline route
to the Mellin-tail majorant.

TS48 has already discharged the concrete derivative `snorm` bound. TS49 does
not prove the Sobolev derivative identity; it records the exact local
infrastructure needed to connect the TS41 abstract Sobolev derivative slot to
the explicit weak-derivative representative from TS42.
-/

/--
Sobolev-agreement infrastructure for the triangle spline.

The field says that the first Sobolev derivative selected by the TS41 Fourier
API ledger agrees almost everywhere with the explicit weak derivative
`triangleSplineDeriv`.
-/
structure TriangleSplineSobolevAgreementInfrastructure where
  /-- Fourier API and normalization choices from TS41. -/
  api :
    TS41.MellinJackson.FourierAPINormalizationLedger

  /-- Agreement with the explicit weak-derivative representative. -/
  sobolev_derivative_agrees :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (api.sobolevDerivative 1
        (fun x : Real => (TS42.MellinJackson.triangleSpline x : Complex)))
      (fun x : Real => (TS42.MellinJackson.triangleSplineDeriv x : Complex))

/-- Target proposition for the Sobolev-agreement step. -/
def TriangleSplineSobolevAgreementTarget : Prop :=
  Nonempty TriangleSplineSobolevAgreementInfrastructure

/-- Any supplied Sobolev-agreement infrastructure discharges the TS49 target. -/
theorem TriangleSplineSobolevAgreementTarget.of_infrastructure
    (H : TriangleSplineSobolevAgreementInfrastructure) :
    TriangleSplineSobolevAgreementTarget :=
  Nonempty.intro H

end MellinJackson
end TS49
