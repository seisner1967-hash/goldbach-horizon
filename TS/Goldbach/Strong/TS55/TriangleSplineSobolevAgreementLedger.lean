import Mathlib.Tactic
import TS.Goldbach.Strong.TS49.TriangleSplineSobolevAgreement
import TS.Goldbach.Strong.TS43.TriangleSplinePointwise

namespace TS55
namespace MellinJackson

open MeasureTheory

/-!
# TS55 - Triangle Spline Sobolev Agreement Ledger

This sprint decomposes the TS49 Sobolev-agreement step into local
weak-derivative obligations for the triangle spline.

It does not prove the distributional derivative identity, does not choose a
test-function or Sobolev API, and does not touch Plancherel or Fourier-tail
estimates. It records the bridge from the explicit piecewise derivative
representative to the TS41 Sobolev derivative slot.
-/

/--
Local decomposition of the Sobolev agreement for the triangle spline.

The first four fields are deliberately roadmap-level markers for the classical
branch, boundary, and distributional steps. The final field is the exact TS49
agreement statement needed to connect the selected TS41 Sobolev derivative
slot to `triangleSplineDeriv`.
-/
structure TriangleSplineSobolevAgreementLedger where
  /-- Fourier API and normalization choices from TS41. -/
  api :
    TS41.MellinJackson.FourierAPINormalizationLedger

  /--
  Classical derivative agreement on the left branch `(-1, 0)`.

  A later sprint should strengthen this marker after choosing the exact
  `HasDerivAt` / `HasDerivWithinAt` API.
  -/
  left_branch_derivative :
    forall {x : Real},
      -1 < x -> x < 0 ->
      True

  /--
  Classical derivative agreement on the right branch `(0, 1)`.
  -/
  right_branch_derivative :
    forall {x : Real},
      0 < x -> x < 1 ->
      True

  /--
  Boundary and raccord data at the exceptional points `-1`, `0`, and `1`.

  These points are null for Lebesgue measure, but they are still part of the
  future integration-by-parts proof.
  -/
  boundary_control :
    True

  /--
  Distributional derivative identity.

  This is the analytic heart of the future proof: the weak derivative of the
  triangle spline is represented by `triangleSplineDeriv`.
  -/
  distributional_derivative_identity :
    True

  /--
  Translation from the distributional identity to the TS41 Sobolev derivative
  slot.
  -/
  sobolev_slot_agreement :
    Filter.EventuallyEq (ae (volume : Measure Real))
      (api.sobolevDerivative 1
        (fun x : Real => (TS42.MellinJackson.triangleSpline x : Complex)))
      (fun x : Real => (TS42.MellinJackson.triangleSplineDeriv x : Complex))

/-- A TS55 ledger gives the TS49 Sobolev-agreement infrastructure. -/
def triangleSplineSobolevAgreementInfrastructure
    (H : TriangleSplineSobolevAgreementLedger) :
    TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure where
  api := H.api
  sobolev_derivative_agrees := H.sobolev_slot_agreement

/-- Target proposition for the decomposed Sobolev route. -/
def TriangleSplineSobolevAgreementLedgerTarget : Prop :=
  Nonempty TriangleSplineSobolevAgreementLedger

/-- Any supplied TS55 ledger discharges the TS55 target. -/
theorem TriangleSplineSobolevAgreementLedgerTarget.of_ledger
    (H : TriangleSplineSobolevAgreementLedger) :
    TriangleSplineSobolevAgreementLedgerTarget :=
  Nonempty.intro H

/-- The TS55 target implies the TS49 Sobolev-agreement target. -/
theorem triangleSplineSobolevAgreementTarget_of_ledgerTarget
    (H : TriangleSplineSobolevAgreementLedgerTarget) :
    TS49.MellinJackson.TriangleSplineSobolevAgreementTarget := by
  cases H with
  | intro h =>
      exact
        TS49.MellinJackson.TriangleSplineSobolevAgreementTarget.of_infrastructure
          (triangleSplineSobolevAgreementInfrastructure h)

end MellinJackson
end TS55
