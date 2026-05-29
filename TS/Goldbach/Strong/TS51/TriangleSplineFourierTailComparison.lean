import Mathlib.Tactic
import TS.Goldbach.Strong.TS40.FourierTailRoadmap
import TS.Goldbach.Strong.TS50.TriangleSplineTailAssembly

namespace TS51
namespace MellinJackson

open MeasureTheory
open scoped ENNReal

/-!
# TS51 - Triangle Spline Fourier Tail Comparison

This sprint isolates the final Fourier-tail comparison input needed by the
triangle-spline route.

TS50 already wires the concrete TS48 derivative norm bound and the TS49
Sobolev-agreement infrastructure into the TS42 tail package. TS51 makes the
remaining tail comparison explicit as a local object, without proving
Plancherel, choosing a concrete Fourier normalization, or proving the Sobolev
identity.
-/

/-- Complex-valued triangle spline representative. -/
noncomputable def triangleSplineComplex (x : Real) : Complex :=
  (TS42.MellinJackson.triangleSpline x : Complex)

/--
High-frequency tail representative for a selected Fourier transform and
cutoff.
-/
noncomputable def triangleSplineFourierTail
    (fourierTransform : (Real -> Complex) -> (Real -> Complex))
    (cutoff : Real) :
    Real -> Complex :=
  fun xi : Real =>
    if cutoff < |xi| then fourierTransform triangleSplineComplex xi else 0

/--
Fourier-tail comparison inputs for the triangle spline.

The comparison is deliberately tied to both:

- a TS40 Fourier-tail infrastructure package;
- the TS49 Sobolev-agreement infrastructure used by TS50.

The two compatibility fields ensure that the Fourier/Sobolev operators used in
the tail comparison are the same slots as the TS41 ledger carried by TS49.
-/
structure TriangleSplineFourierTailComparisonInputs where
  /-- Fourier-tail infrastructure from TS40. -/
  fourierTail :
    TS40.MellinJackson.FourierTailInfrastructure

  /-- Sobolev agreement infrastructure from TS49. -/
  sobolev :
    TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure

  /-- The Fourier transform agrees with the TS41 API slot. -/
  fourierTransform_eq_api :
    fourierTail.fourierTransform = sobolev.api.fourierTransform

  /-- The Sobolev derivative agrees with the TS41 API slot. -/
  sobolevDerivative_eq_api :
    fourierTail.sobolevDerivative = sobolev.api.sobolevDerivative

  /-- Frequency cutoff for the triangle-spline tail comparison. -/
  cutoff :
    Real

  /-- The cutoff is positive. -/
  cutoff_pos :
    0 < cutoff

  /-- The cutoff is large enough to absorb the concrete TS48 `snorm <= 2` bound. -/
  cutoff_ge_two :
    2 <= cutoff

  /-- The remaining concrete Fourier-tail estimate needed for the spline route. -/
  tail_snorm_le_one :
    snorm
      (triangleSplineFourierTail fourierTail.fourierTransform cutoff)
      2
      (volume : Measure Real)
    <= (1 : ENNReal)

/-- Target proposition for the triangle-spline Fourier-tail comparison step. -/
def TriangleSplineFourierTailComparisonTarget : Prop :=
  Nonempty TriangleSplineFourierTailComparisonInputs

/-- Extract the explicit tail estimate from the comparison package. -/
theorem triangleSpline_tail_snorm_le_one
    (H : TriangleSplineFourierTailComparisonInputs) :
    snorm
      (triangleSplineFourierTail H.fourierTail.fourierTransform H.cutoff)
      2
      (volume : Measure Real)
    <= (1 : ENNReal) :=
  H.tail_snorm_le_one

/--
The Fourier-tail comparison package supplies the TS50 assembly inputs.

The TS50 field `tail_majorant_le_one` is a marker; TS51 is the place where the
actual Fourier-tail bound is recorded.
-/
def triangleSplineTailAssemblyInputs_from_fourierTailComparison
    (H : TriangleSplineFourierTailComparisonInputs) :
    TS50.MellinJackson.TriangleSplineTailAssemblyInputs where
  sobolev := H.sobolev
  tail_majorant_le_one := True.intro

/-- A Fourier-tail comparison target yields the TS50 assembly target. -/
theorem triangleSplineTailAssemblyTarget_of_fourierTailComparisonTarget
    (H : TriangleSplineFourierTailComparisonTarget) :
    TS50.MellinJackson.TriangleSplineTailAssemblyTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (triangleSplineTailAssemblyInputs_from_fourierTailComparison h)

/-- A Fourier-tail comparison target yields the TS42 triangle-spline target. -/
theorem triangleSplineTailTarget_of_fourierTailComparisonTarget
    (H : TriangleSplineFourierTailComparisonTarget) :
    TS42.MellinJackson.TriangleSplineTailTarget :=
  TS50.MellinJackson.triangleSplineTailTarget_of_assembly
    (triangleSplineTailAssemblyTarget_of_fourierTailComparisonTarget H)

/--
A Fourier-tail comparison target gives a TS33 Mellin-tail contract target.
-/
theorem mellinTailContractTarget_of_fourierTailComparisonTarget
    (H : TriangleSplineFourierTailComparisonTarget) :
    Nonempty TS33.Goldbach.MellinTailMajorantContract :=
  TS50.MellinJackson.mellinTailContractTarget_of_assemblyTarget
    (triangleSplineTailAssemblyTarget_of_fourierTailComparisonTarget H)

end MellinJackson
end TS51
