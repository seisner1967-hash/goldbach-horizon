import Mathlib.Tactic
import TS.Goldbach.Strong.TS42.MellinTailSplineRoadmap
import TS.Goldbach.Strong.TS48.BoundedSupportSnormLemma
import TS.Goldbach.Strong.TS49.TriangleSplineSobolevAgreement

namespace TS50
namespace MellinJackson

open MeasureTheory

/-!
# TS50 - Triangle Spline Tail Assembly

This sprint assembles the triangle-spline route toward the Mellin-tail
majorant.

The derivative `snorm` side is concrete via TS48. The Sobolev agreement is
carried by the TS49 infrastructure, and the final Fourier-tail comparison
remains an explicit local field.
-/

/--
Assembly inputs for the triangle-spline Mellin-tail route.

The Sobolev side remains conditional through TS49. The final tail-comparison
marker stays local until the Fourier-tail normalization is instantiated.
-/
structure TriangleSplineTailAssemblyInputs where
  /-- Sobolev agreement between the TS41 slot and `triangleSplineDeriv`. -/
  sobolev :
    TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure

  /-- Future Fourier-tail comparison input. -/
  tail_majorant_le_one :
    True

/-- The concrete TS48 derivative `snorm` bound used in the TS42 package. -/
theorem triangleSplineDeriv_snorm_bound :
    snorm
      (fun x : Real =>
        (TS42.MellinJackson.triangleSplineDeriv x : Complex))
      2
      (volume : Measure Real)
    <= 2 := by
  cases TS48.MellinJackson.triangleSplineDerivativeSnormTarget with
  | intro h =>
      exact TS45.MellinJackson.deriv_snorm_bound_of_infrastructure h

/--
Assemble the TS42 triangle-spline tail infrastructure from:

- the concrete TS48 `snorm` discharge;
- the TS49 Sobolev-agreement infrastructure;
- the local tail-comparison input.
-/
def triangleSplineTailInfrastructure_from_inputs
    (H : TriangleSplineTailAssemblyInputs) :
    TS42.MellinJackson.TriangleSplineTailInfrastructure where
  api := H.sobolev.api
  deriv_snorm_bound := triangleSplineDeriv_snorm_bound
  sobolev_derivative_agrees := H.sobolev.sobolev_derivative_agrees
  tail_majorant_le_one := H.tail_majorant_le_one

/-- Conditional assembly target for the triangle-spline route. -/
def TriangleSplineTailAssemblyTarget : Prop :=
  Nonempty TriangleSplineTailAssemblyInputs

/-- If the assembly inputs are supplied, the TS42 triangle-spline target follows. -/
theorem triangleSplineTailTarget_of_assembly
    (H : TriangleSplineTailAssemblyTarget) :
    TS42.MellinJackson.TriangleSplineTailTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (triangleSplineTailInfrastructure_from_inputs h)

/-- A concrete assembly input yields the TS33 Mellin-tail contract `Cm <= 1`. -/
def mellinTailContract_from_triangleSplineAssembly
    (H : TriangleSplineTailAssemblyInputs) :
    TS33.Goldbach.MellinTailMajorantContract :=
  TS42.MellinJackson.mellinTailContract_from_triangleSpline
    (triangleSplineTailInfrastructure_from_inputs H)

/--
If the assembly target is supplied, then the TS33 Mellin-tail contract exists.
-/
theorem mellinTailContractTarget_of_assemblyTarget
    (H : TriangleSplineTailAssemblyTarget) :
    Nonempty TS33.Goldbach.MellinTailMajorantContract := by
  cases H with
  | intro h =>
      exact Nonempty.intro (mellinTailContract_from_triangleSplineAssembly h)

end MellinJackson
end TS50
