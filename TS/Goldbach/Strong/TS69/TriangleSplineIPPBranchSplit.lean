import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import TS.Goldbach.Strong.TS68.TriangleSplineIPPIntegralRestrictionProof

namespace TS69
namespace MellinJackson

/-!
# TS69 - Triangle Spline IPP Branch Split

This sprint records the branch-splitting contract for the restricted
triangle-spline integration-by-parts route.

TS68 restricts the two global IPP product integrals to `[-1, 1]`. TS69 names
the two disjoint branch domains `[-1, 0]` and `(0, 1]`, then records the exact
contract saying that each restricted integral should split as the sum of its
left-branch and right-branch integrals.

No branch-splitting proof, affine integration by parts, distributional
derivative identity, Sobolev-slot agreement, Plancherel, or Fourier-tail
estimate is proved here.
-/

open MeasureTheory Set

/-- Left branch of the triangle-spline support: `[-1, 0]`. -/
def leftBranchSet : Set Real :=
  Icc (-1 : Real) 0

/--
Right branch of the triangle-spline support: `(0, 1]`.

Using `Ioc` avoids double-counting the point `0` when splitting `[-1, 1]`.
-/
def rightBranchSet : Set Real :=
  Ioc (0 : Real) 1

/-- Measure restricted to the left branch `[-1, 0]`. -/
noncomputable def leftBranchMeasure : Measure Real :=
  (volume : Measure Real).restrict leftBranchSet

/-- Measure restricted to the right branch `(0, 1]`. -/
noncomputable def rightBranchMeasure : Measure Real :=
  (volume : Measure Real).restrict rightBranchSet

/--
Branch-splitting contract for the two concrete IPP products.

This is the next integral-level step after TS68. It does not prove affine
integration by parts. It only states that the integral on `[-1, 1]` splits
into the left branch and the right branch.
-/
structure TriangleSplineIPPBranchSplit where
  left_integral_split :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral
        ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
        (TS67.MellinJackson.leftIPPIntegrand phi)
      =
      integral leftBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)
      +
      integral rightBranchMeasure
        (TS67.MellinJackson.leftIPPIntegrand phi)

  right_integral_split :
    forall phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction,
      integral
        ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
        (TS67.MellinJackson.rightIPPIntegrand phi)
      =
      integral leftBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)
      +
      integral rightBranchMeasure
        (TS67.MellinJackson.rightIPPIntegrand phi)

/-- Inputs available before proving the branch split. -/
structure TriangleSplineIPPBranchSplitInputs where
  integral_restriction :
    TS67.MellinJackson.TriangleSplineIPPIntegralRestriction

/-- Concrete inputs from TS68. -/
def triangleSplineIPPBranchSplitInputs :
    TriangleSplineIPPBranchSplitInputs where
  integral_restriction :=
    TS68.MellinJackson.triangleSplineIPPIntegralRestriction

/-- Target proposition for TS69. -/
def TriangleSplineIPPBranchSplitTarget : Prop :=
  Nonempty TriangleSplineIPPBranchSplit

/-- Input target proposition. -/
def TriangleSplineIPPBranchSplitInputsTarget : Prop :=
  Nonempty TriangleSplineIPPBranchSplitInputs

/-- TS68 supplies the input package for the future branch-splitting proof. -/
theorem triangleSplineIPPBranchSplitInputsTarget :
    TriangleSplineIPPBranchSplitInputsTarget :=
  Nonempty.intro triangleSplineIPPBranchSplitInputs

end MellinJackson
end TS69
