import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.SetIntegral
import TS.Goldbach.Strong.TS69.TriangleSplineIPPBranchSplit

namespace TS70
namespace MellinJackson

/-!
# TS70 - Triangle Spline IPP Branch Split Proof

This sprint discharges the branch-splitting contract isolated in TS69.

The split uses the disjoint decomposition
`[-1, 1] = [-1, 0] union (0, 1]`, encoded by TS69 as
`leftBranchSet` and `rightBranchSet`. The proof first records the topological
union and disjointness facts, then splits the restricted measure and the two
concrete IPP integrals.

No conversion of `(0, 1]` to `[0, 1]`, affine integration by parts,
distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimate is proved here.
-/

open MeasureTheory Set

/-- The TS69 branch sets cover `[-1, 1]`. -/
theorem branch_union_eq_Icc :
    Set.union
        TS69.MellinJackson.leftBranchSet
        TS69.MellinJackson.rightBranchSet
      =
    Icc (-1 : Real) 1 := by
  ext x
  constructor
  case mp =>
    intro hx
    rcases hx with hx | hx
    case inl =>
      unfold TS69.MellinJackson.leftBranchSet at hx
      exact And.intro hx.1 (le_trans hx.2 (by norm_num : (0 : Real) <= 1))
    case inr =>
      unfold TS69.MellinJackson.rightBranchSet at hx
      exact And.intro
        (le_trans (by norm_num : (-1 : Real) <= 0) (le_of_lt hx.1))
        hx.2
  case mpr =>
    intro hx
    by_cases h : x <= 0
    case pos =>
      left
      unfold TS69.MellinJackson.leftBranchSet
      exact And.intro hx.1 h
    case neg =>
      right
      unfold TS69.MellinJackson.rightBranchSet
      exact And.intro (lt_of_not_ge h) hx.2

/-- The TS69 left and right branch sets are disjoint. -/
theorem disjoint_left_right_branch :
    Disjoint
      TS69.MellinJackson.leftBranchSet
      TS69.MellinJackson.rightBranchSet := by
  rw [Set.disjoint_left]
  intro x hxL hxR
  unfold TS69.MellinJackson.leftBranchSet at hxL
  unfold TS69.MellinJackson.rightBranchSet at hxR
  exact not_lt_of_ge hxL.2 hxR.1

/--
The restricted measure on `[-1, 1]` splits as the sum of the two branch
restricted measures.
-/
theorem restrict_Icc_eq_left_add_right :
    (volume : Measure Real).restrict (Icc (-1 : Real) 1)
      =
    TS69.MellinJackson.leftBranchMeasure
      +
    TS69.MellinJackson.rightBranchMeasure := by
  rw [branch_union_eq_Icc.symm]
  unfold TS69.MellinJackson.leftBranchMeasure
  unfold TS69.MellinJackson.rightBranchMeasure
  exact
    Measure.restrict_union
      disjoint_left_right_branch
      measurableSet_Ioc

/-- Generic branch split for an integrable function. -/
theorem integral_branch_split
    (f : Real -> Complex)
    (hf : Integrable f (volume : Measure Real)) :
    integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1)) f
      =
    integral TS69.MellinJackson.leftBranchMeasure f
      +
    integral TS69.MellinJackson.rightBranchMeasure f := by
  rw [restrict_Icc_eq_left_add_right]
  exact
    integral_add_measure
      (by
        simpa [TS69.MellinJackson.leftBranchMeasure] using
          hf.mono_measure Measure.restrict_le_self)
      (by
        simpa [TS69.MellinJackson.rightBranchMeasure] using
          hf.mono_measure Measure.restrict_le_self)

/-- Branch split for the left IPP integrand. -/
theorem left_integral_split
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
      (TS67.MellinJackson.leftIPPIntegrand phi)
      =
    integral TS69.MellinJackson.leftBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi)
      +
    integral TS69.MellinJackson.rightBranchMeasure
      (TS67.MellinJackson.leftIPPIntegrand phi) := by
  exact
    integral_branch_split
      (TS67.MellinJackson.leftIPPIntegrand phi)
      (by
        simpa [TS67.MellinJackson.leftIPPIntegrand] using
          TS65.MellinJackson.triangleSpline_mul_testFunctionDeriv_integrable phi)

/-- Branch split for the right IPP integrand. -/
theorem right_integral_split
    (phi : TS62.MellinJackson.TriangleSplineConcreteTestFunction) :
    integral ((volume : Measure Real).restrict (Icc (-1 : Real) 1))
      (TS67.MellinJackson.rightIPPIntegrand phi)
      =
    integral TS69.MellinJackson.leftBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi)
      +
    integral TS69.MellinJackson.rightBranchMeasure
      (TS67.MellinJackson.rightIPPIntegrand phi) := by
  exact
    integral_branch_split
      (TS67.MellinJackson.rightIPPIntegrand phi)
      (by
        simpa [TS67.MellinJackson.rightIPPIntegrand] using
          TS65.MellinJackson.triangleSplineDeriv_mul_testFunction_integrable phi)

/-- Concrete discharge of the TS69 branch-splitting contract. -/
def triangleSplineIPPBranchSplit :
    TS69.MellinJackson.TriangleSplineIPPBranchSplit where
  left_integral_split := by
    intro phi
    exact left_integral_split phi
  right_integral_split := by
    intro phi
    exact right_integral_split phi

/-- Target proposition for the concrete TS70 branch-splitting discharge. -/
def TriangleSplineIPPBranchSplitProofTarget : Prop :=
  Nonempty TS69.MellinJackson.TriangleSplineIPPBranchSplit

/-- TS70 discharges the TS69 target. -/
theorem triangleSplineIPPBranchSplitTarget :
    TS69.MellinJackson.TriangleSplineIPPBranchSplitTarget :=
  Nonempty.intro triangleSplineIPPBranchSplit

/-- TS70 also provides its local proof target. -/
theorem triangleSplineIPPBranchSplitProofTarget :
    TriangleSplineIPPBranchSplitProofTarget :=
  Nonempty.intro triangleSplineIPPBranchSplit

end MellinJackson
end TS70
