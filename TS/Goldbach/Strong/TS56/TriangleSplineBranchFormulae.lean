import Mathlib.Tactic
import TS.Goldbach.Strong.TS55.TriangleSplineSobolevAgreementLedger

namespace TS56
namespace MellinJackson

open Set

/-!
# TS56 - Triangle Spline Branch Formulae

This sprint proves the elementary branch formulae for the triangle spline.

It is the first concrete Sobolev-side refinement after TS55: before proving
classical derivatives, boundary control, or a distributional derivative
identity, we record the exact affine formulae on the two branches and the
vanishing outside `[-1, 1]`.
-/

/--
Left branch formula for the triangle spline.

On `[-1, 0]`, one has `|x| = -x`, hence `triangleSpline x = 1 + x`.
-/
theorem triangleSpline_eq_one_add_of_left
    {x : Real}
    (hx1 : -1 <= x)
    (hx0 : x <= 0) :
    TS42.MellinJackson.triangleSpline x = 1 + x := by
  unfold TS42.MellinJackson.triangleSpline
  have hsupp : -1 <= x /\ x <= 1 := by
    exact And.intro hx1 (by linarith)
  have habs : |x| = -x := abs_of_nonpos hx0
  simp [hsupp, habs]

/--
Right branch formula for the triangle spline.

On `[0, 1]`, one has `|x| = x`, hence `triangleSpline x = 1 - x`.
-/
theorem triangleSpline_eq_one_sub_of_right
    {x : Real}
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    TS42.MellinJackson.triangleSpline x = 1 - x := by
  unfold TS42.MellinJackson.triangleSpline
  have hsupp : -1 <= x /\ x <= 1 := by
    exact And.intro (by linarith) hx1
  have habs : |x| = x := abs_of_nonneg hx0
  simp [hsupp, habs]

/-- Outside `[-1, 1]`, the triangle spline vanishes. -/
theorem triangleSpline_eq_zero_outside_Icc
    {x : Real}
    (hx : Not ((Icc (-1 : Real) 1) x)) :
  TS42.MellinJackson.triangleSpline x = 0 := by
  unfold TS42.MellinJackson.triangleSpline
  have hnot : Not (-1 <= x /\ x <= 1) := by
    intro hs
    exact hx (by simpa [mem_Icc] using hs)
  simp [hnot]

/-!
## Branch-formula package
-/

/-- Package of branch formulae for the next Sobolev-side sprint. -/
structure TriangleSplineBranchFormulae where
  left_formula :
    forall {x : Real}, -1 <= x -> x <= 0 ->
      TS42.MellinJackson.triangleSpline x = 1 + x

  right_formula :
    forall {x : Real}, 0 <= x -> x <= 1 ->
      TS42.MellinJackson.triangleSpline x = 1 - x

  zero_outside :
    forall {x : Real}, Not ((Icc (-1 : Real) 1) x) ->
      TS42.MellinJackson.triangleSpline x = 0

/-- Concrete branch-formula package. -/
def triangleSplineBranchFormulae : TriangleSplineBranchFormulae where
  left_formula := by
    intro x hx1 hx0
    exact triangleSpline_eq_one_add_of_left hx1 hx0
  right_formula := by
    intro x hx0 hx1
    exact triangleSpline_eq_one_sub_of_right hx0 hx1
  zero_outside := by
    intro x hx
    exact triangleSpline_eq_zero_outside_Icc hx

/-- Target proposition for the branch-formula step. -/
def TriangleSplineBranchFormulaeTarget : Prop :=
  Nonempty TriangleSplineBranchFormulae

/-- The concrete branch-formula package discharges the TS56 target. -/
theorem triangleSplineBranchFormulaeTarget :
    TriangleSplineBranchFormulaeTarget :=
  Nonempty.intro triangleSplineBranchFormulae

end MellinJackson
end TS56
