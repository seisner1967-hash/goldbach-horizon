import Mathlib.Tactic
import TS.Goldbach.Strong.TS42.MellinTailSplineRoadmap

namespace TS43
namespace MellinJackson

/-!
# TS43 - Triangle Spline Pointwise Facts

This sprint proves elementary pointwise facts about the weak-derivative
representative introduced in TS42.

It does not prove the Lebesgue integral, the Sobolev derivative identity,
Plancherel, or the Fourier-tail estimate.
-/

/--
On the left open interval `(-1, 0)`, the weak-derivative representative of the
triangle spline is `1`.
-/
theorem triangleSplineDeriv_eq_one_of_left
    {x : Real}
    (hx1 : -1 < x)
    (hx0 : x < 0) :
    TS42.MellinJackson.triangleSplineDeriv x = 1 := by
  have hleft : -1 < x /\ x < 0 := And.intro hx1 hx0
  simp [TS42.MellinJackson.triangleSplineDeriv, hleft]

/--
On the right open interval `(0, 1)`, the weak-derivative representative of the
triangle spline is `-1`.
-/
theorem triangleSplineDeriv_eq_neg_one_of_right
    {x : Real}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    TS42.MellinJackson.triangleSplineDeriv x = -1 := by
  have hleft : Not (-1 < x /\ x < 0) := by
    intro h
    linarith
  have hright : 0 < x /\ x < 1 := And.intro hx0 hx1
  simp [TS42.MellinJackson.triangleSplineDeriv, hleft, hright]

/--
Outside the two open intervals `(-1, 0)` and `(0, 1)`, the representative is
`0`.
-/
theorem triangleSplineDeriv_eq_zero_of_not_left_not_right
    {x : Real}
    (hleft : Not (-1 < x /\ x < 0))
    (hright : Not (0 < x /\ x < 1)) :
    TS42.MellinJackson.triangleSplineDeriv x = 0 := by
  simp [TS42.MellinJackson.triangleSplineDeriv, hleft, hright]

/--
The derivative representative is pointwise bounded in absolute value by `1`.

This is the key pointwise input for the future `L2` norm estimate.
-/
theorem abs_triangleSplineDeriv_le_one
    (x : Real) :
    |TS42.MellinJackson.triangleSplineDeriv x| <= 1 := by
  by_cases hleft : -1 < x /\ x < 0
  case pos =>
    simp [TS42.MellinJackson.triangleSplineDeriv, hleft]
  case neg =>
    by_cases hright : 0 < x /\ x < 1
    case pos =>
      simp [TS42.MellinJackson.triangleSplineDeriv, hleft, hright]
    case neg =>
      simp [TS42.MellinJackson.triangleSplineDeriv, hleft, hright]

end MellinJackson
end TS43
