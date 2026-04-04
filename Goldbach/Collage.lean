/-
  Goldbach/Collage.lean
  Purely logical collage lemma: finite verification + asymptotic range.
-/

import Goldbach.Basic

namespace Goldbach

/--
If Goldbach is verified up to `AMSBound` and holds above `N0`, and if `N0 ≤ AMSBound`,
then Goldbach holds everywhere.
-/
theorem goldbachStrong_from_two_ranges
    {N0 AMSBound : ℕ}
    (hcover : N0 ≤ AMSBound)
    (hsmall : VerifiedUpTo AMSBound)
    (hlarge : HoldsAbove N0) :
    GoldbachStrong := by
  intro n hn4 hEven
  by_cases hA : n ≤ AMSBound
  · exact hsmall n hn4 hA hEven
  · have hN0 : N0 < n := lt_of_le_of_lt hcover (lt_of_not_ge hA)
    exact hlarge n hN0 hEven

end Goldbach
