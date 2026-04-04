/-
  Goldbach/Thresholds.lean
  Conservative integer thresholds, separated from the analytic core.
-/

import Goldbach.Framework

namespace Goldbach

/-- The conservative explicit threshold used for the Horizon collage. -/
def N0 : ℕ :=
  2700000000000000000

/-- The Oliveira e Silva--Herzog--Pardi verification bound. -/
def AMSBound : ℕ :=
  4000000000000000000

/-- The explicit overlap needed for the collage. -/
theorem N0_le_AMSBound : N0 ≤ AMSBound := by
  decide

end Goldbach
