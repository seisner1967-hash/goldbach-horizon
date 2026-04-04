/-
  Goldbach/BreakpointGrid.lean
  Breakpoint grid for the A2 certificate: defines the cell structure
  using the 1229 breakpoint enclosures.

  0 sorry.
-/
import Goldbach.A2CertificateData
import Goldbach.Thresholds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach

open Real

/-! ## Grid cell definition

Each breakpoint enclosure (p, lo, hi) defines an interval
  [lo/10^9, hi/10^9] containing log(p).
For our enclosures, hi = lo + 1 always.
-/

/-- A grid cell is the rational interval [lo, hi]. -/
structure GridCell where
  lo : ℝ
  hi : ℝ
  hlt : lo < hi

/-- Membership in a grid cell: q ∈ [lo, hi]. -/
def GridCell.mem (c : GridCell) (q : ℝ) : Prop :=
  c.lo ≤ q ∧ q ≤ c.hi

/-- The index type for breakpoint cells. -/
abbrev BreakpointIndex := Fin breakpointEnclosures.length

/-- All our enclosures have hi_num = lo_num + 1. -/
theorem enclosure_hi_eq_lo_succ :
    ∀ be ∈ breakpointEnclosures, be.hi_num = be.lo_num + 1 := by
  native_decide

/-- Get the i-th grid cell. -/
noncomputable def gridCell (i : BreakpointIndex) : GridCell where
  lo := ((breakpointEnclosures.get i).lo_num : ℝ) / 10^9
  hi := ((breakpointEnclosures.get i).hi_num : ℝ) / 10^9
  hlt := by
    apply div_lt_div_of_pos_right _ (by positivity : (0:ℝ) < 10^9)
    have hmem : breakpointEnclosures.get i ∈ breakpointEnclosures :=
      List.get_mem _ _
    have h := enclosure_hi_eq_lo_succ _ hmem
    have : (breakpointEnclosures.get i).lo_num < (breakpointEnclosures.get i).hi_num := by omega
    exact_mod_cast this

end Goldbach
