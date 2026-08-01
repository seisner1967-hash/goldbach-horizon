import Mathlib.Tactic
import TS.Goldbach.Strong.TS330.ConditionalTraceBudgetAssembly

namespace TS331
namespace Goldbach

/-!
# TS331: necessary trace-budget feasibility

This module extracts data-independent necessary inequalities from the TS330
trace-budget template.  In particular, every inhabitable template forces the
declared finite-core majorant below `1 / 384`.  The executable checker below is
only a rejection filter: passing it does not construct a template, a zero
cover, a TS181 adapter, or a Goldbach result.
-/

/-! ## Necessary inequalities from the half-budget -/

/-- Every TS330 template allocates at most one half to its moment component. -/
theorem qMoment_le_half
    {H : Nat} {core : Rat}
    (T : TS330.Goldbach.RationalTraceBudgetTemplate H core) :
    T.qMoment <= 1 / 2 := by
  linarith [T.components_le_budget, T.traceBudget_le_half,
    T.truncationTailMajorant_nonnegative,
    T.exceptionalMajorant_nonnegative,
    T.leftMajorant_nonnegative]

/-- The nonnegative moment is therefore quadratically bounded by one quarter. -/
theorem qMoment_sq_le_one_div_four
    {H : Nat} {core : Rat}
    (T : TS330.Goldbach.RationalTraceBudgetTemplate H core) :
    (T.qMoment : Real) ^ 2 <= 1 / 4 := by
  have hNonnegative : (0 : Real) <= (T.qMoment : Real) := by
    exact_mod_cast T.qMoment_nonnegative
  have hHalf : (T.qMoment : Real) <= (1 : Real) / 2 := by
    have hHalfRat : T.qMoment <= (1 : Rat) / 2 := qMoment_le_half T
    have hCast := (Rat.cast_le (K := Real)).2 hHalfRat
    norm_num at hCast
    norm_num
    exact hCast
  nlinarith

/-- The pair contribution must fit below the quarter-budget minus the diagonal. -/
theorem weighted_core_tail_le_diagonal_margin
    {H : Nat} {core : Rat}
    (T : TS330.Goldbach.RationalTraceBudgetTemplate H core) :
    96 * (core + T.tailMajorant) <=
      1 / 4 - T.diagonalMajorant := by
  have hReal :
      (96 : Real) * ((core : Real) + (T.tailMajorant : Real)) <=
        (1 : Real) / 4 - (T.diagonalMajorant : Real) := by
    nlinarith [T.moment_allocation, qMoment_sq_le_one_div_four T]
  have hCast :
      ((96 * (core + T.tailMajorant) : Rat) : Real) <=
        (((1 : Rat) / 4 - T.diagonalMajorant : Rat) : Real) := by
    norm_num at hReal
    norm_num
    exact hReal
  exact (Rat.cast_le (K := Real)).mp hCast

/-- Even after forgetting the nonnegative diagonal, core plus tail is tiny. -/
theorem core_add_tail_le_one_div_384
    {H : Nat} {core : Rat}
    (T : TS330.Goldbach.RationalTraceBudgetTemplate H core) :
    core + T.tailMajorant <= 1 / 384 := by
  nlinarith [weighted_core_tail_le_diagonal_margin T,
    T.diagonalMajorant_nonnegative]

/-- In particular, the declared finite-core majorant cannot exceed `1 / 384`. -/
theorem core_le_one_div_384
    {H : Nat} {core : Rat}
    (T : TS330.Goldbach.RationalTraceBudgetTemplate H core) :
    core <= 1 / 384 := by
  linarith [core_add_tail_le_one_div_384 T,
    T.tailMajorant_nonnegative]

/-! ## Executable rejection filter -/

/-- Check the necessary finite-core threshold for a candidate payload. -/
def checkNecessaryCoreThreshold
    (data : TS324.Goldbach.ZeroCoverPayload) : Bool :=
  decide (TS324.Goldbach.computedCoreMajorant data <= (1 : Rat) / 384)

theorem checkNecessaryCoreThreshold_iff
    (data : TS324.Goldbach.ZeroCoverPayload) :
    checkNecessaryCoreThreshold data = true <->
      TS324.Goldbach.computedCoreMajorant data <= (1 : Rat) / 384 := by
  simp [checkNecessaryCoreThreshold]

end Goldbach
end TS331
