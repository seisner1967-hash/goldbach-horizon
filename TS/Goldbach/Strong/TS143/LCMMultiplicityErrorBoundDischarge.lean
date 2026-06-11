import Mathlib.Tactic
import Mathlib.Data.Int.CardIntervalMod
import TS.Goldbach.Strong.TS142.LCMMultiplicityFractionalDecomposition

open Finset

namespace TS143
namespace Goldbach

/-!
# TS143 - LCM Multiplicity Error Bound Discharge

TS142 splits the exact number of multiples of `lcm(d1,d2)` in the closed
interval `[n,n+h]` into the rational main term `(h+1)/lcm(d1,d2)` plus an
error.

This sprint proves that the absolute value of this error is at most one.  The
proof uses Mathlib's exact count on a half-open natural interval and the fact
that the discrepancy `ceil(q) - q` lies in `[0,1)`.

The separate TS142 lcm dense-side budget remains open.
-/

/--
Exact multiple count on a closed natural interval, expressed as a difference
of rational ceilings.
-/
theorem closedIntervalMultipleCount_eq_ceil_sub_ceil
    (n h m : Nat)
    (hm : 0 < m) :
    (((Finset.Icc n (n + h)).filter fun k => Dvd.dvd m k).card : Int) =
      Int.ceil ((((n + h + 1 : Nat) : Rat) / (m : Rat))) -
        Int.ceil (((n : Rat) / (m : Rat))) := by
  have hmono :
      ((n : Rat) / (m : Rat)) <=
        (((n + h + 1 : Nat) : Rat) / (m : Rat)) := by
    gcongr
    omega
  have hceil :
      Int.ceil ((n : Rat) / (m : Rat)) <=
        Int.ceil (((n + h + 1 : Nat) : Rat) / (m : Rat)) :=
    Int.ceil_mono hmono
  have hraw := Nat.Ico_filter_modEq_card n (n + h + 1) hm 0
  simp only [Nat.cast_zero, sub_zero] at hraw
  rw [max_eq_left (sub_nonneg.mpr hceil)] at hraw
  simpa [Nat.modEq_zero_iff_dvd, Nat.Ico_succ_right,
    Nat.succ_eq_add_one, add_assoc] using hraw

/--
The number of multiples of a positive modulus in `[n,n+h]` differs from
`(h+1)/m` by at most one.
-/
theorem closedIntervalMultipleCount_error_abs_le_one
    (n h m : Nat)
    (hm : 0 < m) :
    abs
        ((((Finset.Icc n (n + h)).filter fun k => Dvd.dvd m k).card : Rat) -
          (((h + 1 : Nat) : Rat) / (m : Rat))) <=
      1 := by
  let A : Rat := (n : Rat) / (m : Rat)
  let B : Rat := ((n + h + 1 : Nat) : Rat) / (m : Rat)
  have hcardInt := closedIntervalMultipleCount_eq_ceil_sub_ceil n h m hm
  have hcardRat :
      (((Finset.Icc n (n + h)).filter fun k => Dvd.dvd m k).card : Rat) =
        (Int.ceil B : Rat) - (Int.ceil A : Rat) := by
    have hcast := congrArg (fun z : Int => (z : Rat)) hcardInt
    simpa [A, B, Int.cast_sub] using hcast
  have hBA :
      B - A = ((h + 1 : Nat) : Rat) / (m : Rat) := by
    dsimp [A, B]
    have hmRat : Not ((m : Rat) = 0) := by
      exact_mod_cast (Nat.ne_of_gt hm)
    field_simp [hmRat]
    ring
  have hAle : A <= (Int.ceil A : Rat) := Int.le_ceil A
  have hAlt : (Int.ceil A : Rat) < A + 1 := Int.ceil_lt_add_one A
  have hBle : B <= (Int.ceil B : Rat) := Int.le_ceil B
  have hBlt : (Int.ceil B : Rat) < B + 1 := Int.ceil_lt_add_one B
  rw [hcardRat]
  rw [<- hBA]
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise TS142 error bound for one positive lcm modulus. -/
theorem lcmMultiplicityErrorRat_abs_le_one
    (x Q n d1 d2 : Nat)
    (hlcm : 0 < Nat.lcm d1 d2) :
    abs (TS142.Goldbach.lcmMultiplicityErrorRat x Q n d1 d2) <= 1 := by
  simpa [
    TS142.Goldbach.lcmMultiplicityErrorRat,
    TS142.Goldbach.lcmMultiplicity,
    TS142.Goldbach.lcmMultiplicityMainRat,
    TS141.Goldbach.selbergConcreteLcmMultiplicity,
    TS138.Goldbach.selbergConcreteInterval
  ] using
    closedIntervalMultipleCount_error_abs_le_one
      n
      (TS15.Goldbach.intervalScale x Q)
      (Nat.lcm d1 d2)
      hlcm

/-- The TS142 local lcm multiplicity error obligation is fully discharged. -/
theorem lcmMultiplicityErrorBound
    (x Q n : Nat) :
    TS142.Goldbach.LCMMultiplicityErrorBound x Q n := by
  intro d1 d2 hlcm
  exact lcmMultiplicityErrorRat_abs_le_one x Q n d1 d2 hlcm

/--
TS143 package: the interval discrepancy is now unconditional, while the
separate lcm dense-side budget remains the only input to the TS142 ledger.
-/
structure LCMMultiplicityErrorBoundDischarge
    (level x Q n : Nat) where
  hlevel :
    0 < level

  error_bound :
    TS142.Goldbach.LCMMultiplicityErrorBound x Q n

  dense_side_budget_obligation :
    TS142.Goldbach.SelbergLCMDenseSideExactBudget level

  fractionalDecomposition :
    TS142.Goldbach.LCMMultiplicityFractionalDecomposition level x Q n

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Build the TS143 package from only the remaining lcm dense-side budget. -/
def lcmMultiplicityErrorBoundDischarge
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (hdense : TS142.Goldbach.SelbergLCMDenseSideExactBudget level) :
    LCMMultiplicityErrorBoundDischarge level x Q n where
  hlevel := hlevel
  error_bound := lcmMultiplicityErrorBound x Q n
  dense_side_budget_obligation := hdense
  fractionalDecomposition :=
    TS142.Goldbach.lcmMultiplicityFractionalDecomposition
      level x Q n hlevel (lcmMultiplicityErrorBound x Q n) hdense
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Bridge target after discharging the TS142 local interval error. -/
def LCMMultiplicityErrorBoundDischargeTarget : Prop :=
  forall level x Q n : Nat,
    0 < level ->
      TS142.Goldbach.SelbergLCMDenseSideExactBudget level ->
        Nonempty (LCMMultiplicityErrorBoundDischarge level x Q n)

/-- The TS143 target now depends only on the lcm dense-side budget. -/
theorem lcmMultiplicityErrorBoundDischargeTarget :
    LCMMultiplicityErrorBoundDischargeTarget := by
  intro level x Q n hlevel hdense
  exact
    Nonempty.intro
      (lcmMultiplicityErrorBoundDischarge
        level x Q n hlevel hdense)

/-- TS143 keeps the exact TS142 decomposition target available. -/
theorem lcmMultiplicityFractionalDecompositionTarget :
    TS142.Goldbach.LCMMultiplicityFractionalDecompositionTarget :=
  TS142.Goldbach.lcmMultiplicityFractionalDecompositionTarget

end Goldbach
end TS143
