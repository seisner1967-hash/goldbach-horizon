import Mathlib.Tactic
import TS.Goldbach.Strong.TS159.SelbergDenominatorRefactorInterface

namespace TS160
namespace Goldbach

/-!
# TS160 - Selberg Phi Denominator Candidate

TS159 isolates the need for a replacement denominator that escapes the
Jordan-two cap proved in TS154.  This sprint introduces the first arithmetic
candidate:

`D_phi(level) = sum_{1 <= d <= level} mu(d)^2 / phi(d)`.

The goal is deliberately modest.  TS160 does not prove a Brun-Titchmarsh
comparison and does not refactor TS122.  It only proves that the phi candidate
is positive, crosses the old `2` barrier already at level `3`, and realizes
the TS159 growing-denominator interface for a prototype lower-bound curve.
-/

/-- A single summand of the phi-denominator candidate. -/
def selbergPhiDenominatorSummand (d : Nat) : Rat :=
  TS122.Goldbach.selbergMobiusRatCoefficient d ^ (2 : Nat) /
    (Nat.totient d : Rat)

/-- Prototype replacement for the TS122 Jordan-two denominator. -/
def selbergPhiDenominator (level : Nat) : Rat :=
  Finset.sum (Finset.Icc 1 level) selbergPhiDenominatorSummand

/--
Prototype growth curve: ask only for `1` at levels below `3`, and for `2`
from level `3` onward.  Later sprints can replace this by a logarithmic or
scale-dependent lower bound.
-/
def selbergPhiRequiredGrowth (level : Nat) : Rat :=
  if 3 <= level then 2 else 1

theorem selbergPhiDenominatorSummand_zero :
    selbergPhiDenominatorSummand 0 = 0 := by
  native_decide

theorem selbergPhiDenominatorSummand_nonneg
    {d : Nat}
    (hd : 0 < d) :
    0 <= selbergPhiDenominatorSummand d := by
  unfold selbergPhiDenominatorSummand
  have htot_pos_nat : 0 < Nat.totient d :=
    (Nat.totient_pos).2 hd
  have htot_nonneg : 0 <= (Nat.totient d : Rat) := by
    exact_mod_cast (Nat.zero_le (Nat.totient d))
  exact div_nonneg
    (sq_nonneg (TS122.Goldbach.selbergMobiusRatCoefficient d))
    htot_nonneg

theorem selbergPhiDenominator_mono
    {a b : Nat}
    (hab : a <= b) :
    selbergPhiDenominator a <= selbergPhiDenominator b := by
  unfold selbergPhiDenominator
  have hsubset : Finset.Icc 1 a <= Finset.Icc 1 b := by
    intro d hd
    have hmem := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr
      (And.intro hmem.1 (le_trans hmem.2 hab))
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (by
      intro d _ hd_not
      if hdpos : 0 < d then
        exact selbergPhiDenominatorSummand_nonneg hdpos
      else
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hdpos
        subst d
        rw [selbergPhiDenominatorSummand_zero])

theorem selbergPhiDenominator_one :
    selbergPhiDenominator 1 = 1 := by
  native_decide

theorem selbergPhiDenominator_two :
    selbergPhiDenominator 2 = 2 := by
  native_decide

theorem selbergPhiDenominator_three :
    selbergPhiDenominator 3 = (5 : Rat) / 2 := by
  native_decide

/-- The phi candidate is positive at every positive level. -/
theorem selbergPhiDenominator_pos
    (level : Nat)
    (hlevel : 0 < level) :
    0 < selbergPhiDenominator level := by
  have hmono : selbergPhiDenominator 1 <= selbergPhiDenominator level :=
    selbergPhiDenominator_mono hlevel
  have hone : (0 : Rat) < selbergPhiDenominator 1 := by
    rw [selbergPhiDenominator_one]
    norm_num
  exact lt_of_lt_of_le hone hmono

/-- The candidate escapes the TS154 `D < 2` cap already at level `3`. -/
theorem selbergPhiDenominator_three_gt_two :
    (2 : Rat) < selbergPhiDenominator 3 := by
  rw [selbergPhiDenominator_three]
  norm_num

/-- Explicit existential form of the barrier escape. -/
theorem selbergPhiDenominator_escapes_two_cap :
    exists level : Nat,
      0 < level /\ (2 : Rat) < selbergPhiDenominator level := by
  exact Exists.intro 3
    (And.intro (by norm_num) selbergPhiDenominator_three_gt_two)

theorem selbergPhiDenominator_ge_one_of_pos
    (level : Nat)
    (hlevel : 0 < level) :
    (1 : Rat) <= selbergPhiDenominator level := by
  have hmono : selbergPhiDenominator 1 <= selbergPhiDenominator level :=
    selbergPhiDenominator_mono hlevel
  simpa [selbergPhiDenominator_one] using hmono

theorem selbergPhiDenominator_ge_two_of_three_le
    (level : Nat)
    (hlevel : 3 <= level) :
    (2 : Rat) <= selbergPhiDenominator level := by
  have hmono : selbergPhiDenominator 3 <= selbergPhiDenominator level :=
    selbergPhiDenominator_mono hlevel
  have htwo : (2 : Rat) <= selbergPhiDenominator 3 :=
    le_of_lt selbergPhiDenominator_three_gt_two
  exact le_trans htwo hmono

theorem selbergPhiRequiredGrowth_lower_bound
    (level : Nat)
    (hreg : TS159.Goldbach.SelbergDenominatorGrowthRegime level) :
    selbergPhiRequiredGrowth level <= selbergPhiDenominator level := by
  unfold selbergPhiRequiredGrowth
  if hthree : 3 <= level then
    simp [hthree, selbergPhiDenominator_ge_two_of_three_le level hthree]
  else
    simp [hthree, selbergPhiDenominator_ge_one_of_pos level hreg]

/-- The phi prototype realizes the TS159 growing-denominator data interface. -/
def selbergPhiGrowingDenominatorData :
    TS159.Goldbach.SelbergGrowingDenominatorData where
  denominator := selbergPhiDenominator
  requiredGrowth := selbergPhiRequiredGrowth
  positive := by
    intro level hlevel
    exact selbergPhiDenominator_pos level hlevel
  lower_bound := by
    intro level hreg
    exact selbergPhiRequiredGrowth_lower_bound level hreg

/-- The phi candidate satisfies the TS159 data-satisfaction predicate. -/
theorem selbergPhiDenominator_satisfies_TS159_interface :
    TS159.Goldbach.SelbergGrowingDenominatorDataSatisfiedBy
      selbergPhiDenominator
      selbergPhiRequiredGrowth := by
  exact Nonempty.intro
    (Subtype.mk selbergPhiGrowingDenominatorData
      (And.intro rfl rfl))

/--
Ledger for the first post-obstruction arithmetic candidate.  It records only
prototype viability, not the eventual TS22 budget comparison.
-/
structure SelbergPhiDenominatorCandidateLedger where
  data :
    TS159.Goldbach.SelbergGrowingDenominatorData

  data_eq :
    data = selbergPhiGrowingDenominatorData

  positive :
    forall level : Nat,
      0 < level -> 0 < selbergPhiDenominator level

  crosses_two_at_three :
    (2 : Rat) < selbergPhiDenominator 3

  satisfies_TS159_interface :
    TS159.Goldbach.SelbergGrowingDenominatorDataSatisfiedBy
      selbergPhiDenominator
      selbergPhiRequiredGrowth

  no_BT_comparison_claim :
    True

/-- Concrete TS160 candidate ledger. -/
def selbergPhiDenominatorCandidateLedger :
    SelbergPhiDenominatorCandidateLedger where
  data := selbergPhiGrowingDenominatorData
  data_eq := rfl
  positive := selbergPhiDenominator_pos
  crosses_two_at_three := selbergPhiDenominator_three_gt_two
  satisfies_TS159_interface :=
    selbergPhiDenominator_satisfies_TS159_interface
  no_BT_comparison_claim := True.intro

/-- Target proposition for TS160. -/
def SelbergPhiDenominatorCandidateTarget : Prop :=
  Nonempty SelbergPhiDenominatorCandidateLedger

/-- The TS160 phi-denominator candidate target is populated. -/
theorem selbergPhiDenominatorCandidateTarget :
    SelbergPhiDenominatorCandidateTarget :=
  Nonempty.intro selbergPhiDenominatorCandidateLedger

end Goldbach
end TS160
