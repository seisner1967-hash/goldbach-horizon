import Mathlib.Tactic
import TS.Goldbach.Strong.TS151.DependentSelbergScaleSplitInterface

namespace TS152
namespace Goldbach

/-!
# TS152 - Finite Head Prime Interval Budget Reduction

TS151 separates the natural-interval theorem into a finite head
`n <= level x Q` and a late-window branch.  This sprint treats the finite
combinatorics of the head.

It proves the universal cardinality bound

`primeIntervalCard n h <= h + 1`

and reduces every head interval to one cumulative interval starting at zero:

`primeIntervalCard n h <= primeIntervalCard 0 (level x Q + h)`.

Two sufficient interfaces then populate the exact TS151 finite-head package:

* a coarse comparison `h + 1 <= brunTitchmarshCeilBudget`;
* a sharper cumulative prime-count comparison.

Neither comparison is asserted unconditionally.  In particular, the first
one is deliberately kept as a contract because the TS22 budget can be smaller
than the total number of integers in the interval.
-/

/-- Any closed natural interval `[n,n+h]` contains at most `h+1` primes. -/
theorem primeIntervalCard_le_intervalLength_add_one
    (n h : Nat) :
    TS22.Goldbach.primeIntervalCard n h <= h + 1 := by
  unfold TS22.Goldbach.primeIntervalCard
  calc
    ((Finset.Icc n (n + h)).filter Nat.Prime).card <=
        (Finset.Icc n (n + h)).card :=
      Finset.card_filter_le _ _
    _ = h + 1 := by
      rw [Nat.card_Icc]
      omega

/--
Every head interval lies inside the cumulative interval beginning at zero and
ending at `level + h`.
-/
theorem primeIntervalCard_le_cumulativeHead
    (n h level : Nat)
    (hn : n <= level) :
    TS22.Goldbach.primeIntervalCard n h <=
      TS22.Goldbach.primeIntervalCard 0 (level + h) := by
  unfold TS22.Goldbach.primeIntervalCard
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk
  have hk_interval := hk.1
  have hk_prime := hk.2
  have hk_bounds : n <= k /\ k <= n + h := Finset.mem_Icc.mp hk_interval
  rw [Finset.mem_filter]
  exact And.intro
    (Finset.mem_Icc.mpr
      (And.intro (Nat.zero_le k) (by omega)))
    hk_prime

/--
Coarse sufficient condition for the TS151 finite head: the complete interval
cardinality already fits under the TS22 budget.
-/
def TrivialFiniteHeadBudgetCondition : Prop :=
  forall x Q : Nat,
    TS15.Goldbach.LargeX x ->
    Q = Nat.log 2 x * Nat.log 2 x ->
      TS15.Goldbach.intervalScale x Q + 1 <=
        TS22.Goldbach.brunTitchmarshCeilBudget x Q

/-- The coarse cardinality condition supplies every dependent finite head. -/
noncomputable def finiteHeadPrimeIntervalBudget_of_trivialCardinality
    (level : TS151.Goldbach.SelbergLevelSelection)
    (H : TrivialFiniteHeadBudgetCondition) :
    TS151.Goldbach.FiniteHeadPrimeIntervalBudget level where
  head_bound := by
    intro x Q n hx hQ _hn _hhead
    exact le_trans
      (primeIntervalCard_le_intervalLength_add_one
        n (TS15.Goldbach.intervalScale x Q))
      (H x Q hx hQ)
  finite_head_bound_obligation := True.intro

/--
Sharper sufficient condition: one cumulative prime count controls the complete
head for each pair `(x,Q)`.
-/
structure CumulativeFiniteHeadPrimeBudget
    (level : TS151.Goldbach.SelbergLevelSelection) where
  cumulative_bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
        TS22.Goldbach.primeIntervalCard
            0
            (level x Q + TS15.Goldbach.intervalScale x Q) <=
          TS22.Goldbach.brunTitchmarshCeilBudget x Q

  cumulative_prime_count_obligation :
    True

/-- A cumulative head estimate supplies the exact TS151 finite-head input. -/
noncomputable def finiteHeadPrimeIntervalBudget_of_cumulative
    (level : TS151.Goldbach.SelbergLevelSelection)
    (H : CumulativeFiniteHeadPrimeBudget level) :
    TS151.Goldbach.FiniteHeadPrimeIntervalBudget level where
  head_bound := by
    intro x Q n hx hQ _hn hhead
    exact le_trans
      (primeIntervalCard_le_cumulativeHead
        n
        (TS15.Goldbach.intervalScale x Q)
        (level x Q)
        hhead)
      (H.cumulative_bound x Q hx hQ)
  finite_head_bound_obligation := H.cumulative_prime_count_obligation

/--
The crude cardinality of the cumulative interval is also explicit.  This is a
diagnostic envelope, not a claim that the resulting comparison is true.
-/
theorem cumulativeHeadPrimeIntervalCard_le_cardinality
    (level : TS151.Goldbach.SelbergLevelSelection)
    (x Q : Nat) :
    TS22.Goldbach.primeIntervalCard
        0
        (level x Q + TS15.Goldbach.intervalScale x Q) <=
      level x Q + TS15.Goldbach.intervalScale x Q + 1 := by
  exact primeIntervalCard_le_intervalLength_add_one
    0
    (level x Q + TS15.Goldbach.intervalScale x Q)

/-- TS152 ledger recording both finite-head reduction routes. -/
structure FiniteHeadPrimeIntervalBudgetReductionLedger
    (level : TS151.Goldbach.SelbergLevelSelection) where
  interval_cardinality_bound :
    forall n h : Nat,
      TS22.Goldbach.primeIntervalCard n h <= h + 1

  cumulative_head_bound :
    forall x Q n h : Nat,
      n <= level x Q ->
        TS22.Goldbach.primeIntervalCard n h <=
          TS22.Goldbach.primeIntervalCard 0 (level x Q + h)

  cumulativePrimeBudget :
    CumulativeFiniteHeadPrimeBudget level

  finiteHead :
    TS151.Goldbach.FiniteHeadPrimeIntervalBudget level

  finite_head_eq :
    finiteHead =
      finiteHeadPrimeIntervalBudget_of_cumulative level cumulativePrimeBudget

  cumulative_prime_count_obligation :
    True

/-- Build the TS152 ledger from the remaining cumulative prime-count input. -/
noncomputable def finiteHeadPrimeIntervalBudgetReductionLedger
    (level : TS151.Goldbach.SelbergLevelSelection)
    (H : CumulativeFiniteHeadPrimeBudget level) :
    FiniteHeadPrimeIntervalBudgetReductionLedger level where
  interval_cardinality_bound := primeIntervalCard_le_intervalLength_add_one
  cumulative_head_bound := by
    intro x Q n h hn
    exact primeIntervalCard_le_cumulativeHead n h (level x Q) hn
  cumulativePrimeBudget := H
  finiteHead := finiteHeadPrimeIntervalBudget_of_cumulative level H
  finite_head_eq := rfl
  cumulative_prime_count_obligation := H.cumulative_prime_count_obligation

/-- Target for the corrected finite-head reduction. -/
def FiniteHeadPrimeIntervalBudgetReductionTarget : Prop :=
  forall level : TS151.Goldbach.SelbergLevelSelection,
    CumulativeFiniteHeadPrimeBudget level ->
      Nonempty (FiniteHeadPrimeIntervalBudgetReductionLedger level)

/-- The TS152 finite-head reduction target is populated. -/
theorem finiteHeadPrimeIntervalBudgetReductionTarget :
    FiniteHeadPrimeIntervalBudgetReductionTarget := by
  intro level H
  exact Nonempty.intro
    (finiteHeadPrimeIntervalBudgetReductionLedger level H)

end Goldbach
end TS152
