import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import TS.Goldbach.Strong.TS21.BrunTitchmarshEnergyDischarge
import TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge

namespace TS22
namespace Goldbach

/--
Number of primes in the closed natural interval `[n, n+h]`.

This is a deliberately elementary finset count. It avoids real endpoints and
rounding choices while retaining the exact interval shape used by the TS15
local windows.
-/
def primeIntervalCard (n h : Nat) : Nat :=
  ((Finset.Icc n (n + h)).filter Nat.Prime).card

/--
Explicit ceiling budget suggested by a Brun-Titchmarsh estimate.

The denominator uses `log (Q+1)` to keep the expression total at the Lean level.
Sharper variants can replace this definition without changing the bridge
theorems below.
-/
noncomputable def brunTitchmarshCeilBudget (x Q : Nat) : Nat :=
  Nat.ceil
    (((4 : Real) * (TS15.Goldbach.intervalScale x Q : Real)) /
      Real.log ((Q : Real) + 1))

/--
The TS15 local count is bounded by the count of all primes in the corresponding
closed natural interval. The former also imposes `p <= x`, so it is a subcount
of the latter.
-/
theorem shortPrimeLocalCount_le_primeIntervalCard
    (x Q n : Nat) :
    TS21.Goldbach.shortPrimeLocalCount x Q n <=
      primeIntervalCard n (TS15.Goldbach.intervalScale x Q) := by
  unfold TS21.Goldbach.shortPrimeLocalCount
  unfold TS16.Goldbach.localCount
  unfold TS16.Goldbach.localWindow
  unfold TS15.Goldbach.primeSetUpTo
  unfold primeIntervalCard
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk
  rcases hk with ⟨hkPrimeSet, hkWindow⟩
  rw [Finset.mem_filter] at hkPrimeSet
  rcases hkPrimeSet with ⟨_hkRange, hkPrime⟩
  rcases hkWindow with ⟨hnk, hkh⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨hnk, hkh⟩, hkPrime⟩

/--
Natural-interval Brun-Titchmarsh input.

A future Selberg/Brun-Titchmarsh formalization should prove this structure, or
a sharper variant, from its explicit interval theorem.
-/
structure BrunTitchmarshNatIntervalBound where
  interval_bound :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n ∈ Finset.range (x + 1) ->
      primeIntervalCard n (TS15.Goldbach.intervalScale x Q) <=
        brunTitchmarshCeilBudget x Q

/--
An interval-count Brun-Titchmarsh theorem instantiates the TS21 local-window
budget.
-/
noncomputable def localWindowBudgetOfNatIntervalBound
    (BT : BrunTitchmarshNatIntervalBound) :
    TS21.Goldbach.BrunTitchmarshLocalWindowBudget where
  windowBudget := brunTitchmarshCeilBudget
  local_bound := by
    intro x Q n hx hQ hn
    exact le_trans
      (shortPrimeLocalCount_le_primeIntervalCard x Q n)
      (BT.interval_bound x Q n hx hQ hn)

/--
The interval-count Brun-Titchmarsh input therefore yields the scaled pair-count
target at the exact ceiling-budget scale, with constant `1`.
-/
theorem Problem_E1Scale_from_natIntervalBound
    (BT : BrunTitchmarshNatIntervalBound) :
    Problem_E1Scale
      (localWindowBudgetScale (localWindowBudgetOfNatIntervalBound BT))
      1 :=
  Problem_E1Scale_from_localWindowBudget
    (localWindowBudgetOfNatIntervalBound BT)

end Goldbach
end TS22
