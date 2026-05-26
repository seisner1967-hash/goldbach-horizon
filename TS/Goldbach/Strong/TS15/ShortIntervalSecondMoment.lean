import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TS.Goldbach.Strong.TS16.CombinatorialDischarge

namespace TS15
namespace Goldbach

def primeSetUpTo (x : Nat) : Finset Nat :=
  (Finset.range (x + 1)).filter Nat.Prime

def intervalScale (x Q : Nat) : Nat :=
  x / Q

theorem primeSetUpTo_le (x : Nat) :
    forall k, k ∈ primeSetUpTo x -> k <= x := by
  intro k hk
  rw [primeSetUpTo] at hk
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)

noncomputable def primePairsAtScale (x Q : Nat) : Real :=
  (_root_.TS16.Goldbach.countPairs (primeSetUpTo x) (intervalScale x Q) : Real)

noncomputable def shortPrimeEnergy (x Q : Nat) : Real :=
  (_root_.TS16.Goldbach.shortEnergy (primeSetUpTo x) x (intervalScale x Q) : Real)

def LargeX (x : Nat) : Prop :=
  16 <= x

structure ShortIntervalPrimeSecondMoment where
  C : Real
  C_pos : 0 < C
  bound :
    forall x Q : Nat,
      LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      shortPrimeEnergy x Q <=
        C * ((x : Real)^2 / ((Q : Real)^2))

end Goldbach
end TS15
