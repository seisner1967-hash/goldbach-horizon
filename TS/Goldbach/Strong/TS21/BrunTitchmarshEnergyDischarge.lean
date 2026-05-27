import Mathlib.Tactic
import TS.Goldbach.Strong.TS21.ShortIntervalBudget

namespace TS21
namespace Goldbach

/--
Prime count in the TS15 short window starting at `n`.

This is the concrete local count whose square is summed by
`TS15.Goldbach.shortPrimeEnergy`.
-/
def shortPrimeLocalCount (x Q n : Nat) : Nat :=
  TS16.Goldbach.localCount
    (TS15.Goldbach.primeSetUpTo x)
    n
    (TS15.Goldbach.intervalScale x Q)

/--
The natural energy scale obtained from a uniform local-window bound
`shortPrimeLocalCount x Q n <= B`.
-/
noncomputable def localCountEnergyScale (x B : Nat) : Real :=
  ((x + 1) * B ^ 2 : Nat)

/--
A local Brun-Titchmarsh-style window budget.

The field `windowBudget x Q` is the explicit upper bound for every local prime
count in the short windows used by TS15. A future fully analytic
Brun-Titchmarsh formalization should instantiate this structure with a bound
of the shape `ceil (4 * h / log h)` (after all integer-rounding choices are
fixed).
-/
structure BrunTitchmarshLocalWindowBudget where
  windowBudget : Nat -> Nat -> Nat
  local_bound :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n ∈ Finset.range (x + 1) ->
      shortPrimeLocalCount x Q n <= windowBudget x Q

theorem shortEnergy_le_of_local_count_bound
    (x Q B : Nat)
    (hB :
      forall n : Nat,
        n ∈ Finset.range (x + 1) ->
        shortPrimeLocalCount x Q n <= B) :
    TS16.Goldbach.shortEnergy
        (TS15.Goldbach.primeSetUpTo x)
        x
        (TS15.Goldbach.intervalScale x Q) <=
      (x + 1) * B ^ 2 := by
  unfold TS16.Goldbach.shortEnergy
  calc
    (∑ n ∈ Finset.range (x + 1),
        TS16.Goldbach.localCount
          (TS15.Goldbach.primeSetUpTo x)
          n
          (TS15.Goldbach.intervalScale x Q) ^ 2)
        <= ∑ _n ∈ Finset.range (x + 1), B ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hc : shortPrimeLocalCount x Q n <= B := hB n hn
          unfold shortPrimeLocalCount at hc
          rw [pow_two, pow_two]
          exact Nat.mul_le_mul hc hc
    _ = (x + 1) * B ^ 2 := by
          simp [mul_comm]

/--
Uniform local-window control implies the corresponding short-prime energy
bound at the correct energy scale `(x+1) * B^2`.
-/
theorem shortPrimeEnergy_le_of_local_count_bound
    (x Q B : Nat)
    (hB :
      forall n : Nat,
        n ∈ Finset.range (x + 1) ->
        shortPrimeLocalCount x Q n <= B) :
    TS15.Goldbach.shortPrimeEnergy x Q <= localCountEnergyScale x B := by
  unfold TS15.Goldbach.shortPrimeEnergy localCountEnergyScale
  exact_mod_cast shortEnergy_le_of_local_count_bound x Q B hB

/--
The local Brun-Titchmarsh budget discharges the short-prime energy estimate at
its natural scale. This is the unconditional combinatorial transport step;
the remaining analytic work is only to instantiate `BrunTitchmarshLocalWindowBudget`.
-/
theorem shortPrimeEnergy_le_BrunTitchmarsh_energy_scale
    (BT : BrunTitchmarshLocalWindowBudget)
    (x Q : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hQ : Q = Nat.log 2 x * Nat.log 2 x) :
    TS15.Goldbach.shortPrimeEnergy x Q <=
      localCountEnergyScale x (BT.windowBudget x Q) := by
  exact shortPrimeEnergy_le_of_local_count_bound x Q (BT.windowBudget x Q)
    (fun n hn => BT.local_bound x Q n hx hQ hn)

end Goldbach
end TS21
