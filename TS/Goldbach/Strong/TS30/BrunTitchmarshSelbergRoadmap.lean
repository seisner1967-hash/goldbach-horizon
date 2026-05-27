import Mathlib.Tactic
import TS.Goldbach.Strong.TS22.BrunTitchmarshIntervalBridge

namespace TS30
namespace Goldbach

/--
A Selberg-sieve interval majorant for the TS22 Brun-Titchmarsh obligation.

The field `majorant x Q n` is the explicit integer upper bound produced by a
future Selberg-sieve theorem for the prime count in the TS22 local interval.
-/
structure SelbergIntervalMajorant where
  majorant : Nat -> Nat -> Nat -> Nat

/--
Sieve-theoretic part of Brun-Titchmarsh.

This is the future Mathlib-facing theorem: Selberg weights, local remainder
control, and the prime-detection argument should prove that the interval prime
count is bounded by the chosen Selberg majorant.
-/
structure SelbergSieveIntervalBound
    (M : SelbergIntervalMajorant) where
  sieve_bound :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      TS22.Goldbach.primeIntervalCard n
          (TS15.Goldbach.intervalScale x Q) <=
        M.majorant x Q n

/--
Arithmetic part of Brun-Titchmarsh.

Once the Selberg majorant is explicit, this field records the elementary
comparison with the TS22 ceiling budget
`brunTitchmarshCeilBudget x Q`.
-/
structure SelbergMajorantBudgetComparison
    (M : SelbergIntervalMajorant) where
  majorant_le_budget :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      M.majorant x Q n <=
        TS22.Goldbach.brunTitchmarshCeilBudget x Q

/--
Complete local Selberg infrastructure sufficient for the TS22 natural-interval
Brun-Titchmarsh obligation.

This is intentionally a parameter package that future analytic work can
instantiate, not a global declaration of the desired theorem.
-/
structure SelbergBrunTitchmarshInfrastructure where
  majorant : SelbergIntervalMajorant
  sieve : SelbergSieveIntervalBound majorant
  budget : SelbergMajorantBudgetComparison majorant

/--
Selberg infrastructure discharges the TS22 natural-interval Brun-Titchmarsh
input.
-/
noncomputable def brunTitchmarshNatIntervalBound_from_selberg
    (S : SelbergBrunTitchmarshInfrastructure) :
    TS22.Goldbach.BrunTitchmarshNatIntervalBound where
  interval_bound := by
    intro x Q n hx hQ hn
    have hnlt : n < x + 1 := Finset.mem_range.mp hn
    exact le_trans
      (S.sieve.sieve_bound x Q n hx hQ hnlt)
      (S.budget.majorant_le_budget x Q n hx hQ hnlt)

/--
The Selberg roadmap therefore feeds the existing TS22 scaled E1 theorem.
-/
theorem Problem_E1Scale_from_selberg_roadmap
    (S : SelbergBrunTitchmarshInfrastructure) :
    TS22.Goldbach.Problem_E1Scale
      (TS22.Goldbach.localWindowBudgetScale
        (TS22.Goldbach.localWindowBudgetOfNatIntervalBound
          (brunTitchmarshNatIntervalBound_from_selberg S)))
      1 :=
  TS22.Goldbach.Problem_E1Scale_from_natIntervalBound
    (brunTitchmarshNatIntervalBound_from_selberg S)

/--
The Selberg roadmap also feeds the padded closed-form scale once TS24 is
imported downstream.

This theorem keeps TS30 independent of TS24 and records the exact reusable
object for downstream modules.
-/
theorem natIntervalBound_from_selberg_roadmap
    (S : SelbergBrunTitchmarshInfrastructure) :
    TS22.Goldbach.BrunTitchmarshNatIntervalBound :=
  brunTitchmarshNatIntervalBound_from_selberg S

end Goldbach
end TS30
