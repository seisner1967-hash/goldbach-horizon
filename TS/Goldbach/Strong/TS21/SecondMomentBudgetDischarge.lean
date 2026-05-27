import Mathlib.Tactic
import TS.Goldbach.Strong.TS18.DirichletCharacterBridge
import TS.Goldbach.Strong.TS21.ShortIntervalBudget

namespace TS21
namespace Goldbach

/--
Large-sieve infrastructure with a transported constant.

This is the TS21 replacement for the rigid TS18 requirement `C <= 1`: the
large-sieve side may produce any explicit `K`, and the threshold computation
later checks whether `K` is admissible.
-/
structure LargeSieveBudgetInfrastructure where
  K : Real
  K_pos : 0 < K
  selectedModulus : Nat -> Nat -> Nat
  sieve_bound :
    forall (D : TS18.Goldbach.DirichletCharacterBridge) (x Q : Nat),
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      D.characterSecondMoment x Q (selectedModulus x Q) +
          D.characterBridgeError x Q (selectedModulus x Q) <=
        K * shortIntervalBase x Q

/--
Relative budgeted second-moment instance from the TS18 character bridge plus a
large-sieve estimate carrying an explicit constant.
-/
noncomputable def secondMomentBudgetInstance
    (D : TS18.Goldbach.DirichletCharacterBridge)
    (L : LargeSieveBudgetInfrastructure) :
    ShortIntervalPrimeSecondMomentK where
  K := L.K
  K_pos := L.K_pos
  bound := by
    intro x Q hx hQ
    exact le_trans
      (D.energy_bound x Q (L.selectedModulus x Q) hx hQ)
      (L.sieve_bound D x Q hx hQ)

/--
Budgeted TS18 discharge: the downstream pair-count estimate carries exactly
the constant supplied by the large-sieve infrastructure.
-/
theorem Problem_E1K_from_budgeted_TS18
    (D : TS18.Goldbach.DirichletCharacterBridge)
    (L : LargeSieveBudgetInfrastructure) :
    Problem_E1K L.K :=
  Problem_E1K_from_short_interval_second_momentK
    (secondMomentBudgetInstance D L)

/--
If the transported large-sieve constant is below an allowed threshold, the
pair-count estimate is promoted to that threshold.
-/
theorem Problem_E1K_allowed_from_budgeted_TS18
    (D : TS18.Goldbach.DirichletCharacterBridge)
    (L : LargeSieveBudgetInfrastructure)
    {KAllowed : Real}
    (hK : L.K <= KAllowed) :
    Problem_E1K KAllowed :=
  Problem_E1K_mono hK (Problem_E1K_from_budgeted_TS18 D L)

end Goldbach
end TS21
