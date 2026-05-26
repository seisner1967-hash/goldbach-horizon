import TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals
import TS.Goldbach.Strong.TS18.DirichletCharacterBridge
import TS.Goldbach.Strong.TS18.LargeSieveInfrastructure

namespace TS18
namespace Goldbach

/--
Relative TS18 instance of the TS15 short-interval second moment.

It combines the Dirichlet-character bridge with the large-sieve infrastructure.
-/
noncomputable def secondMomentInstance
    (D : DirichletCharacterBridge)
    (L : LargeSieveInfrastructure) :
    TS15.Goldbach.ShortIntervalPrimeSecondMoment where
  C := L.C
  C_pos := L.C_pos
  bound := by
    intro x Q hx hQ
    exact le_trans
      (D.energy_bound x Q (L.selectedModulus x Q) hx hQ)
      (L.sieve_bound D x Q hx hQ)

/-- The TS18 relative instance has the constant bound required by TS15. -/
theorem secondMomentInstance_C_le_one
    (D : DirichletCharacterBridge)
    (L : LargeSieveInfrastructure) :
    (secondMomentInstance D L).C <= 1 := by
  exact L.C_le_one

/--
Relative TS18 discharge of `Problem_E1`.

This theorem records the exact downstream use of the second moment once the two
analytic infrastructures are supplied.
-/
theorem Problem_E1_from_TS18
    (D : DirichletCharacterBridge)
    (L : LargeSieveInfrastructure) :
    TS15.Goldbach.Problem_E1 :=
  TS15.Goldbach.Problem_E1_from_short_interval_second_moment
    (secondMomentInstance D L)
    (secondMomentInstance_C_le_one D L)

end Goldbach
end TS18
