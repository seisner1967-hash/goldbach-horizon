import Mathlib.Tactic
import TS.Goldbach.Strong.TS21.ShortIntervalBudget

namespace TS21
namespace Goldbach

/--
Explicit TS21 Brun-Titchmarsh budget constant.

The value `20` is deliberately conservative: it is large enough to absorb the
short-interval counting constants planned for the Brun-Titchmarsh discharge,
while remaining a concrete threshold input for the later numerical budget.
-/
noncomputable def BTShortIntervalConstant : Real :=
  20

theorem BTShortIntervalConstant_pos :
    0 < BTShortIntervalConstant := by
  norm_num [BTShortIntervalConstant]

/--
Local Brun-Titchmarsh short-interval consequence used by TS21.

This is the analytic obligation for the sprint: prove that the concrete
Brun-Titchmarsh interval estimate implies the short-prime energy bound with
constant `20`.
-/
structure BrunTitchmarshShortInterval where
  energy_bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      TS15.Goldbach.shortPrimeEnergy x Q <=
        BTShortIntervalConstant * shortIntervalBase x Q

/--
The Brun-Titchmarsh short-interval consequence instantiates the budgeted
second-moment interface with the explicit constant `20`.
-/
noncomputable def secondMomentBT
    (BT : BrunTitchmarshShortInterval) :
    ShortIntervalPrimeSecondMomentK where
  K := BTShortIntervalConstant
  K_pos := BTShortIntervalConstant_pos
  bound := by
    intro x Q hx hQ
    exact BT.energy_bound x Q hx hQ

theorem secondMomentBT_constant
    (BT : BrunTitchmarshShortInterval) :
    (secondMomentBT BT).K = 20 := by
  rfl

/--
The TS21 Brun-Titchmarsh obligation gives the budgeted pair-count estimate with
constant `20`.
-/
theorem Problem_E1K_from_BrunTitchmarsh
    (BT : BrunTitchmarshShortInterval) :
    Problem_E1K BTShortIntervalConstant :=
  Problem_E1K_from_short_interval_second_momentK (secondMomentBT BT)

end Goldbach
end TS21
