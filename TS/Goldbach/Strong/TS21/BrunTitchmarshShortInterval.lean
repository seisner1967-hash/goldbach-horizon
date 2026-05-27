import Mathlib.Tactic
import TS.Goldbach.Strong.TS21.ShortIntervalBudget

namespace TS21
namespace Goldbach

/--
Explicit TS21 threshold budget constant.

Important scale note: this constant is a downstream threshold target, not the
raw consequence of a pointwise Brun-Titchmarsh bound on every short window.
Pointwise local-window control is transported in
`BrunTitchmarshEnergyDischarge.lean` at the natural scale `(x+1) * B^2`.
-/
noncomputable def BTShortIntervalConstant : Real :=
  20

theorem BTShortIntervalConstant_pos :
    0 < BTShortIntervalConstant := by
  norm_num [BTShortIntervalConstant]

/--
Threshold-form short-interval consequence used by the original TS21 budget.

This is intentionally stronger than what follows from a pointwise
Brun-Titchmarsh local-window estimate alone. It should only be instantiated
after an additional averaging/correlation argument or a threshold computation
has bridged the natural energy scale to `20 * x^2 / Q^2`.
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
