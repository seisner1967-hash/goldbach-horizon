import Mathlib.Tactic
import TS.Goldbach.Strong.TS21.BrunTitchmarshEnergyDischarge
import TS.Goldbach.Strong.TS22.EnergyScale

namespace TS22
namespace Goldbach

/--
The scale naturally produced by a local Brun-Titchmarsh window budget.

If every short window has at most `B = BT.windowBudget x Q` primes, the raw
short-prime energy is bounded by `(x+1) * B^2`. This is the scale proved in
TS21.
-/
noncomputable def localWindowBudgetScale
    (BT : TS21.Goldbach.BrunTitchmarshLocalWindowBudget) :
    ShortIntervalScale where
  scale := fun x Q =>
    TS21.Goldbach.localCountEnergyScale x (BT.windowBudget x Q)
  scale_nonneg := by
    intro x Q
    unfold TS21.Goldbach.localCountEnergyScale
    change (0 : Real) <= (((x + 1) * (BT.windowBudget x Q) ^ 2 : Nat) : Real)
    exact_mod_cast Nat.zero_le ((x + 1) * (BT.windowBudget x Q) ^ 2)

/--
The local Brun-Titchmarsh window budget gives a scaled second-moment estimate
with constant `1` at its natural energy scale.
-/
noncomputable def secondMomentScaleFromLocalWindowBudget
    (BT : TS21.Goldbach.BrunTitchmarshLocalWindowBudget) :
    ShortIntervalPrimeSecondMomentScale (localWindowBudgetScale BT) where
  K := 1
  K_pos := by norm_num
  bound := by
    intro x Q hx hQ
    have h :=
      TS21.Goldbach.shortPrimeEnergy_le_BrunTitchmarsh_energy_scale
        BT x Q hx hQ
    simpa [localWindowBudgetScale] using h

/--
The local Brun-Titchmarsh window budget gives the corresponding pair-count
target with constant `1` at its natural energy scale.
-/
theorem Problem_E1Scale_from_localWindowBudget
    (BT : TS21.Goldbach.BrunTitchmarshLocalWindowBudget) :
    Problem_E1Scale (localWindowBudgetScale BT) 1 :=
  Problem_E1Scale_from_second_moment_scale
    (secondMomentScaleFromLocalWindowBudget BT)

/--
Bridge from the natural local-window scale to another chosen normalization.

This is the right place for future analytic or numeric work showing, for
example, that a closed-form Brun-Titchmarsh scale is large enough to dominate
the exact integer window budget scale.
-/
structure BrunTitchmarshScaleBridge
    (BT : TS21.Goldbach.BrunTitchmarshLocalWindowBudget)
    (S : ShortIntervalScale) where
  scale_bound :
    forall x Q : Nat,
      (localWindowBudgetScale BT).scale x Q <= S.scale x Q

/--
If a chosen normalization dominates the exact local-window budget scale, the
Brun-Titchmarsh local-window estimate transports to that normalization with
constant `1`.
-/
theorem Problem_E1Scale_from_localWindowBudget_bridge
    (BT : TS21.Goldbach.BrunTitchmarshLocalWindowBudget)
    (S : ShortIntervalScale)
    (B : BrunTitchmarshScaleBridge BT S) :
    Problem_E1Scale S 1 :=
  Problem_E1Scale_mono_scale
    (by norm_num : (0 : Real) <= 1)
    B.scale_bound
    (Problem_E1Scale_from_localWindowBudget BT)

end Goldbach
end TS22
