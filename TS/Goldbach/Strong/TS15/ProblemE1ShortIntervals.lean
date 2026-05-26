import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import TS.Goldbach.Strong.TS15.ShortIntervalSecondMoment

namespace TS15
namespace Goldbach

def Problem_E1 : Prop :=
  forall x Q : Nat,
    LargeX x ->
    0 < Q ->
    Q = Nat.log 2 x * Nat.log 2 x ->
    primePairsAtScale x Q <= ((x : Real)^2 / ((Q : Real)^2))

theorem pair_count_le_short_interval_energy :
  forall x Q : Nat,
    LargeX x ->
    0 < Q ->
    Q = Nat.log 2 x * Nat.log 2 x ->
    primePairsAtScale x Q <= shortPrimeEnergy x Q := by
  intro x Q hx hQpos hQ
  unfold primePairsAtScale shortPrimeEnergy
  exact Nat.cast_le.mpr
    (_root_.TS16.Goldbach.pair_count_le_energy
      (primeSetUpTo x) x (intervalScale x Q) (primeSetUpTo_le x))

theorem Problem_E1_from_short_interval_second_moment
    (H : ShortIntervalPrimeSecondMoment)
    (hC : H.C <= 1) :
    Problem_E1 := by
  intro x Q hx hQpos hQ

  have hpair :
      primePairsAtScale x Q <= shortPrimeEnergy x Q :=
    pair_count_le_short_interval_energy x Q hx hQpos hQ

  have henergy :
      shortPrimeEnergy x Q <=
        H.C * ((x : Real)^2 / ((Q : Real)^2)) :=
    H.bound x Q hx hQ

  have hbase_nonneg :
      0 <= ((x : Real)^2 / ((Q : Real)^2)) := by
    exact div_nonneg (sq_nonneg (x : Real)) (sq_nonneg (Q : Real))

  have hcoef :
      H.C * ((x : Real)^2 / ((Q : Real)^2))
        <= ((x : Real)^2 / ((Q : Real)^2)) := by
    exact mul_le_of_le_one_left hbase_nonneg hC

  exact le_trans hpair (le_trans henergy hcoef)

end Goldbach
end TS15
