import Mathlib.Tactic
import TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals

namespace TS21
namespace Goldbach

/-- Normalizing scale for the short-interval second moment. -/
noncomputable def shortIntervalBase (x Q : Nat) : Real :=
  (x : Real)^2 / ((Q : Real)^2)

theorem shortIntervalBase_nonneg (x Q : Nat) :
    0 <= shortIntervalBase x Q := by
  unfold shortIntervalBase
  exact div_nonneg (sq_nonneg (x : Real)) (sq_nonneg (Q : Real))

/--
Budgeted version of the TS15 pair-count target.

`Problem_E1K K` records the same estimate as `Problem_E1`, but keeps the
constant `K` explicit instead of forcing it to be at most one immediately.
-/
def Problem_E1K (K : Real) : Prop :=
  forall x Q : Nat,
    TS15.Goldbach.LargeX x ->
    0 < Q ->
    Q = Nat.log 2 x * Nat.log 2 x ->
    TS15.Goldbach.primePairsAtScale x Q <= K * shortIntervalBase x Q

/--
Short-interval second moment with an explicit transported constant.
-/
structure ShortIntervalPrimeSecondMomentK where
  K : Real
  K_pos : 0 < K
  bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      TS15.Goldbach.shortPrimeEnergy x Q <= K * shortIntervalBase x Q

/-- Forget the budgeted wrapper and recover the original TS15 interface. -/
noncomputable def ShortIntervalPrimeSecondMomentK.toTS15
    (H : ShortIntervalPrimeSecondMomentK) :
    TS15.Goldbach.ShortIntervalPrimeSecondMoment where
  C := H.K
  C_pos := H.K_pos
  bound := by
    intro x Q hx hQ
    simpa [shortIntervalBase] using H.bound x Q hx hQ

/--
The combinatorial TS16 discharge plus a budgeted second-moment estimate gives a
budgeted pair-count estimate with the same constant.
-/
theorem Problem_E1K_from_short_interval_second_momentK
    (H : ShortIntervalPrimeSecondMomentK) :
    Problem_E1K H.K := by
  intro x Q hx hQpos hQ
  have hpair :
      TS15.Goldbach.primePairsAtScale x Q <=
        TS15.Goldbach.shortPrimeEnergy x Q :=
    TS15.Goldbach.pair_count_le_short_interval_energy x Q hx hQpos hQ
  have henergy :
      TS15.Goldbach.shortPrimeEnergy x Q <=
        H.K * shortIntervalBase x Q :=
    H.bound x Q hx hQ
  exact le_trans hpair henergy

/-- A budgeted `Problem_E1K` is monotone in its explicit constant. -/
theorem Problem_E1K_mono
    {K L : Real}
    (hKL : K <= L)
    (hK : Problem_E1K K) :
    Problem_E1K L := by
  intro x Q hx hQpos hQ
  have hbase : 0 <= shortIntervalBase x Q :=
    shortIntervalBase_nonneg x Q
  have hscale :
      K * shortIntervalBase x Q <= L * shortIntervalBase x Q := by
    exact mul_le_mul_of_nonneg_right hKL hbase
  exact le_trans (hK x Q hx hQpos hQ) hscale

/--
Compatibility with the original TS15 target: if the transported budget is at
most one, the old `Problem_E1` follows.
-/
theorem Problem_E1_from_problem_E1K_of_le_one
    {K : Real}
    (hK_le_one : K <= 1)
    (hK : Problem_E1K K) :
    TS15.Goldbach.Problem_E1 := by
  intro x Q hx hQpos hQ
  have hbase : 0 <= shortIntervalBase x Q :=
    shortIntervalBase_nonneg x Q
  have hcoef :
      K * shortIntervalBase x Q <= shortIntervalBase x Q := by
    exact mul_le_of_le_one_left hbase hK_le_one
  exact le_trans (hK x Q hx hQpos hQ) hcoef

end Goldbach
end TS21
