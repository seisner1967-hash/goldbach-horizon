import Mathlib.Tactic
import TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals

namespace TS22
namespace Goldbach

/--
A normalization scale for the short-interval energy and pair-count estimates.

TS15 used the rigid scale `x^2 / Q^2`. TS22 makes the scale explicit so that
different analytic inputs can carry their natural dimensions without changing
the combinatorial core.
-/
structure ShortIntervalScale where
  scale : Nat -> Nat -> Real
  scale_nonneg : forall x Q : Nat, 0 <= scale x Q

/-- The original TS15/TS21 normalization scale. -/
noncomputable def classicalScale : ShortIntervalScale where
  scale := fun x Q => (x : Real)^2 / ((Q : Real)^2)
  scale_nonneg := by
    intro x Q
    exact div_nonneg (sq_nonneg (x : Real)) (sq_nonneg (Q : Real))

/--
Pair-count target with an explicit scale.
-/
def Problem_E1Scale (S : ShortIntervalScale) (K : Real) : Prop :=
  forall x Q : Nat,
    TS15.Goldbach.LargeX x ->
    0 < Q ->
    Q = Nat.log 2 x * Nat.log 2 x ->
    TS15.Goldbach.primePairsAtScale x Q <= K * S.scale x Q

/--
Short-interval second moment with an explicit scale.
-/
structure ShortIntervalPrimeSecondMomentScale (S : ShortIntervalScale) where
  K : Real
  K_pos : 0 < K
  bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      TS15.Goldbach.shortPrimeEnergy x Q <= K * S.scale x Q

/--
The TS16 combinatorial discharge transports any scaled second-moment estimate
to the corresponding scaled pair-count estimate.
-/
theorem Problem_E1Scale_from_second_moment_scale
    {S : ShortIntervalScale}
    (H : ShortIntervalPrimeSecondMomentScale S) :
    Problem_E1Scale S H.K := by
  intro x Q hx hQpos hQ
  have hpair :
      TS15.Goldbach.primePairsAtScale x Q <=
        TS15.Goldbach.shortPrimeEnergy x Q :=
    TS15.Goldbach.pair_count_le_short_interval_energy x Q hx hQpos hQ
  have henergy :
      TS15.Goldbach.shortPrimeEnergy x Q <= H.K * S.scale x Q :=
    H.bound x Q hx hQ
  exact le_trans hpair henergy

/-- Monotonicity in the transported constant. -/
theorem Problem_E1Scale_mono_const
    {S : ShortIntervalScale}
    {K L : Real}
    (hKL : K <= L)
    (hK : Problem_E1Scale S K) :
    Problem_E1Scale S L := by
  intro x Q hx hQpos hQ
  have hscale_nonneg : 0 <= S.scale x Q := S.scale_nonneg x Q
  have hmul : K * S.scale x Q <= L * S.scale x Q := by
    exact mul_le_mul_of_nonneg_right hKL hscale_nonneg
  exact le_trans (hK x Q hx hQpos hQ) hmul

/-- Monotonicity in the normalization scale. -/
theorem Problem_E1Scale_mono_scale
    {S T : ShortIntervalScale}
    {K : Real}
    (hK_nonneg : 0 <= K)
    (hST : forall x Q : Nat, S.scale x Q <= T.scale x Q)
    (hS : Problem_E1Scale S K) :
    Problem_E1Scale T K := by
  intro x Q hx hQpos hQ
  have hmul : K * S.scale x Q <= K * T.scale x Q := by
    exact mul_le_mul_of_nonneg_left (hST x Q) hK_nonneg
  exact le_trans (hS x Q hx hQpos hQ) hmul

end Goldbach
end TS22
