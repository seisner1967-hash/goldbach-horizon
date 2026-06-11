import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS144.LCMDenseSideBudgetRefactor

namespace TS145
namespace Goldbach

/-!
# TS145 - Euler Totient Diagonalization and Jordan Domination

TS144 reduces the corrected lcm dense-side budget to two finite arithmetic
inputs.  This sprint discharges both:

* the absorbed gcd kernel diagonalizes with Euler's totient;
* Euler's totient is bounded by the Jordan-two coefficient on positive
  integers, hence on the TS122 support.

Consequently the TS144 lcm dense side and fractional main term have the
required unconditional `1 / D` upper bound for every positive level.
-/

theorem totient_prime_pow_le_jordanTwo
    {p k : Nat}
    (hp : p.Prime)
    (hk : 0 < k) :
    (Nat.totient (p ^ k) : Rat) <=
      TS119.Goldbach.selbergJordanTwoCoefficient (p ^ k) := by
  cases k with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hk)
  | succ j =>
      rw [Nat.totient_prime_pow_succ hp]
      rw [TS125.Goldbach.selbergJordanTwoCoefficient_prime_pow_succ hp]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le]
      have hp_rat : (1 : Rat) <= (p : Rat) := by
        exact_mod_cast hp.one_lt.le
      have hpow_one : (1 : Rat) <= (p : Rat) ^ j :=
        by exact_mod_cast Nat.one_le_pow j p hp.pos
      have hpow : (p : Rat) ^ j <= (p : Rat) ^ (2 * j) := by
        rw [show 2 * j = j + j by omega, pow_add]
        nlinarith
      have hp_sub : (p : Rat) - 1 <= (p : Rat) ^ 2 - 1 := by
        nlinarith
      have hleft_nonneg : 0 <= (p : Rat) ^ j :=
        le_trans zero_le_one hpow_one
      have hright_nonneg : 0 <= (p : Rat) - 1 := sub_nonneg.mpr hp_rat
      have hfactor :
          (p : Rat) ^ (2 * (j + 1)) - (p : Rat) ^ (2 * j) =
            (p : Rat) ^ (2 * j) * ((p : Rat) ^ 2 - 1) := by
        rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
        ring
      rw [hfactor]
      exact mul_le_mul hpow hp_sub hright_nonneg (le_trans hleft_nonneg hpow)

theorem totient_le_jordanTwo
    (n : Nat)
    (hn : 0 < n) :
    (Nat.totient n : Rat) <=
      TS119.Goldbach.selbergJordanTwoCoefficient n := by
  have hn0 : Not (n = 0) := Nat.ne_of_gt hn
  have htotNat :
      Nat.totient n =
        n.factorization.prod fun p k => Nat.totient (p ^ k) := by
    exact Nat.multiplicative_factorization
      Nat.totient (@Nat.totient_mul) Nat.totient_one hn0
  rw [htotNat]
  rw [TS126.Goldbach.selbergJordanTwoCoefficient_factorization hn0]
  rw [Finsupp.prod, Finsupp.prod]
  push_cast
  refine Finset.prod_le_prod (fun p _hp_mem => by positivity) ?_
  intro p hp_mem
  have hp_prime : p.Prime := by
    simpa [Nat.support_factorization] using
      Nat.prime_of_mem_primeFactors hp_mem
  have hk_pos : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
  exact totient_prime_pow_le_jordanTwo hp_prime hk_pos

theorem eulerTotientLeJordanTwoOnSupport
    (level : Nat) :
    TS144.Goldbach.SelbergEulerTotientLeJordanTwoOnSupport level := by
  intro r hr
  unfold TS122.Goldbach.selbergJordanTwoPenalty
  exact totient_le_jordanTwo r
    (TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hr)

def eulerTransformedWeight
    (level r : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun m =>
    if Dvd.dvd r m then TS144.Goldbach.selbergLCMAbsorbedLambda level m else 0

theorem absorbedDiagonalVector_eq_eulerTransformedWeight
    (level r : Nat) :
    TS129.Goldbach.selbergAbsorbedDiagonalVector
        level
        (TS136.Goldbach.selbergOptimalIntervalWeight level)
        r =
      eulerTransformedWeight level r := by
  unfold TS129.Goldbach.selbergAbsorbedDiagonalVector
  unfold TS119.Goldbach.selbergGcdSquareTransformedWeight
  unfold TS118.Goldbach.selbergLCMAbsorbedWeight
  unfold eulerTransformedWeight
  unfold TS122.Goldbach.selbergOptimizationSupport
  unfold TS121.Goldbach.selbergPositiveQuadraticSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hmpos : 0 < m
  case pos =>
    simp [hmpos, TS144.Goldbach.selbergLCMAbsorbedLambda,
      TS142.Goldbach.selbergConcreteLambda]
  case neg =>
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmpos
    subst m
    simp [TS144.Goldbach.selbergLCMAbsorbedLambda,
      TS142.Goldbach.selbergConcreteLambda]

def eulerDiagonalFilterTerm
    (level r m : Nat) : Rat :=
  if Dvd.dvd r m then TS144.Goldbach.selbergLCMAbsorbedLambda level m else 0

def eulerDiagonalTripleSum
    (level : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun r =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun m =>
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun n =>
        (Nat.totient r : Rat) *
          eulerDiagonalFilterTerm level r m *
            eulerDiagonalFilterTerm level r n

theorem eulerDiagonalSide_eq_tripleSum
    (level : Nat) :
    TS144.Goldbach.selbergEulerTotientDiagonalSideRat level =
      eulerDiagonalTripleSum level := by
  unfold TS144.Goldbach.selbergEulerTotientDiagonalSideRat
  unfold eulerDiagonalTripleSum
  apply Finset.sum_congr rfl
  intro r _hr
  rw [absorbedDiagonalVector_eq_eulerTransformedWeight]
  unfold eulerTransformedWeight
  unfold eulerDiagonalFilterTerm
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

def eulerPairCoefficient
    (level m n : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun r =>
    if Dvd.dvd r (Nat.gcd m n) then (Nat.totient r : Rat) else 0

def eulerPairFirstSide
    (level : Nat) : Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun m =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun n =>
      TS144.Goldbach.selbergLCMAbsorbedLambda level m *
        TS144.Goldbach.selbergLCMAbsorbedLambda level n *
          eulerPairCoefficient level m n

theorem eulerDiagonalFilter_mul_eq_gcdFilter
    (level r m n : Nat) :
    eulerDiagonalFilterTerm level r m *
        eulerDiagonalFilterTerm level r n =
      if Dvd.dvd r (Nat.gcd m n) then
        TS144.Goldbach.selbergLCMAbsorbedLambda level m *
          TS144.Goldbach.selbergLCMAbsorbedLambda level n
      else 0 := by
  unfold eulerDiagonalFilterTerm
  by_cases hg : Dvd.dvd r (Nat.gcd m n)
  case pos =>
    have hm : Dvd.dvd r m := hg.trans (Nat.gcd_dvd_left m n)
    have hn : Dvd.dvd r n := hg.trans (Nat.gcd_dvd_right m n)
    simp [hg, hm, hn]
  case neg =>
    have hp : Not (And (Dvd.dvd r m) (Dvd.dvd r n)) := by
      intro h
      exact hg (Nat.dvd_gcd h.1 h.2)
    by_cases hm : Dvd.dvd r m
    case pos =>
      have hn : Not (Dvd.dvd r n) := fun h => hp (And.intro hm h)
      simp [hg, hm, hn]
    case neg =>
      simp [hg, hm]

theorem eulerDiagonalTripleSum_eq_pairFirst
    (level : Nat) :
    eulerDiagonalTripleSum level = eulerPairFirstSide level := by
  unfold eulerDiagonalTripleSum
  unfold eulerPairFirstSide
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold eulerPairCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [show
    (Nat.totient r : Rat) * eulerDiagonalFilterTerm level r m *
        eulerDiagonalFilterTerm level r n =
      (Nat.totient r : Rat) *
        (eulerDiagonalFilterTerm level r m *
          eulerDiagonalFilterTerm level r n) by ring]
  rw [eulerDiagonalFilter_mul_eq_gcdFilter]
  by_cases hg : Dvd.dvd r (Nat.gcd m n)
  case pos =>
    simp [hg]
    ring
  case neg =>
    simp [hg]

theorem optimizationSupport_filter_dvd_gcd_eq_divisors
    (level m n : Nat)
    (hm : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) m) :
    (TS122.Goldbach.selbergOptimizationSupport level).filter
        (fun r => Dvd.dvd r (Nat.gcd m n)) =
      (Nat.gcd m n).divisors := by
  have hm_full :
      Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) m :=
    (TS121.Goldbach.mem_selbergPositiveQuadraticSupport.mp
      (show Membership.mem (TS121.Goldbach.selbergPositiveQuadraticSupport level) m by
        simpa [TS122.Goldbach.selbergOptimizationSupport] using hm)).1
  have hm_pos : 0 < m :=
    TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hm
  rw [show TS122.Goldbach.selbergOptimizationSupport level =
      TS121.Goldbach.selbergPositiveQuadraticSupport level by rfl]
  apply Finset.ext
  intro r
  rw [Finset.mem_filter, Nat.mem_divisors]
  constructor
  case mp =>
    intro h
    exact And.intro h.2 (Nat.gcd_pos_of_pos_left n hm_pos).ne'
  case mpr =>
    intro h
    have hfull :
        Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) r := by
      have heq := TS121.Goldbach.selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left
        level m n hm_full hm_pos
      have hrfilter :
          Membership.mem
            ((TS108.Goldbach.selbergQuadraticSupport level).filter
              (fun d => Dvd.dvd d (Nat.gcd m n))) r := by
        rw [heq]
        exact Nat.mem_divisors.mpr h
      exact (Finset.mem_filter.mp hrfilter).1
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos h.1 (Nat.gcd_pos_of_pos_left n hm_pos)
    exact And.intro
      (TS121.Goldbach.mem_selbergPositiveQuadraticSupport.mpr
        (And.intro hfull hrpos))
      h.1

theorem eulerPairCoefficient_eq_gcd
    (level m n : Nat)
    (hm : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) m) :
    eulerPairCoefficient level m n = (Nat.gcd m n : Rat) := by
  unfold eulerPairCoefficient
  rw [<- Finset.sum_filter]
  rw [optimizationSupport_filter_dvd_gcd_eq_divisors level m n hm]
  exact_mod_cast Nat.sum_totient (Nat.gcd m n)

theorem eulerPairFirstSide_eq_gcdDenseSide
    (level : Nat) :
    eulerPairFirstSide level = TS144.Goldbach.selbergGcdAbsorbedDenseSideRat level := by
  unfold eulerPairFirstSide
  unfold TS144.Goldbach.selbergGcdAbsorbedDenseSideRat
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n _hn
  rw [eulerPairCoefficient_eq_gcd level m n hm]

theorem gcdEulerTotientDiagonalization
    (level : Nat) :
    TS144.Goldbach.SelbergGcdEulerTotientDiagonalization level := by
  unfold TS144.Goldbach.SelbergGcdEulerTotientDiagonalization
  calc
    TS144.Goldbach.selbergGcdAbsorbedDenseSideRat level =
        eulerPairFirstSide level :=
      (eulerPairFirstSide_eq_gcdDenseSide level).symm
    _ = eulerDiagonalTripleSum level :=
      (eulerDiagonalTripleSum_eq_pairFirst level).symm
    _ = TS144.Goldbach.selbergEulerTotientDiagonalSideRat level :=
      (eulerDiagonalSide_eq_tripleSum level).symm

/-- The corrected TS144 lcm dense-side budget is unconditional at positive level. -/
theorem selbergLCMDenseSideBudgetUpperBound
    (level : Nat)
    (hlevel : 0 < level) :
    TS144.Goldbach.SelbergLCMDenseSideBudgetUpperBound level := by
  exact TS144.Goldbach.selbergLCMDenseSideBudgetUpperBound_of_totient_route
    level
    hlevel
    (gcdEulerTotientDiagonalization level)
    (eulerTotientLeJordanTwoOnSupport level)

/-- The fractional main term is bounded by interval length times `1 / D`. -/
theorem selbergFractionalMainTerm_le_optimalBudget
    (level x Q : Nat)
    (hlevel : 0 < level) :
    TS142.Goldbach.selbergFractionalMainTermRat level x Q <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        (1 / TS122.Goldbach.selbergOptimizationDenominator level) := by
  exact TS144.Goldbach.selbergFractionalMainTerm_le_optimalBudget
    level x Q (selbergLCMDenseSideBudgetUpperBound level hlevel)

/-- TS145 package closing the two arithmetic fields of the TS144 refactor. -/
structure EulerTotientJordanDominationDischarge
    (level x Q n : Nat) where
  hlevel :
    0 < level

  gcd_totient_diagonalization :
    TS144.Goldbach.SelbergGcdEulerTotientDiagonalization level

  totient_le_jordan_two :
    TS144.Goldbach.SelbergEulerTotientLeJordanTwoOnSupport level

  dense_side_upper_budget :
    TS144.Goldbach.SelbergLCMDenseSideBudgetUpperBound level

  fractional_main_term_upper_budget :
    TS142.Goldbach.selbergFractionalMainTermRat level x Q <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        (1 / TS122.Goldbach.selbergOptimizationDenominator level)

  refactor :
    TS144.Goldbach.LCMDenseSideBudgetRefactor level x Q n

/-- Concrete TS145 discharge package. -/
def eulerTotientJordanDominationDischarge
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    EulerTotientJordanDominationDischarge level x Q n where
  hlevel := hlevel
  gcd_totient_diagonalization := gcdEulerTotientDiagonalization level
  totient_le_jordan_two := eulerTotientLeJordanTwoOnSupport level
  dense_side_upper_budget :=
    selbergLCMDenseSideBudgetUpperBound level hlevel
  fractional_main_term_upper_budget :=
    selbergFractionalMainTerm_le_optimalBudget level x Q hlevel
  refactor :=
    TS144.Goldbach.lcmDenseSideBudgetRefactor
      level x Q n hlevel
      (gcdEulerTotientDiagonalization level)
      (eulerTotientLeJordanTwoOnSupport level)

/-- Target proposition for the unconditional TS145 arithmetic discharge. -/
def EulerTotientJordanDominationDischargeTarget : Prop :=
  forall level x Q n : Nat,
    0 < level ->
      Nonempty (EulerTotientJordanDominationDischarge level x Q n)

/-- The TS145 target is populated for every positive level. -/
theorem eulerTotientJordanDominationDischargeTarget :
    EulerTotientJordanDominationDischargeTarget := by
  intro level x Q n hlevel
  exact Nonempty.intro
    (eulerTotientJordanDominationDischarge level x Q n hlevel)

end Goldbach
end TS145
