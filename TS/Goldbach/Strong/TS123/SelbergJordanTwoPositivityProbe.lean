import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import TS.Goldbach.Strong.TS122.SelbergDiagonalOptimizationLedger

namespace TS123
namespace Goldbach

/-!
# TS123 - Selberg Jordan-Two Positivity Probe

TS122 proves the finite weighted Cauchy optimization inequality for the
corrected Selberg diagonal form, assuming positivity of the Jordan-two
coefficient on the finite support and positivity of the optimization
denominator.

This sprint keeps the scope deliberately local. It records the current support
reality, proves that `1` lies in the optimization support as soon as
`0 < level`, proves the Mobius coefficient at `1`, and shows that
Jordan-two positivity on the support implies denominator positivity.

The full multiplicative proof that `J2(d) > 0` for every positive `d` remains
the next arithmetic input.
-/

/-- The current TS122 optimization support is the positive finite window. -/
theorem selbergOptimizationSupport_eq_positive_support
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationSupport level =
      TS121.Goldbach.selbergPositiveQuadraticSupport level :=
  rfl

/--
The current optimization support is not yet a squarefree-only support; it is
the positive part of the finite quadratic window.
-/
theorem selbergOptimizationSupport_eq_positive_range_filter
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationSupport level =
      (TS108.Goldbach.selbergQuadraticSupport level).filter fun d =>
        0 < d :=
  rfl

/--
Concrete support diagnostic: for `4 <= level`, the current optimization
support contains `4`.
-/
theorem four_mem_selbergOptimizationSupport_of_level_ge_four
    (level : Nat)
    (hlevel : 4 <= level) :
    Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) 4 := by
  have hlt : 4 < level + 1 :=
    Nat.lt_succ_iff.mpr hlevel
  simp
    [TS122.Goldbach.selbergOptimizationSupport,
      TS121.Goldbach.selbergPositiveQuadraticSupport,
      TS108.Goldbach.selbergQuadraticSupport,
      hlt]

/-- The index `4` is not squarefree. -/
theorem not_squarefree_four :
    Not (Squarefree (4 : Nat)) := by
  intro hsq
  have hunit : IsUnit (2 : Nat) := by
    exact hsq 2 (by norm_num)
  have htwo_eq_one : (2 : Nat) = 1 :=
    Nat.isUnit_iff.mp hunit
  norm_num at htwo_eq_one

/-- For `0 < level`, the index `1` belongs to the TS122 optimization support. -/
theorem one_mem_selbergOptimizationSupport
    (level : Nat)
    (hlevel : 0 < level) :
    Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) 1 := by
  simp
    [TS122.Goldbach.selbergOptimizationSupport,
      TS121.Goldbach.selbergPositiveQuadraticSupport,
      TS108.Goldbach.selbergQuadraticSupport,
      hlevel]

/-- The rational Mobius coefficient used by TS122 is `1` at `1`. -/
theorem selbergMobiusRatCoefficient_one :
    TS122.Goldbach.selbergMobiusRatCoefficient 1 = 1 := by
  simp
    [TS122.Goldbach.selbergMobiusRatCoefficient,
      ArithmeticFunction.moebius_apply_one]

/-- Local name for the positivity input required by TS122. -/
def SelbergJordanTwoPositiveOnSupport
    (level : Nat) :
    Prop :=
  forall d : Nat,
    Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d ->
      0 < TS122.Goldbach.selbergJordanTwoPenalty d

/-- Local name for the denominator positivity input required by TS122. -/
def SelbergOptimizationDenominatorPositive
    (level : Nat) :
    Prop :=
  0 < TS122.Goldbach.selbergOptimizationDenominator level

/--
Every denominator summand is nonnegative if the Jordan-two coefficient is
positive on the support.
-/
theorem selbergOptimizationDenominator_term_nonneg
    (level d : Nat)
    (hJ2_pos : SelbergJordanTwoPositiveOnSupport level)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    0 <=
      TS122.Goldbach.selbergMobiusRatCoefficient d ^ (2 : Nat) /
        TS122.Goldbach.selbergJordanTwoPenalty d := by
  exact
    div_nonneg
      (sq_nonneg (TS122.Goldbach.selbergMobiusRatCoefficient d))
      (hJ2_pos d hd).le

/--
The denominator summand at `1` is strictly positive if `J2(1)` is positive.
-/
theorem selbergOptimizationDenominator_term_one_pos
    (level : Nat)
    (hlevel : 0 < level)
    (hJ2_pos : SelbergJordanTwoPositiveOnSupport level) :
    0 <
      TS122.Goldbach.selbergMobiusRatCoefficient 1 ^ (2 : Nat) /
        TS122.Goldbach.selbergJordanTwoPenalty 1 := by
  have hmem_one :
      Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) 1 :=
    one_mem_selbergOptimizationSupport level hlevel
  have hJ2_one :
      0 < TS122.Goldbach.selbergJordanTwoPenalty 1 :=
    hJ2_pos 1 hmem_one
  rw [selbergMobiusRatCoefficient_one]
  exact div_pos (by norm_num : (0 : Rat) < 1 ^ (2 : Nat)) hJ2_one

/--
The TS122 denominator is positive once the support is nonempty (`0 < level`)
and `J2` is positive on that support.
-/
theorem selbergOptimizationDenominator_pos_of_jordanTwo_pos
    (level : Nat)
    (hlevel : 0 < level)
    (hJ2_pos : SelbergJordanTwoPositiveOnSupport level) :
    SelbergOptimizationDenominatorPositive level := by
  unfold SelbergOptimizationDenominatorPositive
  unfold TS122.Goldbach.selbergOptimizationDenominator
  refine Finset.sum_pos' ?h_nonneg ?h_pos
  case h_nonneg =>
    intro d hd
    exact
      selbergOptimizationDenominator_term_nonneg
        level
        d
        hJ2_pos
        hd
  case h_pos =>
    exact
      Exists.intro
        1
        (And.intro
          (one_mem_selbergOptimizationSupport level hlevel)
          (selbergOptimizationDenominator_term_one_pos
            level
            hlevel
            hJ2_pos))

/--
With the TS123 denominator positivity bridge, the constrained TS122 lower
bound needs only the local `J2` positivity input and `0 < level`.
-/
theorem selbergDiagonalEnergy_lower_bound_of_jordanTwo_pos
    (level : Nat)
    (vector : Nat -> Rat)
    (hlevel : 0 < level)
    (hJ2_pos : SelbergJordanTwoPositiveOnSupport level)
    (hconstraint :
      TS122.Goldbach.selbergMobiusLinearForm level vector = 1) :
    1 / TS122.Goldbach.selbergOptimizationDenominator level <=
      TS122.Goldbach.selbergDiagonalEnergy level vector := by
  exact
    TS122.Goldbach.selbergDiagonalEnergy_lower_bound_of_constraint
      level
      vector
      hJ2_pos
      (selbergOptimizationDenominator_pos_of_jordanTwo_pos
        level
        hlevel
        hJ2_pos)
      hconstraint

/-- Candidate optimal vector for the next equality-case sprint. -/
def selbergOptimalDiagonalVectorCandidate
    (level : Nat)
    (d : Nat) :
    Rat :=
  TS122.Goldbach.selbergMobiusRatCoefficient d /
    (TS122.Goldbach.selbergOptimizationDenominator level *
      TS122.Goldbach.selbergJordanTwoPenalty d)

/--
TS123 positivity bridge package.

It does not prove the multiplicative positivity of `J2`; it proves that this
single arithmetic input is enough to unlock the denominator positivity needed
by the TS122 Cauchy optimization layer.
-/
structure SelbergJordanTwoPositivityProbe
    (level : Nat)
    (weight : Nat -> Rat) where
  diagonalOptimization :
    TS122.Goldbach.SelbergDiagonalOptimization level weight

  support_is_positive_window :
    TS122.Goldbach.selbergOptimizationSupport level =
      TS121.Goldbach.selbergPositiveQuadraticSupport level

  one_in_support_if_level_pos :
    0 < level ->
      Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) 1

  mobius_one :
    TS122.Goldbach.selbergMobiusRatCoefficient 1 = 1

  denominator_pos_from_jordan_two_pos :
    0 < level ->
      SelbergJordanTwoPositiveOnSupport level ->
        SelbergOptimizationDenominatorPositive level

  constrained_lower_bound_from_jordan_two_pos :
    forall vector : Nat -> Rat,
      0 < level ->
        SelbergJordanTwoPositiveOnSupport level ->
          TS122.Goldbach.selbergMobiusLinearForm level vector = 1 ->
            1 / TS122.Goldbach.selbergOptimizationDenominator level <=
              TS122.Goldbach.selbergDiagonalEnergy level vector

  jordan_two_positivity_obligation :
    Prop

  jordan_two_positivity_obligation_eq :
    jordan_two_positivity_obligation =
      SelbergJordanTwoPositiveOnSupport level

  optimal_vector_candidate :
    Nat -> Rat

  optimal_vector_candidate_eq :
    forall d : Nat,
      optimal_vector_candidate d =
        selbergOptimalDiagonalVectorCandidate level d

  optimal_vector_normalization_obligation :
    True

  selberg_sieve_bound_obligation :
    True

/-- Concrete TS123 positivity probe package. -/
def selbergJordanTwoPositivityProbe
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergJordanTwoPositivityProbe level weight where
  diagonalOptimization :=
    TS122.Goldbach.selbergDiagonalOptimization level weight
  support_is_positive_window :=
    selbergOptimizationSupport_eq_positive_support level
  one_in_support_if_level_pos := by
    intro hlevel
    exact one_mem_selbergOptimizationSupport level hlevel
  mobius_one :=
    selbergMobiusRatCoefficient_one
  denominator_pos_from_jordan_two_pos := by
    intro hlevel hJ2_pos
    exact
      selbergOptimizationDenominator_pos_of_jordanTwo_pos
        level
        hlevel
        hJ2_pos
  constrained_lower_bound_from_jordan_two_pos := by
    intro vector hlevel hJ2_pos hconstraint
    exact
      selbergDiagonalEnergy_lower_bound_of_jordanTwo_pos
        level
        vector
        hlevel
        hJ2_pos
        hconstraint
  jordan_two_positivity_obligation :=
    SelbergJordanTwoPositiveOnSupport level
  jordan_two_positivity_obligation_eq := rfl
  optimal_vector_candidate :=
    selbergOptimalDiagonalVectorCandidate level
  optimal_vector_candidate_eq := by
    intro d
    rfl
  optimal_vector_normalization_obligation := True.intro
  selberg_sieve_bound_obligation := True.intro

/-- Target proposition for TS123 positivity probe. -/
def SelbergJordanTwoPositivityProbeTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergJordanTwoPositivityProbe level weight)

/-- The TS123 positivity probe package is populated. -/
theorem selbergJordanTwoPositivityProbeTarget :
    SelbergJordanTwoPositivityProbeTarget := by
  intro level weight
  exact Nonempty.intro (selbergJordanTwoPositivityProbe level weight)

/-- TS123 keeps the TS122 optimization target available. -/
theorem selbergDiagonalOptimizationTarget :
    TS122.Goldbach.SelbergDiagonalOptimizationTarget :=
  TS122.Goldbach.selbergDiagonalOptimizationTarget

end Goldbach
end TS123
