import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import TS.Goldbach.Strong.TS123.SelbergJordanTwoPositivityProbe

namespace TS124
namespace Goldbach

/-!
# TS124 - Selberg Jordan-Two Positivity API Probe

TS123 shows that the TS122 optimization denominator is positive once the
Jordan-two coefficient is positive on the finite positive support. This sprint
starts discharging that arithmetic input without adding any global assumption.

The full proof that `J2(d) > 0` for every positive `d` is still multiplicative
arithmetic. Here we prove concrete local facts that the later proof will need:

* `J2(1) = 1`;
* for prime `p`, `J2(p) = p^2 - 1`;
* consequently `J2(p) > 0` for prime `p`;
* full positive-integer positivity implies the TS123 supportwise positivity
  input, and therefore the TS122 denominator positivity and lower bound.
-/

/-- The Jordan-two coefficient at `1` is `1`. -/
theorem selbergJordanTwoCoefficient_one :
    TS119.Goldbach.selbergJordanTwoCoefficient 1 = 1 := by
  unfold TS119.Goldbach.selbergJordanTwoCoefficient
  unfold TS119.Goldbach.selbergJordanTwoFunction
  rw [ArithmeticFunction.mul_apply_one]
  simp [ArithmeticFunction.moebius_apply_one, ArithmeticFunction.pow_apply]

/-- At a prime, the Jordan-two coefficient is `p^2 - 1`. -/
theorem selbergJordanTwoCoefficient_prime
    {p : Nat}
    (hp : p.Prime) :
    TS119.Goldbach.selbergJordanTwoCoefficient p =
      (p : Rat) ^ (2 : Nat) - 1 := by
  rw [show p = p ^ (1 : Nat) by simp]
  unfold TS119.Goldbach.selbergJordanTwoCoefficient
  unfold TS119.Goldbach.selbergJordanTwoFunction
  rw [ArithmeticFunction.mul_apply]
  rw
    [Nat.sum_divisorsAntidiagonal
      (fun a b : Nat =>
        (ArithmeticFunction.moebius : ArithmeticFunction Rat) a *
          (ArithmeticFunction.pow 2 : ArithmeticFunction Rat) b)]
  rw [Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp
    [ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.pow_apply]
  have hp_ne_zero_rat : Not ((p : Rat) = 0) := by
    exact_mod_cast hp.ne_zero
  field_simp [hp_ne_zero_rat]
  ring

/-- The Jordan-two coefficient is positive at every prime. -/
theorem selbergJordanTwoCoefficient_pos_of_prime
    {p : Nat}
    (hp : p.Prime) :
    0 < TS119.Goldbach.selbergJordanTwoCoefficient p := by
  rw [selbergJordanTwoCoefficient_prime hp]
  have hp_rat : (1 : Rat) < (p : Rat) := by
    exact_mod_cast hp.one_lt
  have hp_pos : (0 : Rat) < (p : Rat) :=
    lt_trans zero_lt_one hp_rat
  have hp_sq_pos : 1 < (p : Rat) ^ (2 : Nat) := by
    nlinarith [mul_pos hp_pos hp_pos]
  nlinarith

/-- Global positive-integer `J2` positivity, named as the next arithmetic input. -/
def SelbergJordanTwoPositiveOnPositiveNat : Prop :=
  forall d : Nat,
    0 < d -> 0 < TS122.Goldbach.selbergJordanTwoPenalty d

/--
Full positive-integer positivity immediately supplies the TS123 finite-support
positivity input.
-/
theorem selbergJordanTwoPositiveOnSupport_of_positiveNat
    (level : Nat)
    (hJ2_pos : SelbergJordanTwoPositiveOnPositiveNat) :
    TS123.Goldbach.SelbergJordanTwoPositiveOnSupport level := by
  intro d hd
  have hd_pos : 0 < d := by
    have hd' := hd
    simp
      [TS122.Goldbach.selbergOptimizationSupport,
        TS121.Goldbach.selbergPositiveQuadraticSupport,
        TS108.Goldbach.selbergQuadraticSupport] at hd'
    exact hd'.2
  exact hJ2_pos d hd_pos

/--
Full positive-integer `J2` positivity implies positivity of the Selberg
optimization denominator for `0 < level`.
-/
theorem selbergOptimizationDenominator_pos_of_positiveNat
    (level : Nat)
    (hlevel : 0 < level)
    (hJ2_pos : SelbergJordanTwoPositiveOnPositiveNat) :
    TS123.Goldbach.SelbergOptimizationDenominatorPositive level := by
  exact
    TS123.Goldbach.selbergOptimizationDenominator_pos_of_jordanTwo_pos
      level
      hlevel
      (selbergJordanTwoPositiveOnSupport_of_positiveNat level hJ2_pos)

/--
The constrained TS122 energy lower bound can be invoked from the single global
positive-integer `J2` positivity input.
-/
theorem selbergDiagonalEnergy_lower_bound_of_positiveNat
    (level : Nat)
    (vector : Nat -> Rat)
    (hlevel : 0 < level)
    (hJ2_pos : SelbergJordanTwoPositiveOnPositiveNat)
    (hconstraint :
      TS122.Goldbach.selbergMobiusLinearForm level vector = 1) :
    1 / TS122.Goldbach.selbergOptimizationDenominator level <=
      TS122.Goldbach.selbergDiagonalEnergy level vector := by
  exact
    TS123.Goldbach.selbergDiagonalEnergy_lower_bound_of_jordanTwo_pos
      level
      vector
      hlevel
      (selbergJordanTwoPositiveOnSupport_of_positiveNat level hJ2_pos)
      hconstraint

/--
TS124 positivity API probe package.

The package records the concrete `J2(1)` and prime positivity facts, plus the
bridge saying that the future global positivity theorem will feed TS123/TS122.
-/
structure SelbergJordanTwoPositivityAPIProbe
    (level : Nat)
    (weight : Nat -> Rat) where
  positivityProbe :
    TS123.Goldbach.SelbergJordanTwoPositivityProbe level weight

  jordan_two_at_one :
    TS119.Goldbach.selbergJordanTwoCoefficient 1 = 1

  jordan_two_at_prime :
    forall p : Nat,
      p.Prime ->
        TS119.Goldbach.selbergJordanTwoCoefficient p =
          (p : Rat) ^ (2 : Nat) - 1

  jordan_two_prime_pos :
    forall p : Nat,
      p.Prime -> 0 < TS119.Goldbach.selbergJordanTwoCoefficient p

  positive_nat_to_support :
    SelbergJordanTwoPositiveOnPositiveNat ->
      TS123.Goldbach.SelbergJordanTwoPositiveOnSupport level

  denominator_pos_from_positive_nat :
    0 < level ->
      SelbergJordanTwoPositiveOnPositiveNat ->
        TS123.Goldbach.SelbergOptimizationDenominatorPositive level

  constrained_lower_bound_from_positive_nat :
    forall vector : Nat -> Rat,
      0 < level ->
        SelbergJordanTwoPositiveOnPositiveNat ->
          TS122.Goldbach.selbergMobiusLinearForm level vector = 1 ->
            1 / TS122.Goldbach.selbergOptimizationDenominator level <=
              TS122.Goldbach.selbergDiagonalEnergy level vector

  jordan_two_positive_nat_obligation :
    Prop

  jordan_two_positive_nat_obligation_eq :
    jordan_two_positive_nat_obligation =
      SelbergJordanTwoPositiveOnPositiveNat

  multiplicative_positivity_route_obligation :
    True

  optimal_vector_normalization_obligation :
    True

  selberg_sieve_bound_obligation :
    True

/-- Concrete TS124 positivity API probe package. -/
def selbergJordanTwoPositivityAPIProbe
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergJordanTwoPositivityAPIProbe level weight where
  positivityProbe :=
    TS123.Goldbach.selbergJordanTwoPositivityProbe level weight
  jordan_two_at_one :=
    selbergJordanTwoCoefficient_one
  jordan_two_at_prime := by
    intro p hp
    exact selbergJordanTwoCoefficient_prime hp
  jordan_two_prime_pos := by
    intro p hp
    exact selbergJordanTwoCoefficient_pos_of_prime hp
  positive_nat_to_support := by
    intro hJ2_pos
    exact selbergJordanTwoPositiveOnSupport_of_positiveNat level hJ2_pos
  denominator_pos_from_positive_nat := by
    intro hlevel hJ2_pos
    exact
      selbergOptimizationDenominator_pos_of_positiveNat
        level
        hlevel
        hJ2_pos
  constrained_lower_bound_from_positive_nat := by
    intro vector hlevel hJ2_pos hconstraint
    exact
      selbergDiagonalEnergy_lower_bound_of_positiveNat
        level
        vector
        hlevel
        hJ2_pos
        hconstraint
  jordan_two_positive_nat_obligation :=
    SelbergJordanTwoPositiveOnPositiveNat
  jordan_two_positive_nat_obligation_eq := rfl
  multiplicative_positivity_route_obligation := True.intro
  optimal_vector_normalization_obligation := True.intro
  selberg_sieve_bound_obligation := True.intro

/-- Target proposition for TS124 positivity API probe. -/
def SelbergJordanTwoPositivityAPIProbeTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergJordanTwoPositivityAPIProbe level weight)

/-- The TS124 positivity API probe package is populated. -/
theorem selbergJordanTwoPositivityAPIProbeTarget :
    SelbergJordanTwoPositivityAPIProbeTarget := by
  intro level weight
  exact Nonempty.intro (selbergJordanTwoPositivityAPIProbe level weight)

/-- TS124 keeps the TS123 positivity probe target available. -/
theorem selbergJordanTwoPositivityProbeTarget :
    TS123.Goldbach.SelbergJordanTwoPositivityProbeTarget :=
  TS123.Goldbach.selbergJordanTwoPositivityProbeTarget

end Goldbach
end TS124
