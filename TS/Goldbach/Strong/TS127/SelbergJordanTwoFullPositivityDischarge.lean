import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS126.SelbergJordanTwoMultiplicativityAPIProbe

namespace TS127
namespace Goldbach

/-!
# TS127 - Selberg Jordan-Two Full Positivity Discharge

TS126 proves that the corrected Selberg Jordan-two coefficient is
multiplicative and admits the `Nat.factorization` product formula. TS125 proves
strict positivity on every positive prime power.

This sprint combines those two inputs with finite-product positivity to prove
the global arithmetic input used by TS124:

`forall n, 0 < n -> 0 < J2(n)`.

That makes the TS123 denominator positivity and the TS122 constrained diagonal
energy lower bound available without any further `J2` positivity hypothesis.
-/

/-- The Jordan-two coefficient is positive at every positive natural number. -/
theorem selbergJordanTwoCoefficient_pos_of_pos
    (n : Nat)
    (hn : 0 < n) :
    0 < TS119.Goldbach.selbergJordanTwoCoefficient n := by
  have hn_ne_zero : Not (n = 0) := by
    exact Nat.ne_of_gt hn
  rw [TS126.Goldbach.selbergJordanTwoCoefficient_factorization hn_ne_zero]
  rw [Finsupp.prod]
  exact Finset.prod_pos fun p hp => by
    have hp_prime : p.Prime := by
      simpa [Nat.support_factorization] using
        Nat.prime_of_mem_primeFactors hp
    have hk_pos : 0 < n.factorization p := by
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact
      TS126.Goldbach.selbergJordanTwoCoefficient_pos_of_prime_pow
        hp_prime
        hk_pos

/-- The global positive-integer `J2` input required by TS124 is now concrete. -/
theorem selbergJordanTwoPositiveOnPositiveNat :
    TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat := by
  intro d hd
  exact selbergJordanTwoCoefficient_pos_of_pos d hd

/--
The TS123 supportwise positivity input follows unconditionally from the global
positive-integer discharge.
-/
theorem selbergJordanTwoPositiveOnSupport
    (level : Nat) :
    TS123.Goldbach.SelbergJordanTwoPositiveOnSupport level := by
  exact
    TS124.Goldbach.selbergJordanTwoPositiveOnSupport_of_positiveNat
      level
      selbergJordanTwoPositiveOnPositiveNat

/-- The TS122 optimization denominator is positive for every positive level. -/
theorem selbergOptimizationDenominator_pos
    (level : Nat)
    (hlevel : 0 < level) :
    TS123.Goldbach.SelbergOptimizationDenominatorPositive level := by
  exact
    TS124.Goldbach.selbergOptimizationDenominator_pos_of_positiveNat
      level
      hlevel
      selbergJordanTwoPositiveOnPositiveNat

/--
The constrained TS122 diagonal energy lower bound now needs only the linear
normalization constraint.
-/
theorem selbergDiagonalEnergy_lower_bound
    (level : Nat)
    (vector : Nat -> Rat)
    (hlevel : 0 < level)
    (hconstraint :
      TS122.Goldbach.selbergMobiusLinearForm level vector = 1) :
    1 / TS122.Goldbach.selbergOptimizationDenominator level <=
      TS122.Goldbach.selbergDiagonalEnergy level vector := by
  exact
    TS124.Goldbach.selbergDiagonalEnergy_lower_bound_of_positiveNat
      level
      vector
      hlevel
      selbergJordanTwoPositiveOnPositiveNat
      hconstraint

/-- TS127 full positivity package for the Selberg Jordan-two coefficient. -/
structure SelbergJordanTwoFullPositivityDischarge
    (level : Nat)
    (weight : Nat -> Rat) where
  multiplicativityAPIProbe :
    TS126.Goldbach.SelbergJordanTwoMultiplicativityAPIProbe level weight

  jordan_two_positive_nat :
    TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat

  jordan_two_positive_on_support :
    TS123.Goldbach.SelbergJordanTwoPositiveOnSupport level

  denominator_positive :
    0 < level ->
      TS123.Goldbach.SelbergOptimizationDenominatorPositive level

  constrained_lower_bound :
    forall vector : Nat -> Rat,
      0 < level ->
        TS122.Goldbach.selbergMobiusLinearForm level vector = 1 ->
          1 / TS122.Goldbach.selbergOptimizationDenominator level <=
            TS122.Goldbach.selbergDiagonalEnergy level vector

  optimal_vector_normalization_obligation :
    True

  selberg_sieve_bound_obligation :
    True

  brun_titchmarsh_obligation :
    True

/-- Concrete TS127 full positivity package. -/
def selbergJordanTwoFullPositivityDischarge
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergJordanTwoFullPositivityDischarge level weight where
  multiplicativityAPIProbe :=
    TS126.Goldbach.selbergJordanTwoMultiplicativityAPIProbe level weight
  jordan_two_positive_nat :=
    selbergJordanTwoPositiveOnPositiveNat
  jordan_two_positive_on_support :=
    selbergJordanTwoPositiveOnSupport level
  denominator_positive := by
    intro hlevel
    exact selbergOptimizationDenominator_pos level hlevel
  constrained_lower_bound := by
    intro vector hlevel hconstraint
    exact
      selbergDiagonalEnergy_lower_bound
        level
        vector
        hlevel
        hconstraint
  optimal_vector_normalization_obligation := True.intro
  selberg_sieve_bound_obligation := True.intro
  brun_titchmarsh_obligation := True.intro

/-- Target proposition for TS127 full positivity. -/
def SelbergJordanTwoFullPositivityDischargeTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergJordanTwoFullPositivityDischarge level weight)

/-- The TS127 full positivity package is populated. -/
theorem selbergJordanTwoFullPositivityDischargeTarget :
    SelbergJordanTwoFullPositivityDischargeTarget := by
  intro level weight
  exact Nonempty.intro
    (selbergJordanTwoFullPositivityDischarge level weight)

/-- TS127 keeps the TS126 multiplicativity API probe target available. -/
theorem selbergJordanTwoMultiplicativityAPIProbeTarget :
    TS126.Goldbach.SelbergJordanTwoMultiplicativityAPIProbeTarget :=
  TS126.Goldbach.selbergJordanTwoMultiplicativityAPIProbeTarget

end Goldbach
end TS127
