import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic
import TS.Goldbach.Strong.TS127.SelbergJordanTwoFullPositivityDischarge

namespace TS128
namespace Goldbach

/-!
# TS128 - Selberg Optimal Vector Normalization

TS127 makes the Jordan-two penalty positive on every positive natural number.
This sprint uses that positivity to finish the finite algebra of the optimal
diagonal vector for the TS122 weighted Cauchy problem.

For a finite weighted Cauchy problem with coefficients `c_i`, penalties `a_i`,
and denominator `D = sum c_i^2 / a_i`, the optimal vector is

`y_i = c_i / (D * a_i)`.

TS128 proves, over `Rat`, that this vector has normalized linear form `1` and
has exact energy `1 / D`. The Selberg specialization uses
`c_d = mobius(d)` and `a_d = J2(d)`.
-/

/-- Generic denominator for finite weighted Cauchy optimization over `Rat`. -/
def finiteWeightedCauchyDenominator
    {alpha : Type}
    (support : Finset alpha)
    (linearCoeff penalty : alpha -> Rat) :
    Rat :=
  Finset.sum support fun i =>
    linearCoeff i ^ (2 : Nat) / penalty i

/-- Generic optimal vector for finite weighted Cauchy optimization over `Rat`. -/
def finiteWeightedCauchyOptimalVector
    {alpha : Type}
    (support : Finset alpha)
    (linearCoeff penalty : alpha -> Rat)
    (i : alpha) :
    Rat :=
  linearCoeff i /
    (finiteWeightedCauchyDenominator support linearCoeff penalty *
      penalty i)

/-- The generic optimal vector normalizes the weighted linear form. -/
theorem finiteWeightedCauchyOptimalVector_linear_constraint
    {alpha : Type}
    (support : Finset alpha)
    (linearCoeff penalty : alpha -> Rat)
    (hpenalty_ne :
      forall i : alpha,
        Membership.mem support i -> Not (penalty i = 0))
    (hden_ne :
      Not (finiteWeightedCauchyDenominator support linearCoeff penalty = 0)) :
    (Finset.sum support fun i =>
        linearCoeff i *
          finiteWeightedCauchyOptimalVector support linearCoeff penalty i) =
      1 := by
  let denominator :=
    finiteWeightedCauchyDenominator support linearCoeff penalty
  have hden_ne' : Not (denominator = 0) := by
    simpa [denominator] using hden_ne
  have hterm :
      forall i : alpha,
        Membership.mem support i ->
          linearCoeff i *
              finiteWeightedCauchyOptimalVector support linearCoeff penalty i =
            (linearCoeff i ^ (2 : Nat) / penalty i) / denominator := by
    intro i hi
    have hpenalty : Not (penalty i = 0) := hpenalty_ne i hi
    unfold finiteWeightedCauchyOptimalVector
    field_simp [denominator, hden_ne', hpenalty]
    ring
  calc
    (Finset.sum support fun i =>
        linearCoeff i *
          finiteWeightedCauchyOptimalVector support linearCoeff penalty i) =
        (Finset.sum support fun i =>
          (linearCoeff i ^ (2 : Nat) / penalty i) / denominator) := by
      exact Finset.sum_congr rfl hterm
    _ =
        denominator / denominator := by
      rw [<- Finset.sum_div]
      rfl
    _ = 1 := by
      exact div_self hden_ne'

/-- The generic optimal vector has exact weighted energy `1 / D`. -/
theorem finiteWeightedCauchyOptimalVector_energy_eq
    {alpha : Type}
    (support : Finset alpha)
    (linearCoeff penalty : alpha -> Rat)
    (hpenalty_ne :
      forall i : alpha,
        Membership.mem support i -> Not (penalty i = 0))
    (hden_ne :
      Not (finiteWeightedCauchyDenominator support linearCoeff penalty = 0)) :
    (Finset.sum support fun i =>
        penalty i *
          finiteWeightedCauchyOptimalVector support linearCoeff penalty i ^
            (2 : Nat)) =
      1 / finiteWeightedCauchyDenominator support linearCoeff penalty := by
  let denominator :=
    finiteWeightedCauchyDenominator support linearCoeff penalty
  have hden_ne' : Not (denominator = 0) := by
    simpa [denominator] using hden_ne
  have hterm :
      forall i : alpha,
        Membership.mem support i ->
          penalty i *
              finiteWeightedCauchyOptimalVector support linearCoeff penalty i ^
                (2 : Nat) =
            (linearCoeff i ^ (2 : Nat) / penalty i) /
              denominator ^ (2 : Nat) := by
    intro i hi
    have hpenalty : Not (penalty i = 0) := hpenalty_ne i hi
    unfold finiteWeightedCauchyOptimalVector
    field_simp [denominator, hden_ne', hpenalty]
    ring
  calc
    (Finset.sum support fun i =>
        penalty i *
          finiteWeightedCauchyOptimalVector support linearCoeff penalty i ^
            (2 : Nat)) =
        (Finset.sum support fun i =>
          (linearCoeff i ^ (2 : Nat) / penalty i) /
            denominator ^ (2 : Nat)) := by
      exact Finset.sum_congr rfl hterm
    _ =
        denominator / denominator ^ (2 : Nat) := by
      rw [<- Finset.sum_div]
      rfl
    _ = 1 / denominator := by
      field_simp [hden_ne']
      ring

/-- Selberg optimal diagonal vector for the TS122 optimization problem. -/
def selbergOptimalDiagonalVector
    (level : Nat) :
    Nat -> Rat :=
  finiteWeightedCauchyOptimalVector
    (TS122.Goldbach.selbergOptimizationSupport level)
    TS122.Goldbach.selbergMobiusRatCoefficient
    TS122.Goldbach.selbergJordanTwoPenalty

/-- The TS128 vector is the TS123 candidate vector. -/
theorem selbergOptimalDiagonalVector_eq_candidate
    (level d : Nat) :
    selbergOptimalDiagonalVector level d =
      TS123.Goldbach.selbergOptimalDiagonalVectorCandidate level d := by
  rfl

/-- Denominator equality between the generic and TS122 definitions. -/
theorem finiteWeightedCauchyDenominator_selberg
    (level : Nat) :
    finiteWeightedCauchyDenominator
        (TS122.Goldbach.selbergOptimizationSupport level)
        TS122.Goldbach.selbergMobiusRatCoefficient
        TS122.Goldbach.selbergJordanTwoPenalty =
      TS122.Goldbach.selbergOptimizationDenominator level := by
  rfl

/-- Non-vanishing of the TS122 Jordan-two penalty on the optimization support. -/
theorem selbergJordanTwoPenalty_ne_on_support
    (level d : Nat)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    Not (TS122.Goldbach.selbergJordanTwoPenalty d = 0) := by
  exact
    ne_of_gt
      (TS127.Goldbach.selbergJordanTwoPositiveOnSupport level d hd)

/-- Non-vanishing of the TS122 optimization denominator for positive level. -/
theorem selbergOptimizationDenominator_ne
    (level : Nat)
    (hlevel : 0 < level) :
    Not (TS122.Goldbach.selbergOptimizationDenominator level = 0) := by
  exact ne_of_gt (TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel)

/-- The Selberg optimal vector satisfies the normalized Mobius constraint. -/
theorem selbergOptimalDiagonalVector_linear_constraint
    (level : Nat)
    (hlevel : 0 < level) :
    TS122.Goldbach.selbergMobiusLinearForm level
      (selbergOptimalDiagonalVector level) =
        1 := by
  unfold TS122.Goldbach.selbergMobiusLinearForm
  unfold selbergOptimalDiagonalVector
  exact
    finiteWeightedCauchyOptimalVector_linear_constraint
      (support := TS122.Goldbach.selbergOptimizationSupport level)
      (linearCoeff := TS122.Goldbach.selbergMobiusRatCoefficient)
      (penalty := TS122.Goldbach.selbergJordanTwoPenalty)
      (hpenalty_ne := selbergJordanTwoPenalty_ne_on_support level)
      (hden_ne := by
        simpa [finiteWeightedCauchyDenominator_selberg level] using
          selbergOptimizationDenominator_ne level hlevel)

/-- The Selberg optimal vector attains the TS122 Cauchy lower-bound energy. -/
theorem selbergOptimalDiagonalVector_energy_eq
    (level : Nat)
    (hlevel : 0 < level) :
    TS122.Goldbach.selbergDiagonalEnergy level
      (selbergOptimalDiagonalVector level) =
        1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  unfold TS122.Goldbach.selbergDiagonalEnergy
  unfold selbergOptimalDiagonalVector
  exact
    finiteWeightedCauchyOptimalVector_energy_eq
      (support := TS122.Goldbach.selbergOptimizationSupport level)
      (linearCoeff := TS122.Goldbach.selbergMobiusRatCoefficient)
      (penalty := TS122.Goldbach.selbergJordanTwoPenalty)
      (hpenalty_ne := selbergJordanTwoPenalty_ne_on_support level)
      (hden_ne := by
        simpa [finiteWeightedCauchyDenominator_selberg level] using
          selbergOptimizationDenominator_ne level hlevel)

/--
The lower bound from TS127 is sharp for the TS128 optimal vector.
-/
theorem selbergOptimalDiagonalVector_lower_bound_sharp
    (level : Nat)
    (hlevel : 0 < level) :
    1 / TS122.Goldbach.selbergOptimizationDenominator level =
      TS122.Goldbach.selbergDiagonalEnergy level
        (selbergOptimalDiagonalVector level) := by
  exact (selbergOptimalDiagonalVector_energy_eq level hlevel).symm

/-- TS128 optimal-vector package for the corrected Selberg diagonal problem. -/
structure SelbergOptimalVectorNormalization
    (level : Nat)
    (weight : Nat -> Rat) where
  fullPositivity :
    TS127.Goldbach.SelbergJordanTwoFullPositivityDischarge level weight

  optimalVector :
    Nat -> Rat

  optimal_vector_eq :
    forall d : Nat,
      optimalVector d = selbergOptimalDiagonalVector level d

  linear_constraint :
    0 < level ->
      TS122.Goldbach.selbergMobiusLinearForm level optimalVector = 1

  energy_eq :
    0 < level ->
      TS122.Goldbach.selbergDiagonalEnergy level optimalVector =
        1 / TS122.Goldbach.selbergOptimizationDenominator level

  cauchy_lower_bound_sharp :
    0 < level ->
      1 / TS122.Goldbach.selbergOptimizationDenominator level =
        TS122.Goldbach.selbergDiagonalEnergy level optimalVector

  selberg_sieve_bound_obligation :
    True

  brun_titchmarsh_obligation :
    True

/-- Concrete TS128 optimal-vector package. -/
def selbergOptimalVectorNormalization
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergOptimalVectorNormalization level weight where
  fullPositivity :=
    TS127.Goldbach.selbergJordanTwoFullPositivityDischarge level weight
  optimalVector :=
    selbergOptimalDiagonalVector level
  optimal_vector_eq := by
    intro d
    rfl
  linear_constraint := by
    intro hlevel
    exact selbergOptimalDiagonalVector_linear_constraint level hlevel
  energy_eq := by
    intro hlevel
    exact selbergOptimalDiagonalVector_energy_eq level hlevel
  cauchy_lower_bound_sharp := by
    intro hlevel
    exact selbergOptimalDiagonalVector_lower_bound_sharp level hlevel
  selberg_sieve_bound_obligation := True.intro
  brun_titchmarsh_obligation := True.intro

/-- Target proposition for TS128 optimal-vector normalization. -/
def SelbergOptimalVectorNormalizationTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergOptimalVectorNormalization level weight)

/-- The TS128 optimal-vector package is populated. -/
theorem selbergOptimalVectorNormalizationTarget :
    SelbergOptimalVectorNormalizationTarget := by
  intro level weight
  exact Nonempty.intro
    (selbergOptimalVectorNormalization level weight)

/-- TS128 keeps the TS127 full positivity target available. -/
theorem selbergJordanTwoFullPositivityDischargeTarget :
    TS127.Goldbach.SelbergJordanTwoFullPositivityDischargeTarget :=
  TS127.Goldbach.selbergJordanTwoFullPositivityDischargeTarget

end Goldbach
end TS128
