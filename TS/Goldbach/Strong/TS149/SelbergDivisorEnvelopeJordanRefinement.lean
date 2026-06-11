import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic
import TS.Goldbach.Strong.TS148.SelbergDivisorEnvelopePolynomialBound

namespace TS149
namespace Goldbach

open ArithmeticFunction

/-!
# TS149 - Selberg Divisor Envelope Jordan Refinement

TS148 gives the coarse finite estimate `divisorEnvelope <= level^3 / D`.
This sprint uses the arithmetic structure hidden in the divisor mass to improve
that estimate to `level / D`.

The main input is the global domination

`sigma_1(n) <= J2(n)` for every positive integer `n`.

It is proved first on prime powers and then transported through
`Nat.factorization`.  On the positive optimization support, the supported
divisor mass is exactly `sigma_1(d)`.  The `J2(d)` factor therefore cancels the
same penalty in the explicit TS128 coordinate bound, leaving at most `1 / D`
per support element.  Since the support has cardinality `level`, the resulting
envelope is at most `level / D`.
-/

/-- A geometric sum at a prime is bounded by the next power. -/
theorem prime_geometric_sum_le_pow
    {p : Nat}
    (hp : p.Prime)
    (k : Nat) :
    (Finset.sum (Finset.range (k + 1)) fun i => (p : Rat) ^ i) <=
      (p : Rat) ^ (k + 1) := by
  induction k with
  | zero =>
      simp
      exact_mod_cast hp.one_lt.le
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      have hp_two : (2 : Rat) <= (p : Rat) := by
        exact_mod_cast hp.two_le
      have hpow_nonneg : 0 <= (p : Rat) ^ (k + 1) := by positivity
      calc
        (Finset.sum (Finset.range (k + 1)) fun i => (p : Rat) ^ i) +
              (p : Rat) ^ (k + 1) <=
            (p : Rat) ^ (k + 1) + (p : Rat) ^ (k + 1) :=
          add_le_add_right ih _
        _ <= (p : Rat) ^ (k + 1) * (p : Rat) := by
          nlinarith
        _ = (p : Rat) ^ ((k + 1) + 1) := by
          exact (pow_succ (p : Rat) (k + 1)).symm

theorem sigmaOne_prime_pow_le_jordanTwo
    {p k : Nat}
    (hp : p.Prime)
    (hk : 0 < k) :
    (ArithmeticFunction.sigma 1 (p ^ k) : Rat) <=
      TS119.Goldbach.selbergJordanTwoCoefficient (p ^ k) := by
  cases k with
  | zero => exact False.elim (Nat.lt_irrefl 0 hk)
  | succ k =>
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
      push_cast
      rw [TS125.Goldbach.selbergJordanTwoCoefficient_prime_pow_succ hp]
      cases k with
      | zero =>
          simp
          have hp_two : (2 : Rat) <= (p : Rat) := by
            exact_mod_cast hp.two_le
          nlinarith
      | succ j =>
          have hsum := prime_geometric_sum_le_pow hp (j + 2)
          have hp_one : (1 : Rat) <= (p : Rat) := by
            exact_mod_cast hp.one_lt.le
          have hpow :
              (p : Rat) ^ (j + 2) <= (p : Rat) ^ (2 * (j + 1)) := by
            exact pow_le_pow_right hp_one (by omega)
          have hfactor :
              (p : Rat) ^ (2 * ((j + 1) + 1)) -
                  (p : Rat) ^ (2 * (j + 1)) =
                (p : Rat) ^ (2 * (j + 1)) * ((p : Rat) ^ 2 - 1) := by
            rw [show 2 * ((j + 1) + 1) = 2 * (j + 1) + 2 by omega]
            rw [pow_add]
            ring
          have hp_factor : (p : Rat) <= (p : Rat) ^ 2 - 1 := by
            have hp_two : (2 : Rat) <= (p : Rat) := by
              exact_mod_cast hp.two_le
            nlinarith
          have hnonneg : 0 <= (p : Rat) ^ (j + 2) := by positivity
          calc
            (Finset.sum (Finset.range (j + 1 + 1 + 1)) fun i =>
                (p : Rat) ^ i) <= (p : Rat) ^ (j + 2 + 1) := by
              simpa [Nat.add_assoc] using hsum
            _ = (p : Rat) ^ (j + 2) * (p : Rat) := by
              rw [pow_succ]
            _ <= (p : Rat) ^ (2 * (j + 1)) * ((p : Rat) ^ 2 - 1) := by
              exact mul_le_mul hpow hp_factor (by positivity) (by positivity)
            _ =
                (p : Rat) ^ (2 * ((j + 1) + 1)) -
                  (p : Rat) ^ (2 * (j + 1)) := hfactor.symm

theorem sigmaOne_le_jordanTwo
    (n : Nat)
    (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : Rat) <=
      TS119.Goldbach.selbergJordanTwoCoefficient n := by
  have hn0 : Not (n = 0) := Nat.ne_of_gt hn
  have hsigmaNat :
      ArithmeticFunction.sigma 1 n =
        n.factorization.prod fun p k => ArithmeticFunction.sigma 1 (p ^ k) := by
    exact ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization
      (ArithmeticFunction.sigma 1) hn0
  rw [hsigmaNat]
  rw [TS126.Goldbach.selbergJordanTwoCoefficient_factorization hn0]
  rw [Finsupp.prod, Finsupp.prod]
  push_cast
  refine Finset.prod_le_prod (fun p _hp => by positivity) ?_
  intro p hp_mem
  have hp_prime : p.Prime := by
    simpa [Nat.support_factorization] using
      Nat.prime_of_mem_primeFactors hp_mem
  have hk_pos : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
  exact sigmaOne_prime_pow_le_jordanTwo hp_prime hk_pos

theorem optimizationSupport_filter_dvd_eq_divisors
    (level d : Nat)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    (TS122.Goldbach.selbergOptimizationSupport level).filter
        (fun m => Dvd.dvd m d) = d.divisors := by
  simpa using
    TS145.Goldbach.optimizationSupport_filter_dvd_gcd_eq_divisors
      level d d hd

theorem selbergSupportedDivisorMass_eq_sigmaOne
    (level d : Nat)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    TS147.Goldbach.selbergSupportedDivisorMassRat level d =
      (ArithmeticFunction.sigma 1 d : Rat) := by
  unfold TS147.Goldbach.selbergSupportedDivisorMassRat
  rw [<- Finset.sum_filter]
  rw [optimizationSupport_filter_dvd_eq_divisors level d hd]
  rw [ArithmeticFunction.sigma_one_apply]
  push_cast
  rfl

theorem selbergSupportedDivisorMass_le_jordanTwo
    (level d : Nat)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
      TS122.Goldbach.selbergJordanTwoPenalty d := by
  rw [selbergSupportedDivisorMass_eq_sigmaOne level d hd]
  exact sigmaOne_le_jordanTwo d
    (TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hd)

theorem abs_selbergOptimalDiagonalVector_le_inv_den_mul_jordanTwo
    (level d : Nat)
    (hlevel : 0 < level)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) <=
      1 / (TS122.Goldbach.selbergOptimizationDenominator level *
        TS122.Goldbach.selbergJordanTwoPenalty d) := by
  have hDpos := TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hJpos := TS127.Goldbach.selbergJordanTwoPositiveOnSupport level d hd
  have hmu := TS147.Goldbach.abs_selbergMobiusRatCoefficient_le_one d
  unfold TS128.Goldbach.selbergOptimalDiagonalVector
  unfold TS128.Goldbach.finiteWeightedCauchyOptimalVector
  rw [TS128.Goldbach.finiteWeightedCauchyDenominator_selberg]
  rw [abs_div, abs_mul, abs_of_pos hDpos, abs_of_pos hJpos]
  exact div_le_div_of_nonneg_right hmu (mul_pos hDpos hJpos).le

theorem divisorEnvelope_term_le_invDenominator
    (level d : Nat)
    (hlevel : 0 < level)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) *
        TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  have hY :=
    abs_selbergOptimalDiagonalVector_le_inv_den_mul_jordanTwo
      level d hlevel hd
  have hmass := selbergSupportedDivisorMass_le_jordanTwo level d hd
  have hmass_nonneg :
      0 <= TS147.Goldbach.selbergSupportedDivisorMassRat level d := by
    unfold TS147.Goldbach.selbergSupportedDivisorMassRat
    positivity
  have hDpos := TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hJpos := TS127.Goldbach.selbergJordanTwoPositiveOnSupport level d hd
  have hinv_nonneg :
      0 <= 1 / (TS122.Goldbach.selbergOptimizationDenominator level *
        TS122.Goldbach.selbergJordanTwoPenalty d) := by
    exact (one_div_pos.mpr (mul_pos hDpos hJpos)).le
  calc
    abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) *
          TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
        (1 / (TS122.Goldbach.selbergOptimizationDenominator level *
          TS122.Goldbach.selbergJordanTwoPenalty d)) *
            TS122.Goldbach.selbergJordanTwoPenalty d := by
      exact mul_le_mul hY hmass hmass_nonneg hinv_nonneg
    _ = 1 / TS122.Goldbach.selbergOptimizationDenominator level := by
      field_simp [hDpos.ne', hJpos.ne']
      ring

/-- The TS147 divisor envelope improves from `level^3 / D` to `level / D`. -/
theorem selbergOptimalWeightDivisorEnvelope_le_level_div_denominator
    (level : Nat)
    (hlevel : 0 < level) :
    TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level <=
      (level : Rat) /
        TS122.Goldbach.selbergOptimizationDenominator level := by
  unfold TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat
  calc
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) (fun d =>
        abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) *
          TS147.Goldbach.selbergSupportedDivisorMassRat level d) <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) (fun _ =>
          1 / TS122.Goldbach.selbergOptimizationDenominator level) := by
      apply Finset.sum_le_sum
      intro d hd
      exact divisorEnvelope_term_le_invDenominator level d hlevel hd
    _ =
        ((TS122.Goldbach.selbergOptimizationSupport level).card : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) := by
      simp
    _ =
        (level : Rat) /
          TS122.Goldbach.selbergOptimizationDenominator level := by
      rw [TS148.Goldbach.card_selbergOptimizationSupport]
      ring

/-- Refined effective bound for the TS146 finite `L1` norm. -/
theorem selbergConcreteLambdaL1_le_level_div_denominator
    (level : Nat)
    (hlevel : 0 < level) :
    TS146.Goldbach.selbergConcreteLambdaL1Rat level <=
      (level : Rat) /
        TS122.Goldbach.selbergOptimizationDenominator level := by
  exact le_trans
    (TS147.Goldbach.selbergConcreteLambdaL1_le_divisorEnvelope level)
    (selbergOptimalWeightDivisorEnvelope_le_level_div_denominator
      level hlevel)

/--
The interval square majorant now has the refined quadratic error budget.
-/
theorem selbergConcreteSquareMajorantRat_le_refinedBudget
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        ((level : Rat) /
          TS122.Goldbach.selbergOptimizationDenominator level) ^ 2 := by
  have hEnvelope :=
    selbergOptimalWeightDivisorEnvelope_le_level_div_denominator
      level hlevel
  have hEnvelope_nonneg :
      0 <= TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level := by
    rw [<- TS147.Goldbach.selbergOptimalWeightL1Envelope_eq_divisorEnvelope]
    unfold TS147.Goldbach.selbergOptimalWeightL1EnvelopeRat
    unfold TS147.Goldbach.selbergOptimalWeightDiagonalEnvelopeRat
    positivity
  have hDpos := TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hBudget_nonneg :
      0 <=
        (level : Rat) /
          TS122.Goldbach.selbergOptimizationDenominator level := by
    exact div_nonneg (by positivity) hDpos.le
  have hsq :
      (TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level) ^ 2 <=
        ((level : Rat) /
          TS122.Goldbach.selbergOptimizationDenominator level) ^ 2 := by
    nlinarith
  exact le_trans
    (TS147.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_divisorEnvelope_sq
      level x Q n hlevel)
    (add_le_add_left hsq _)

/-- TS149 package for the Jordan-refined divisor envelope. -/
structure SelbergDivisorEnvelopeJordanRefinement
    (level x Q n : Nat) where
  hlevel :
    0 < level

  sigma_one_le_jordan_two :
    forall d : Nat,
      0 < d ->
        (ArithmeticFunction.sigma 1 d : Rat) <=
          TS119.Goldbach.selbergJordanTwoCoefficient d

  supported_divisor_mass_eq_sigma_one :
    forall d : Nat,
      Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d ->
        TS147.Goldbach.selbergSupportedDivisorMassRat level d =
          (ArithmeticFunction.sigma 1 d : Rat)

  supported_divisor_mass_le_jordan_two :
    forall d : Nat,
      Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d ->
        TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
          TS122.Goldbach.selbergJordanTwoPenalty d

  divisor_envelope_bound :
    TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level <=
      (level : Rat) /
        TS122.Goldbach.selbergOptimizationDenominator level

  lambda_l1_bound :
    TS146.Goldbach.selbergConcreteLambdaL1Rat level <=
      (level : Rat) /
        TS122.Goldbach.selbergOptimizationDenominator level

  square_majorant_upper_budget :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        ((level : Rat) /
          TS122.Goldbach.selbergOptimizationDenominator level) ^ 2

  sharper_divisor_ratio_obligation :
    True

  level_selection_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Construct the unconditional finite TS149 refinement package. -/
def selbergDivisorEnvelopeJordanRefinement
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    SelbergDivisorEnvelopeJordanRefinement level x Q n where
  hlevel := hlevel
  sigma_one_le_jordan_two := sigmaOne_le_jordanTwo
  supported_divisor_mass_eq_sigma_one := by
    intro d hd
    exact selbergSupportedDivisorMass_eq_sigmaOne level d hd
  supported_divisor_mass_le_jordan_two := by
    intro d hd
    exact selbergSupportedDivisorMass_le_jordanTwo level d hd
  divisor_envelope_bound :=
    selbergOptimalWeightDivisorEnvelope_le_level_div_denominator
      level hlevel
  lambda_l1_bound :=
    selbergConcreteLambdaL1_le_level_div_denominator level hlevel
  square_majorant_upper_budget :=
    selbergConcreteSquareMajorantRat_le_refinedBudget
      level x Q n hlevel
  sharper_divisor_ratio_obligation := True.intro
  level_selection_obligation := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Target proposition for the unconditional TS149 refinement. -/
def SelbergDivisorEnvelopeJordanRefinementTarget : Prop :=
  forall level x Q n : Nat,
    0 < level ->
      Nonempty (SelbergDivisorEnvelopeJordanRefinement level x Q n)

/-- The TS149 target is populated for every positive level. -/
theorem selbergDivisorEnvelopeJordanRefinementTarget :
    SelbergDivisorEnvelopeJordanRefinementTarget := by
  intro level x Q n hlevel
  exact Nonempty.intro
    (selbergDivisorEnvelopeJordanRefinement level x Q n hlevel)

end Goldbach
end TS149
