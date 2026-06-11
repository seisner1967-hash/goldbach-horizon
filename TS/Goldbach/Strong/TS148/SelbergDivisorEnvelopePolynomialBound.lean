import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import TS.Goldbach.Strong.TS147.SelbergOptimalWeightExplicitFormula

namespace TS148
namespace Goldbach

/-!
# TS148 - Selberg Divisor Envelope Polynomial Bound

TS147 bounds the finite `L1` norm of the reconstructed Selberg weights by a
divisor-first envelope. This sprint gives that envelope a fully explicit,
coarse polynomial bound.

The proof uses only finite arithmetic:

* the positive optimization support is exactly `Icc 1 level`, hence has
  cardinality `level`;
* each supported divisor mass is at most `level^2`;
* the optimal diagonal coordinate has absolute value at most `1 / D`, using
  `|mu| <= 1`, positivity of `D`, and `1 <= J2` on positive integers.

Consequently the TS147 divisor envelope is at most `level^3 / D`. No claim of
optimal growth is made here.
-/

/-- The TS122 positive support is the natural interval from one to `level`. -/
theorem selbergOptimizationSupport_eq_Icc
    (level : Nat) :
    TS122.Goldbach.selbergOptimizationSupport level = Finset.Icc 1 level := by
  apply Finset.ext
  intro d
  simp only [TS122.Goldbach.selbergOptimizationSupport,
    TS121.Goldbach.selbergPositiveQuadraticSupport,
    TS108.Goldbach.selbergQuadraticSupport,
    Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The positive optimization support has exactly `level` elements. -/
theorem card_selbergOptimizationSupport
    (level : Nat) :
    (TS122.Goldbach.selbergOptimizationSupport level).card = level := by
  rw [selbergOptimizationSupport_eq_Icc]
  simp

/-- The Jordan-two penalty is at least one on positive integers. -/
theorem one_le_selbergJordanTwoPenalty
    (d : Nat)
    (hd : 0 < d) :
    (1 : Rat) <= TS122.Goldbach.selbergJordanTwoPenalty d := by
  have htot_pos : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have htot_one : 1 <= Nat.totient d := htot_pos
  have htot_rat : (1 : Rat) <= (Nat.totient d : Rat) := by
    exact_mod_cast htot_one
  exact le_trans htot_rat (TS145.Goldbach.totient_le_jordanTwo d hd)

/-- Every supported divisor-mass term is bounded by `level`. -/
theorem supportedDivisorMass_term_le_level
    (level d m : Nat)
    (hm : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) m) :
    (if Dvd.dvd m d then (m : Rat) else 0) <= (level : Rat) := by
  have hm_le : m <= level :=
    TS130.Goldbach.mem_selbergReconstructionSupport_le_level
      (show Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) m by
        simpa [TS130.Goldbach.selbergReconstructionSupport] using hm)
  by_cases hmd : Dvd.dvd m d
  case pos =>
    simp only [hmd, if_true]
    exact_mod_cast hm_le
  case neg =>
    simp [hmd]

/-- Coarse bound for the supported sum of divisors. -/
theorem selbergSupportedDivisorMass_le_level_sq
    (level d : Nat) :
    TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
      (level : Rat) ^ 2 := by
  unfold TS147.Goldbach.selbergSupportedDivisorMassRat
  calc
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) (fun m =>
        if Dvd.dvd m d then (m : Rat) else 0) <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) (fun _ =>
          (level : Rat)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact supportedDivisorMass_term_le_level level d m hm
    _ =
        ((TS122.Goldbach.selbergOptimizationSupport level).card : Rat) *
          (level : Rat) := by
      simp
    _ = (level : Rat) ^ 2 := by
      rw [card_selbergOptimizationSupport]
      ring

/-- The TS128 optimal diagonal coordinate is bounded by `1 / D`. -/
theorem abs_selbergOptimalDiagonalVector_le_invDenominator
    (level d : Nat)
    (hlevel : 0 < level)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) <=
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  have hdpos : 0 < d := TS144.Goldbach.pos_of_mem_selbergOptimizationSupport hd
  have hDpos :
      0 < TS122.Goldbach.selbergOptimizationDenominator level :=
    TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
  have hJone :
      (1 : Rat) <= TS122.Goldbach.selbergJordanTwoPenalty d :=
    one_le_selbergJordanTwoPenalty d hdpos
  have hJpos : 0 < TS122.Goldbach.selbergJordanTwoPenalty d :=
    lt_of_lt_of_le zero_lt_one hJone
  have hmu := TS147.Goldbach.abs_selbergMobiusRatCoefficient_le_one d
  unfold TS128.Goldbach.selbergOptimalDiagonalVector
  unfold TS128.Goldbach.finiteWeightedCauchyOptimalVector
  rw [TS128.Goldbach.finiteWeightedCauchyDenominator_selberg]
  rw [abs_div, abs_mul, abs_of_pos hDpos, abs_of_pos hJpos]
  have hmuJ :
      abs (TS122.Goldbach.selbergMobiusRatCoefficient d) /
          TS122.Goldbach.selbergJordanTwoPenalty d <= 1 := by
    exact (div_le_one hJpos).2 (le_trans hmu hJone)
  have hdiv := div_le_div_of_nonneg_right hmuJ hDpos.le
  calc
    abs (TS122.Goldbach.selbergMobiusRatCoefficient d) /
          (TS122.Goldbach.selbergOptimizationDenominator level *
            TS122.Goldbach.selbergJordanTwoPenalty d) =
        (abs (TS122.Goldbach.selbergMobiusRatCoefficient d) /
          TS122.Goldbach.selbergJordanTwoPenalty d) /
            TS122.Goldbach.selbergOptimizationDenominator level := by
      ring
    _ <= 1 / TS122.Goldbach.selbergOptimizationDenominator level := hdiv

/-- One divisor-envelope summand is bounded by `level^2 / D`. -/
theorem divisorEnvelope_term_le
    (level d : Nat)
    (hlevel : 0 < level)
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) *
        TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
      (1 / TS122.Goldbach.selbergOptimizationDenominator level) *
        (level : Rat) ^ 2 := by
  have hY := abs_selbergOptimalDiagonalVector_le_invDenominator level d hlevel hd
  have hmass := selbergSupportedDivisorMass_le_level_sq level d
  have hmass_nonneg :
      0 <= TS147.Goldbach.selbergSupportedDivisorMassRat level d := by
    unfold TS147.Goldbach.selbergSupportedDivisorMassRat
    positivity
  have hinv_nonneg :
      0 <= 1 / TS122.Goldbach.selbergOptimizationDenominator level := by
    have hDpos := TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
    exact (one_div_pos.mpr hDpos).le
  exact mul_le_mul hY hmass hmass_nonneg hinv_nonneg

/-- The TS147 divisor envelope has the explicit coarse bound `level^3 / D`. -/
theorem selbergOptimalWeightDivisorEnvelope_le_level_cube_div_denominator
    (level : Nat)
    (hlevel : 0 < level) :
    TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level <=
      (level : Rat) ^ 3 /
        TS122.Goldbach.selbergOptimizationDenominator level := by
  unfold TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat
  calc
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) (fun d =>
        abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) *
          TS147.Goldbach.selbergSupportedDivisorMassRat level d) <=
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) (fun _ =>
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) *
            (level : Rat) ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact divisorEnvelope_term_le level d hlevel hd
    _ =
        ((TS122.Goldbach.selbergOptimizationSupport level).card : Rat) *
          ((1 / TS122.Goldbach.selbergOptimizationDenominator level) *
            (level : Rat) ^ 2) := by
      simp
    _ =
        (level : Rat) ^ 3 /
          TS122.Goldbach.selbergOptimizationDenominator level := by
      rw [card_selbergOptimizationSupport]
      ring

/-- Effective coarse bound for the TS146 `L1` norm. -/
theorem selbergConcreteLambdaL1_le_level_cube_div_denominator
    (level : Nat)
    (hlevel : 0 < level) :
    TS146.Goldbach.selbergConcreteLambdaL1Rat level <=
      (level : Rat) ^ 3 /
        TS122.Goldbach.selbergOptimizationDenominator level := by
  exact le_trans
    (TS147.Goldbach.selbergConcreteLambdaL1_le_divisorEnvelope level)
    (selbergOptimalWeightDivisorEnvelope_le_level_cube_div_denominator
      level hlevel)

/--
The interval square majorant now has a fully explicit polynomial error term.
-/
theorem selbergConcreteSquareMajorantRat_le_explicitPolynomialBudget
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        ((level : Rat) ^ 3 /
          TS122.Goldbach.selbergOptimizationDenominator level) ^ 2 := by
  have hEnvelope :=
    selbergOptimalWeightDivisorEnvelope_le_level_cube_div_denominator
      level hlevel
  have hEnvelope_nonneg :
      0 <= TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level := by
    rw [<- TS147.Goldbach.selbergOptimalWeightL1Envelope_eq_divisorEnvelope]
    unfold TS147.Goldbach.selbergOptimalWeightL1EnvelopeRat
    unfold TS147.Goldbach.selbergOptimalWeightDiagonalEnvelopeRat
    positivity
  have hBudget_nonneg :
      0 <=
        (level : Rat) ^ 3 /
          TS122.Goldbach.selbergOptimizationDenominator level := by
    have hDpos := TS127.Goldbach.selbergOptimizationDenominator_pos level hlevel
    exact div_nonneg (by positivity) hDpos.le
  have hsq :
      (TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level) ^ 2 <=
        ((level : Rat) ^ 3 /
          TS122.Goldbach.selbergOptimizationDenominator level) ^ 2 := by
    nlinarith
  exact le_trans
    (TS147.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_divisorEnvelope_sq
      level x Q n hlevel)
    (add_le_add_left hsq _)

/-- TS148 package for the first effective polynomial envelope. -/
structure SelbergDivisorEnvelopePolynomialBound
    (level x Q n : Nat) where
  hlevel :
    0 < level

  support_card :
    (TS122.Goldbach.selbergOptimizationSupport level).card = level

  divisor_mass_bound :
    forall d : Nat,
      TS147.Goldbach.selbergSupportedDivisorMassRat level d <=
        (level : Rat) ^ 2

  diagonal_coordinate_bound :
    forall d : Nat,
      Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d ->
        abs (TS128.Goldbach.selbergOptimalDiagonalVector level d) <=
          1 / TS122.Goldbach.selbergOptimizationDenominator level

  divisor_envelope_bound :
    TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat level <=
      (level : Rat) ^ 3 /
        TS122.Goldbach.selbergOptimizationDenominator level

  square_majorant_upper_budget :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
          (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
        ((level : Rat) ^ 3 /
          TS122.Goldbach.selbergOptimizationDenominator level) ^ 2

  polynomial_refinement_obligation :
    True

  denominator_estimate_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Construct the unconditional finite TS148 package. -/
def selbergDivisorEnvelopePolynomialBound
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    SelbergDivisorEnvelopePolynomialBound level x Q n where
  hlevel := hlevel
  support_card := card_selbergOptimizationSupport level
  divisor_mass_bound := by
    intro d
    exact selbergSupportedDivisorMass_le_level_sq level d
  diagonal_coordinate_bound := by
    intro d hd
    exact abs_selbergOptimalDiagonalVector_le_invDenominator
      level d hlevel hd
  divisor_envelope_bound :=
    selbergOptimalWeightDivisorEnvelope_le_level_cube_div_denominator
      level hlevel
  square_majorant_upper_budget :=
    selbergConcreteSquareMajorantRat_le_explicitPolynomialBudget
      level x Q n hlevel
  polynomial_refinement_obligation := True.intro
  denominator_estimate_obligation := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Target proposition for the unconditional TS148 polynomial bound. -/
def SelbergDivisorEnvelopePolynomialBoundTarget : Prop :=
  forall level x Q n : Nat,
    0 < level ->
      Nonempty (SelbergDivisorEnvelopePolynomialBound level x Q n)

/-- The TS148 target is populated for every positive level. -/
theorem selbergDivisorEnvelopePolynomialBoundTarget :
    SelbergDivisorEnvelopePolynomialBoundTarget := by
  intro level x Q n hlevel
  exact Nonempty.intro
    (selbergDivisorEnvelopePolynomialBound level x Q n hlevel)

end Goldbach
end TS148
