import Mathlib.Tactic
import TS.Goldbach.Strong.TS141.ConcreteSelbergSquareMajorantExpansion

namespace TS142
namespace Goldbach

/-!
# TS142 - LCM Multiplicity Fractional Decomposition

TS141 rewrites the concrete Selberg square majorant as a pair-first sum whose
geometric input is the number of interval points divisible by
`lcm(d1,d2)`.

This sprint performs the next exact algebraic step.  It decomposes each
multiplicity into the rational interval-length main term plus a remainder,
and inserts that decomposition into the full TS141 double sum.

The genuine estimates remain explicit inputs:

* the remainder has absolute value at most one;
* the lcm main-term quadratic form equals the optimized budget `1 / D`.

No asymptotic estimate or Brun-Titchmarsh comparison is claimed here.
-/

/-- Cartesian support for pairs of TS122 optimization indices. -/
def selbergLCMPairSupport
    (level : Nat) :
    Finset (Prod Nat Nat) :=
  (TS122.Goldbach.selbergOptimizationSupport level).product
    (TS122.Goldbach.selbergOptimizationSupport level)

/-- The reconstructed optimal Selberg coefficient used in TS138--TS141. -/
def selbergConcreteLambda
    (level d : Nat) :
    Rat :=
  TS136.Goldbach.selbergOptimalIntervalWeight level d

/-- The TS141 interval multiple count, exposed under the TS142 name. -/
def lcmMultiplicity
    (x Q n d1 d2 : Nat) :
    Nat :=
  TS141.Goldbach.selbergConcreteLcmMultiplicity x Q n d1 d2

/-- Rational interval-length main term for one positive lcm modulus. -/
def lcmMultiplicityMainRat
    (x Q d1 d2 : Nat) :
    Rat :=
  ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) /
    (Nat.lcm d1 d2 : Rat)

/-- Exact remainder after subtracting the rational main term. -/
def lcmMultiplicityErrorRat
    (x Q n d1 d2 : Nat) :
    Rat :=
  (lcmMultiplicity x Q n d1 d2 : Rat) -
    lcmMultiplicityMainRat x Q d1 d2

/-- TS142 uses exactly the lcm multiplicity introduced in TS141. -/
theorem lcmMultiplicity_eq_TS141
    (x Q n d1 d2 : Nat) :
    lcmMultiplicity x Q n d1 d2 =
      TS141.Goldbach.selbergConcreteLcmMultiplicity x Q n d1 d2 := by
  rfl

/-- Exact pointwise main-term plus remainder decomposition. -/
theorem lcmMultiplicity_eq_main_add_error
    (x Q n d1 d2 : Nat) :
    (lcmMultiplicity x Q n d1 d2 : Rat) =
      lcmMultiplicityMainRat x Q d1 d2 +
        lcmMultiplicityErrorRat x Q n d1 d2 := by
  unfold lcmMultiplicityErrorRat
  ring

/--
The next interval-counting input: a positive modulus has discrepancy at most
one from the rational interval-length main term.
-/
def LCMMultiplicityErrorBound
    (x Q n : Nat) :
    Prop :=
  forall d1 d2 : Nat,
    0 < Nat.lcm d1 d2 ->
      abs (lcmMultiplicityErrorRat x Q n d1 d2) <= 1

/-- The lcm main-term quadratic form in the reconstructed weights. -/
def selbergLCMDenseSideRat
    (level : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
      selbergConcreteLambda level d1 *
        selbergConcreteLambda level d2 /
          (Nat.lcm d1 d2 : Rat)

/--
The exact main-term identification still required after TS136.

This is intentionally separate from the TS136 `gcd/lcm` dense budget: the
present quadratic form has kernel `1/lcm`, so identifying it with `1 / D`
requires its own proof.
-/
def SelbergLCMDenseSideExactBudget
    (level : Nat) :
    Prop :=
  selbergLCMDenseSideRat level =
    1 / TS122.Goldbach.selbergOptimizationDenominator level

/-- Main part of the TS141 lcm expansion after pointwise decomposition. -/
def selbergFractionalMainTermRat
    (level x Q : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
      selbergConcreteLambda level d1 *
        selbergConcreteLambda level d2 *
          lcmMultiplicityMainRat x Q d1 d2

/-- Error part of the TS141 lcm expansion after pointwise decomposition. -/
def selbergFractionalErrorTermRat
    (level x Q n : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
      selbergConcreteLambda level d1 *
        selbergConcreteLambda level d2 *
          lcmMultiplicityErrorRat x Q n d1 d2

/-- The complete main-term plus error expression. -/
def selbergFractionalExpansionRat
    (level x Q n : Nat) :
    Rat :=
  selbergFractionalMainTermRat level x Q +
    selbergFractionalErrorTermRat level x Q n

/-- Insert the pointwise decomposition into the exact TS141 double sum. -/
theorem selbergConcreteSquareMajorantRat_eq_fractionalExpansion
    (level x Q n : Nat) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n =
      selbergFractionalExpansionRat level x Q n := by
  rw [TS141.Goldbach.selbergConcreteSquareMajorantRat_expand_lcm]
  unfold TS141.Goldbach.selbergConcreteLcmExpandedMajorantRat
  unfold selbergFractionalExpansionRat
  unfold selbergFractionalMainTermRat
  unfold selbergFractionalErrorTermRat
  unfold selbergConcreteLambda
  simp_rw [<- lcmMultiplicity_eq_TS141]
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d1 _hd1
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d2 _hd2
  rw [lcmMultiplicity_eq_main_add_error]
  ring

/-- The main part factors as interval length times the lcm dense side. -/
theorem selbergFractionalMainTerm_eq_intervalLength_mul_denseSide
    (level x Q : Nat) :
    selbergFractionalMainTermRat level x Q =
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        selbergLCMDenseSideRat level := by
  unfold selbergFractionalMainTermRat
  unfold selbergLCMDenseSideRat
  unfold lcmMultiplicityMainRat
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d1 _hd1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d2 _hd2
  ring

/-- A supplied lcm budget turns the main term into the optimized `1 / D`. -/
theorem selbergFractionalMainTerm_eq_optimalBudget
    (level x Q : Nat)
    (hdense : SelbergLCMDenseSideExactBudget level) :
    selbergFractionalMainTermRat level x Q =
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        (1 / TS122.Goldbach.selbergOptimizationDenominator level) := by
  rw [selbergFractionalMainTerm_eq_intervalLength_mul_denseSide]
  rw [hdense]

/--
TS142 ledger: exact fractional decomposition plus the two remaining analytic
inputs needed to convert it into a Brun-Titchmarsh budget.
-/
structure LCMMultiplicityFractionalDecomposition
    (level x Q n : Nat) where
  hlevel :
    0 < level

  pointwise_decomposition :
    forall d1 d2 : Nat,
      (lcmMultiplicity x Q n d1 d2 : Rat) =
        lcmMultiplicityMainRat x Q d1 d2 +
          lcmMultiplicityErrorRat x Q n d1 d2

  square_majorant_expansion :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n =
      selbergFractionalExpansionRat level x Q n

  error_bound :
    LCMMultiplicityErrorBound x Q n

  dense_side_budget :
    SelbergLCMDenseSideExactBudget level

  main_term_budget :
    selbergFractionalMainTermRat level x Q =
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        (1 / TS122.Goldbach.selbergOptimizationDenominator level)

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Construct the TS142 ledger from the two remaining genuine estimates. -/
def lcmMultiplicityFractionalDecomposition
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (herror : LCMMultiplicityErrorBound x Q n)
    (hdense : SelbergLCMDenseSideExactBudget level) :
    LCMMultiplicityFractionalDecomposition level x Q n where
  hlevel := hlevel
  pointwise_decomposition := by
    intro d1 d2
    exact lcmMultiplicity_eq_main_add_error x Q n d1 d2
  square_majorant_expansion :=
    selbergConcreteSquareMajorantRat_eq_fractionalExpansion level x Q n
  error_bound := herror
  dense_side_budget := hdense
  main_term_budget :=
    selbergFractionalMainTerm_eq_optimalBudget level x Q hdense
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Bridge target for the exact TS142 decomposition. -/
def LCMMultiplicityFractionalDecompositionTarget : Prop :=
  forall level x Q n : Nat,
    0 < level ->
      LCMMultiplicityErrorBound x Q n ->
        SelbergLCMDenseSideExactBudget level ->
          Nonempty
            (LCMMultiplicityFractionalDecomposition level x Q n)

/-- The TS142 target is populated once its two named estimates are supplied. -/
theorem lcmMultiplicityFractionalDecompositionTarget :
    LCMMultiplicityFractionalDecompositionTarget := by
  intro level x Q n hlevel herror hdense
  exact
    Nonempty.intro
      (lcmMultiplicityFractionalDecomposition
        level x Q n hlevel herror hdense)

/-- TS142 keeps the exact TS141 expansion available. -/
theorem concreteSelbergSquareMajorantExpansionBridgeTarget :
    TS141.Goldbach.ConcreteSelbergSquareMajorantExpansionBridgeTarget :=
  TS141.Goldbach.concreteSelbergSquareMajorantExpansionBridgeTarget

end Goldbach
end TS142
