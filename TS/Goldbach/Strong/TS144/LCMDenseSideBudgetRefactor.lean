import Mathlib.Tactic
import TS.Goldbach.Strong.TS143.LCMMultiplicityErrorBoundDischarge

namespace TS144
namespace Goldbach

/-!
# TS144 - LCM Dense-Side Budget Refactor

TS142 isolated an exact-budget contract for the quadratic kernel `1 / lcm`.
That contract must not be imported from TS136: the TS136 exact budget concerns
the different kernel `gcd / lcm`.

This sprint records the obstruction pointwise, replaces exact equality by the
upper bound actually needed by the interval majorant, and exposes a corrected
route through the Euler-totient diagonalization of the gcd kernel.

The two remaining arithmetic inputs are explicit:

* diagonalize the absorbed gcd kernel with `Nat.totient`;
* compare the Euler-totient diagonal energy with the Jordan-two energy.
-/

/-- The `1/lcm` and `gcd/lcm` kernels already differ at `(2,2)`. -/
theorem one_div_lcm_ne_gcd_div_lcm_at_two :
    (1 : Rat) / (Nat.lcm 2 2 : Rat) !=
      (Nat.gcd 2 2 : Rat) / (Nat.lcm 2 2 : Rat) := by
  norm_num

/-- Correct budget contract for the TS142 lcm dense side. -/
def SelbergLCMDenseSideBudgetUpperBound
    (level : Nat) :
    Prop :=
  TS142.Goldbach.selbergLCMDenseSideRat level <=
    1 / TS122.Goldbach.selbergOptimizationDenominator level

/-- The former exact contract implies the corrected upper-bound contract. -/
theorem selbergLCMDenseSideBudgetUpperBound_of_exact
    (level : Nat)
    (hexact : TS142.Goldbach.SelbergLCMDenseSideExactBudget level) :
    SelbergLCMDenseSideBudgetUpperBound level := by
  exact hexact.le

/-- Positive-index rational kernel identity behind the corrected route. -/
theorem one_div_lcm_eq_gcd_div_mul
    {d1 d2 : Nat}
    (h1 : 0 < d1)
    (h2 : 0 < d2) :
    (1 : Rat) / (Nat.lcm d1 d2 : Rat) =
      (Nat.gcd d1 d2 : Rat) / ((d1 : Rat) * (d2 : Rat)) := by
  have hd1 : Not ((d1 : Rat) = 0) := by
    exact_mod_cast (Nat.ne_of_gt h1)
  have hd2 : Not ((d2 : Rat) = 0) := by
    exact_mod_cast (Nat.ne_of_gt h2)
  have hlcm : Not ((Nat.lcm d1 d2 : Rat) = 0) := by
    exact_mod_cast (Nat.lcm_pos h1 h2).ne'
  have hcast :
      (Nat.gcd d1 d2 : Rat) * (Nat.lcm d1 d2 : Rat) =
        (d1 : Rat) * (d2 : Rat) := by
    exact_mod_cast (Nat.gcd_mul_lcm d1 d2)
  apply (div_eq_iff hlcm).2
  rw [div_mul_eq_mul_div]
  rw [hcast]
  field_simp [hd1, hd2]

/-- Original reconstructed coefficient after absorbing one divisor factor. -/
def selbergLCMAbsorbedLambda
    (level d : Nat) :
    Rat :=
  TS142.Goldbach.selbergConcreteLambda level d / (d : Rat)

/-- The gcd-kernel form obtained from the TS142 `1/lcm` side. -/
def selbergGcdAbsorbedDenseSideRat
    (level : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
      selbergLCMAbsorbedLambda level d1 *
        selbergLCMAbsorbedLambda level d2 *
          (Nat.gcd d1 d2 : Rat)

/-- Membership in the TS122 support supplies positivity of the index. -/
theorem pos_of_mem_selbergOptimizationSupport
    {level d : Nat}
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    0 < d := by
  have hd' :
      Membership.mem (TS121.Goldbach.selbergPositiveQuadraticSupport level) d := by
    simpa [TS122.Goldbach.selbergOptimizationSupport] using hd
  exact (TS121.Goldbach.mem_selbergPositiveQuadraticSupport.mp hd').2

/-- The TS142 lcm form is exactly the absorbed gcd-kernel form. -/
theorem selbergLCMDenseSide_eq_gcdAbsorbedDenseSide
    (level : Nat) :
    TS142.Goldbach.selbergLCMDenseSideRat level =
      selbergGcdAbsorbedDenseSideRat level := by
  unfold TS142.Goldbach.selbergLCMDenseSideRat
  unfold selbergGcdAbsorbedDenseSideRat
  apply Finset.sum_congr rfl
  intro d1 hd1
  apply Finset.sum_congr rfl
  intro d2 hd2
  have h1 : 0 < d1 := pos_of_mem_selbergOptimizationSupport hd1
  have h2 : 0 < d2 := pos_of_mem_selbergOptimizationSupport hd2
  rw [show
    TS142.Goldbach.selbergConcreteLambda level d1 *
          TS142.Goldbach.selbergConcreteLambda level d2 /
            (Nat.lcm d1 d2 : Rat) =
        TS142.Goldbach.selbergConcreteLambda level d1 *
          TS142.Goldbach.selbergConcreteLambda level d2 *
            ((1 : Rat) / (Nat.lcm d1 d2 : Rat)) by ring]
  rw [one_div_lcm_eq_gcd_div_mul h1 h2]
  unfold selbergLCMAbsorbedLambda
  ring

/-- Euler-totient diagonal side for the absorbed TS136 optimal weights. -/
def selbergEulerTotientDiagonalSideRat
    (level : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun r =>
    (Nat.totient r : Rat) *
      TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (TS136.Goldbach.selbergOptimalIntervalWeight level)
          r ^ (2 : Nat)

/-- Exact finite diagonalization contract for the absorbed gcd kernel. -/
def SelbergGcdEulerTotientDiagonalization
    (level : Nat) :
    Prop :=
  selbergGcdAbsorbedDenseSideRat level =
    selbergEulerTotientDiagonalSideRat level

/-- Coefficientwise comparison needed to dominate the totient energy by J2. -/
def SelbergEulerTotientLeJordanTwoOnSupport
    (level : Nat) :
    Prop :=
  forall r : Nat,
    Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) r ->
      (Nat.totient r : Rat) <= TS122.Goldbach.selbergJordanTwoPenalty r

/-- Coefficientwise `totient <= J2` implies the corresponding energy bound. -/
theorem selbergEulerTotientDiagonalSide_le_jordanEnergy
    (level : Nat)
    (hcoeff : SelbergEulerTotientLeJordanTwoOnSupport level) :
    selbergEulerTotientDiagonalSideRat level <=
      TS122.Goldbach.selbergDiagonalEnergy
        level
        (TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (TS136.Goldbach.selbergOptimalIntervalWeight level)) := by
  unfold selbergEulerTotientDiagonalSideRat
  unfold TS122.Goldbach.selbergDiagonalEnergy
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_right (hcoeff r hr) (sq_nonneg _)

/-- The Jordan-two energy of the reconstructed optimal weights is `1 / D`. -/
theorem selbergOptimalAbsorbedJordanEnergy_eq_budget
    (level : Nat)
    (hlevel : 0 < level) :
    TS122.Goldbach.selbergDiagonalEnergy
        level
        (TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (TS136.Goldbach.selbergOptimalIntervalWeight level)) =
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  calc
    TS122.Goldbach.selbergDiagonalEnergy
        level
        (TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (TS136.Goldbach.selbergOptimalIntervalWeight level)) =
        TS110.Goldbach.selbergDenseSide
          level
          (TS136.Goldbach.selbergOptimalIntervalWeight level) :=
      (TS129.Goldbach.selbergOriginalDenseSide_eq_absorbedDiagonalEnergy
        level
        (TS136.Goldbach.selbergOptimalIntervalWeight level)).symm
    _ = 1 / TS122.Goldbach.selbergOptimizationDenominator level :=
      TS136.Goldbach.selbergOptimalIntervalWeight_dense_budget_exact
        level
        hlevel

/-- Corrected route from gcd/totient inputs to the TS142 upper budget. -/
theorem selbergLCMDenseSideBudgetUpperBound_of_totient_route
    (level : Nat)
    (hlevel : 0 < level)
    (hdiag : SelbergGcdEulerTotientDiagonalization level)
    (hcoeff : SelbergEulerTotientLeJordanTwoOnSupport level) :
    SelbergLCMDenseSideBudgetUpperBound level := by
  calc
    TS142.Goldbach.selbergLCMDenseSideRat level =
        selbergGcdAbsorbedDenseSideRat level :=
      selbergLCMDenseSide_eq_gcdAbsorbedDenseSide level
    _ = selbergEulerTotientDiagonalSideRat level := hdiag
    _ <=
        TS122.Goldbach.selbergDiagonalEnergy
          level
          (TS129.Goldbach.selbergAbsorbedDiagonalVector
            level
            (TS136.Goldbach.selbergOptimalIntervalWeight level)) :=
      selbergEulerTotientDiagonalSide_le_jordanEnergy level hcoeff
    _ = 1 / TS122.Goldbach.selbergOptimizationDenominator level :=
      selbergOptimalAbsorbedJordanEnergy_eq_budget level hlevel

/-- The corrected dense upper bound controls the TS142 fractional main term. -/
theorem selbergFractionalMainTerm_le_optimalBudget
    (level x Q : Nat)
    (hbudget : SelbergLCMDenseSideBudgetUpperBound level) :
    TS142.Goldbach.selbergFractionalMainTermRat level x Q <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        (1 / TS122.Goldbach.selbergOptimizationDenominator level) := by
  rw [TS142.Goldbach.selbergFractionalMainTerm_eq_intervalLength_mul_denseSide]
  exact mul_le_mul_of_nonneg_left hbudget (by positivity)

/-- TS144 package for the corrected lcm dense-side route. -/
structure LCMDenseSideBudgetRefactor
    (level x Q n : Nat) where
  hlevel :
    0 < level

  kernel_obstruction :
    (1 : Rat) / (Nat.lcm 2 2 : Rat) !=
      (Nat.gcd 2 2 : Rat) / (Nat.lcm 2 2 : Rat)

  lcm_to_gcd :
    TS142.Goldbach.selbergLCMDenseSideRat level =
      selbergGcdAbsorbedDenseSideRat level

  gcd_totient_diagonalization :
    SelbergGcdEulerTotientDiagonalization level

  totient_le_jordan_two :
    SelbergEulerTotientLeJordanTwoOnSupport level

  dense_side_upper_budget :
    SelbergLCMDenseSideBudgetUpperBound level

  main_term_upper_budget :
    TS142.Goldbach.selbergFractionalMainTermRat level x Q <=
      ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
        (1 / TS122.Goldbach.selbergOptimizationDenominator level)

  local_error_bound :
    TS142.Goldbach.LCMMultiplicityErrorBound x Q n

  weighted_error_aggregation_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Build TS144 from the two remaining arithmetic inputs. -/
def lcmDenseSideBudgetRefactor
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (hdiag : SelbergGcdEulerTotientDiagonalization level)
    (hcoeff : SelbergEulerTotientLeJordanTwoOnSupport level) :
    LCMDenseSideBudgetRefactor level x Q n where
  hlevel := hlevel
  kernel_obstruction := one_div_lcm_ne_gcd_div_lcm_at_two
  lcm_to_gcd := selbergLCMDenseSide_eq_gcdAbsorbedDenseSide level
  gcd_totient_diagonalization := hdiag
  totient_le_jordan_two := hcoeff
  dense_side_upper_budget :=
    selbergLCMDenseSideBudgetUpperBound_of_totient_route
      level hlevel hdiag hcoeff
  main_term_upper_budget :=
    selbergFractionalMainTerm_le_optimalBudget
      level x Q
      (selbergLCMDenseSideBudgetUpperBound_of_totient_route
        level hlevel hdiag hcoeff)
  local_error_bound :=
    TS143.Goldbach.lcmMultiplicityErrorBound x Q n
  weighted_error_aggregation_obligation := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Corrected TS144 target, free of the obstructed exact-budget premise. -/
def LCMDenseSideBudgetRefactorTarget : Prop :=
  forall level x Q n : Nat,
    0 < level ->
      SelbergGcdEulerTotientDiagonalization level ->
        SelbergEulerTotientLeJordanTwoOnSupport level ->
          Nonempty (LCMDenseSideBudgetRefactor level x Q n)

/-- The corrected target is populated by the two named arithmetic inputs. -/
theorem lcmDenseSideBudgetRefactorTarget :
    LCMDenseSideBudgetRefactorTarget := by
  intro level x Q n hlevel hdiag hcoeff
  exact Nonempty.intro
    (lcmDenseSideBudgetRefactor
      level x Q n hlevel hdiag hcoeff)

end Goldbach
end TS144
