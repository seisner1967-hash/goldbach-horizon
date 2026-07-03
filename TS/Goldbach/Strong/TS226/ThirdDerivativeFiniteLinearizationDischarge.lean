import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS225.ThirdDerivativeCutoffValueReduction

namespace TS226
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS226 - Third-Derivative Finite Linearization Discharge

TS225 reduced the TS219 third-derivative cutoff value to Dirichlet product
cutoffs at frequencies `1` and `2`, but it deliberately left one compact
algebra statement open: the finite interval integral of the third-derivative
kernel is the same linear combination of the two finite Dirichlet integrals.

This sprint proves that finite linearization.  It does not prove the
Dirichlet cutoff values themselves, the cos-square value, the canonical
`sinc^4` value, Plancherel evidence, or Goldbach.
-/

private theorem sineDirichletKernel_intervalIntegrable_of_pos_left
    (a eps T : Real)
    (heps : 0 < eps)
    (hT : eps < T) :
    IntervalIntegrable
      (fun x : Real => TS213.Goldbach.sineDirichletKernel a x)
      volume
      eps
      T := by
  have hcont :
      ContinuousOn
        (fun x : Real => TS213.Goldbach.sineDirichletKernel a x)
        (Set.uIcc eps T) := by
    intro x hx
    have hx_left : eps <= x := by
      rcases Set.mem_uIcc.1 hx with h | h
      next =>
        exact h.1
      next =>
        have : False := by
          linarith
        exact False.elim this
    have hx0 : Ne x 0 := by
      linarith
    unfold TS213.Goldbach.sineDirichletKernel
    exact
      ((by fun_prop :
        Continuous
          (fun y : Real => Real.sin (a * y))).continuousWithinAt).div
        ((by fun_prop :
          Continuous
            (fun y : Real => y)).continuousWithinAt)
        hx0
  exact hcont.intervalIntegrable

private theorem thirdDerivativeKernel_intervalIntegrable_of_pos_left
    (eps T : Real)
    (heps : 0 < eps)
    (hT : eps < T) :
    IntervalIntegrable
      (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
      volume
      eps
      T := by
  have hcont :
      ContinuousOn
        (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
        (Set.uIcc eps T) := by
    intro x hx
    have hx_left : eps <= x := by
      rcases Set.mem_uIcc.1 hx with h | h
      next =>
        exact h.1
      next =>
        have : False := by
          linarith
        exact False.elim this
    have hx0 : Ne x 0 := by
      linarith
    unfold TS213.Goldbach.cosSquareThirdDerivativeKernel
    exact
      ((by fun_prop :
        Continuous
          (fun y : Real =>
            -2 * Real.sin y + 4 * Real.sin (2 * y))).continuousWithinAt).div
        ((by fun_prop :
          Continuous
            (fun y : Real => y)).continuousWithinAt)
        hx0
  exact hcont.intervalIntegrable

private theorem thirdDerivativeFiniteLinearization_on_pos_left
    (eps T : Real)
    (heps : 0 < eps)
    (hT : eps < T) :
    intervalIntegral
        (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
        eps
        T
        volume =
      (-2 : Real) *
          intervalIntegral
            (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
            eps
            T
            volume +
        4 *
          intervalIntegral
            (fun x : Real => TS213.Goldbach.sineDirichletKernel 2 x)
            eps
            T
            volume := by
  have h1 :=
    sineDirichletKernel_intervalIntegrable_of_pos_left 1 eps T heps hT
  have h2 :=
    sineDirichletKernel_intervalIntegrable_of_pos_left 2 eps T heps hT
  have hleft :
      intervalIntegral
          (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
          eps
          T
          volume =
        intervalIntegral
          (fun x : Real =>
            (-2 : Real) * TS213.Goldbach.sineDirichletKernel 1 x +
              4 * TS213.Goldbach.sineDirichletKernel 2 x)
          eps
          T
          volume := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact TS225.Goldbach.cosSquareThirdDerivativeKernel_eq_dirichletCombination x
  rw [hleft]
  rw [intervalIntegral.integral_add (h1.const_mul _) (h2.const_mul _)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const_mul]

theorem thirdDerivativeCutoffLinearization :
    TS225.Goldbach.ThirdDerivativeCutoffLinearizationStatement := by
  unfold TS225.Goldbach.ThirdDerivativeCutoffLinearizationStatement
  unfold TS219.Goldbach.cosSquareCutoffFilter
  have hsmall :
      Filter.Eventually
        (fun eps : Real => eps < 1)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    have hsmall_nhds :
        Filter.Eventually
          (fun eps : Real => eps < 1)
          (nhds (0 : Real)) :=
      Iio_mem_nhds (show (0 : Real) < 1 by norm_num)
    exact hsmall_nhds.filter_mono nhdsWithin_le_nhds
  have hpos :
      Filter.Eventually
        (fun eps : Real => 0 < eps)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact heps
  have hfirst :
      Filter.Eventually
        (fun eps : Real => 0 < eps /\ eps < 1)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    exact hpos.and hsmall
  filter_upwards [Filter.prod_mem_prod hfirst
    (eventually_gt_atTop (1 : Real))] with p hp
  cases hp with
  | intro hp_first hT_gt_one =>
  cases hp_first with
  | intro heps heps_lt_one =>
  change 1 < p.2 at hT_gt_one
  have h_eps_T : p.1 < p.2 := by
    linarith
  unfold TS225.Goldbach.thirdDerivativeDirichletCombination
  unfold TS225.Goldbach.dirichletProductCutoffIntegral
  exact thirdDerivativeFiniteLinearization_on_pos_left p.1 p.2 heps h_eps_T

/-- Ledger recording the TS226 finite linearization discharge. -/
structure ThirdDerivativeFiniteLinearizationDischargeLedger where
  ts225_cutoff_reduction :
    TS225.Goldbach.ThirdDerivativeCutoffValueReductionLedger

  finite_linearization :
    TS225.Goldbach.ThirdDerivativeCutoffLinearizationStatement

  finite_linearization_on_positive_cutoffs :
    forall eps T : Real,
      0 < eps ->
        eps < T ->
        intervalIntegral
          (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
          eps
          T
          volume =
        (-2 : Real) *
            intervalIntegral
              (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
              eps
              T
              volume +
          4 *
            intervalIntegral
              (fun x : Real => TS213.Goldbach.sineDirichletKernel 2 x)
              eps
              T
              volume

  dirichlet_product_cutoffs_not_proved :
    True

  third_derivative_cutoff_value_not_proved :
    True

  cos_square_integral_value_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS226 finite linearization ledger. -/
noncomputable def thirdDerivativeFiniteLinearizationDischargeLedger :
    ThirdDerivativeFiniteLinearizationDischargeLedger where
  ts225_cutoff_reduction :=
    TS225.Goldbach.thirdDerivativeCutoffValueReductionLedger
  finite_linearization :=
    thirdDerivativeCutoffLinearization
  finite_linearization_on_positive_cutoffs :=
    thirdDerivativeFiniteLinearization_on_pos_left
  dirichlet_product_cutoffs_not_proved := True.intro
  third_derivative_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS226. -/
def ThirdDerivativeFiniteLinearizationDischargeTarget :
    Prop :=
  Nonempty ThirdDerivativeFiniteLinearizationDischargeLedger

theorem thirdDerivativeFiniteLinearizationDischargeTarget :
    ThirdDerivativeFiniteLinearizationDischargeTarget :=
  Nonempty.intro thirdDerivativeFiniteLinearizationDischargeLedger

end Goldbach
end TS226
