import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS227.DirichletProductCutoffScalingReduction

namespace TS228
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS228 - Dirichlet Product-Cutoff Partial-Integral Bridge

TS227 reduced all positive-frequency Dirichlet product-cutoff values to the
unit-frequency product-cutoff value.  This sprint separates the remaining
unit-frequency target into a one-sided partial integral at infinity and the
elementary lower-end contribution near zero.

The genuinely hard analytic input is now the classical one-variable cutoff
limit

`int_0^T sin x / x dx -> pi/2` as `T -> +infty`.

TS228 does not prove that value.  It proves that this one-variable partial
integral value, together with the finite interval decomposition, supplies the
TS227 product-filter unit value.
-/

/-- Unit-frequency Dirichlet partial integral from `0` to `T`. -/
noncomputable def dirichletUnitPartialIntegral
    (T : Real) :
    Real :=
  intervalIntegral
    (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
    0
    T
    volume

/-- The single remaining one-variable Dirichlet cutoff value. -/
def DirichletUnitPartialIntegralAtTopStatement :
    Prop :=
  Tendsto
    dirichletUnitPartialIntegral
    atTop
    (nhds (Real.pi / 2))

/-- The lower endpoint contribution vanishes as `eps -> 0+`. -/
def DirichletUnitPartialIntegralZeroRightStatement :
    Prop :=
  Tendsto
    dirichletUnitPartialIntegral
    (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
    (nhds (0 : Real))

/--
Finite decomposition of the unit product cutoff into two partial integrals.

This is kept as a named statement because it is the exact algebraic bridge
between the product-filter target and the one-sided partial integral target.
-/
def DirichletUnitPartialIntegralDecompositionStatement :
    Prop :=
  Filter.Eventually
    (fun p : Prod Real Real =>
      TS225.Goldbach.dirichletProductCutoffIntegral 1 p =
        dirichletUnitPartialIntegral p.2 -
          dirichletUnitPartialIntegral p.1)
    TS219.Goldbach.cosSquareCutoffFilter

/-- The TS216 cutoff target is definitionally the TS228 atTop target. -/
theorem dirichletUnitPartialIntegralAtTopStatement_eq_ts216 :
    DirichletUnitPartialIntegralAtTopStatement =
      TS216.Goldbach.DirichletUnitFrequencyCutoffStatement := by
  rfl

/-- Global elementary bound for the unit Dirichlet kernel. -/
theorem sineDirichletKernel_one_abs_le_one
    (x : Real) :
    |TS213.Goldbach.sineDirichletKernel 1 x| <= (1 : Real) := by
  unfold TS213.Goldbach.sineDirichletKernel
  by_cases hx : x = 0
  case pos =>
    simp [hx]
  case neg =>
    have hsin : |Real.sin x| <= |x| := Real.abs_sin_le_abs
    have hxabs : 0 < |x| := abs_pos.mpr hx
    rw [one_mul, abs_div]
    calc
      |Real.sin x| / |x| <= |x| / |x| := by
        exact div_le_div_of_nonneg_right hsin (abs_nonneg x)
      _ = (1 : Real) := by
        exact div_self (ne_of_gt hxabs)

/-- The partial integral is bounded by the interval length. -/
theorem dirichletUnitPartialIntegral_abs_le_abs
    (T : Real) :
    |dirichletUnitPartialIntegral T| <= |T| := by
  unfold dirichletUnitPartialIntegral
  have hbound :
      forall x : Real,
        (Set.uIoc (0 : Real) T) x ->
          norm (TS213.Goldbach.sineDirichletKernel 1 x) <=
            (1 : Real) := by
    intro x hx
    simpa [Real.norm_eq_abs] using sineDirichletKernel_one_abs_le_one x
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : Real))
      (b := T)
      (C := (1 : Real))
      (f := fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
      hbound
  simpa [Real.norm_eq_abs, abs_sub_comm] using hnorm

/-- The unit Dirichlet kernel is interval-integrable on every compact interval. -/
theorem sineDirichletKernel_one_intervalIntegrable
    (a b : Real) :
    IntervalIntegrable
      (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
      volume
      a
      b := by
  rw [intervalIntegrable_iff']
  apply Measure.integrableOn_of_bounded
  case s_finite =>
    rw [Set.uIcc]
    exact measure_Icc_lt_top.ne
  case f_mble =>
    have hmeas :
        Measurable
          (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x) := by
      unfold TS213.Goldbach.sineDirichletKernel
      simpa [one_mul] using
        (Real.measurable_sin.comp measurable_id).div measurable_id
    exact hmeas.aestronglyMeasurable
  case f_bdd =>
    exact
      Eventually.of_forall
        (fun x : Real => by
          simpa [Real.norm_eq_abs] using
            sineDirichletKernel_one_abs_le_one x)

/--
Finite additive decomposition:
`int_eps^T D_1 = F(T) - F(eps)`.
-/
theorem dirichletUnitPartialIntegral_decomposition :
    DirichletUnitPartialIntegralDecompositionStatement := by
  unfold DirichletUnitPartialIntegralDecompositionStatement
  exact
    Eventually.of_forall
      (fun p : Prod Real Real => by
        unfold TS225.Goldbach.dirichletProductCutoffIntegral
        unfold dirichletUnitPartialIntegral
        exact
          (intervalIntegral.integral_interval_sub_left
            (sineDirichletKernel_one_intervalIntegrable 0 p.2)
            (sineDirichletKernel_one_intervalIntegrable 0 p.1)).symm)

/-- The lower endpoint partial integral tends to zero. -/
theorem dirichletUnitPartialIntegralZeroRight :
    DirichletUnitPartialIntegralZeroRightStatement := by
  unfold DirichletUnitPartialIntegralZeroRightStatement
  have habs :
      Tendsto
        (fun x : Real => |x|)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) := by
    have hid :
        Tendsto
          (fun x : Real => x)
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
          (nhds (0 : Real)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.abs
  have hneg :
      Tendsto
        (fun x : Real => -|x|)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) := by
    simpa using habs.neg
  have hlower :
      Filter.Eventually
        (fun x : Real =>
          -|x| <= dirichletUnitPartialIntegral x)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    filter_upwards with x
    exact neg_le_of_abs_le (dirichletUnitPartialIntegral_abs_le_abs x)
  have hupper :
      Filter.Eventually
        (fun x : Real =>
          dirichletUnitPartialIntegral x <= |x|)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    filter_upwards with x
    exact le_of_abs_le (dirichletUnitPartialIntegral_abs_le_abs x)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hneg
      habs
      hlower
      hupper

/--
The partial-integral upper value plus the finite decomposition imply the
unit-frequency product-filter cutoff value.
-/
theorem dirichletProductCutoffUnitValue_of_partialIntegral
    (hdecomp :
      DirichletUnitPartialIntegralDecompositionStatement)
    (hupper :
      DirichletUnitPartialIntegralAtTopStatement) :
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement := by
  unfold TS227.Goldbach.DirichletProductCutoffUnitValueStatement
  unfold TS225.Goldbach.DirichletProductCutoffValueStatement
  have hT :
      Tendsto
        (fun p : Prod Real Real =>
          dirichletUnitPartialIntegral p.2)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (Real.pi / 2)) :=
    hupper.comp tendsto_snd
  have heps :
      Tendsto
        (fun p : Prod Real Real =>
          dirichletUnitPartialIntegral p.1)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (0 : Real)) :=
    dirichletUnitPartialIntegralZeroRight.comp tendsto_fst
  have hdiff :
      Tendsto
        (fun p : Prod Real Real =>
          dirichletUnitPartialIntegral p.2 -
            dirichletUnitPartialIntegral p.1)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (Real.pi / 2 - 0)) :=
    hT.sub heps
  have htarget :
      Tendsto
        (fun p : Prod Real Real =>
          dirichletUnitPartialIntegral p.2 -
            dirichletUnitPartialIntegral p.1)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (Real.pi / 2)) := by
    simpa using hdiff
  exact htarget.congr' (hdecomp.mono fun p hp => hp.symm)

/--
The one-variable partial integral value supplies the single unit-frequency
product-cutoff value required by TS227.
-/
theorem dirichletProductCutoffUnitValue_of_partialIntegralAtTop
    (hupper :
      DirichletUnitPartialIntegralAtTopStatement) :
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement :=
  dirichletProductCutoffUnitValue_of_partialIntegral
    dirichletUnitPartialIntegral_decomposition
    hupper

/-- Ledger recording the TS228 product-cutoff/partial-integral bridge. -/
structure DirichletProductCutoffPartialIntegralBridgeLedger where
  ts227_scaling_reduction :
    TS227.Goldbach.DirichletProductCutoffScalingReductionLedger

  unit_product_cutoff_statement :
    Prop

  unit_product_cutoff_statement_eq :
    unit_product_cutoff_statement =
      TS227.Goldbach.DirichletProductCutoffUnitValueStatement

  partial_integral_atTop_statement :
    Prop

  partial_integral_atTop_statement_eq :
    partial_integral_atTop_statement =
      DirichletUnitPartialIntegralAtTopStatement

  partial_integral_zero_right_statement :
    Prop

  partial_integral_zero_right_statement_eq :
    partial_integral_zero_right_statement =
      DirichletUnitPartialIntegralZeroRightStatement

  finite_decomposition_statement :
    Prop

  finite_decomposition_statement_eq :
    finite_decomposition_statement =
      DirichletUnitPartialIntegralDecompositionStatement

  kernel_abs_bound :
    forall x : Real,
      |TS213.Goldbach.sineDirichletKernel 1 x| <= (1 : Real)

  partial_integral_abs_bound :
    forall T : Real,
      |dirichletUnitPartialIntegral T| <= |T|

  partial_integral_zero_right :
    DirichletUnitPartialIntegralZeroRightStatement

  finite_decomposition :
    DirichletUnitPartialIntegralDecompositionStatement

  partial_integral_atTop_supplies_unit_value :
    DirichletUnitPartialIntegralAtTopStatement ->
      TS227.Goldbach.DirichletProductCutoffUnitValueStatement

  partial_integral_atTop_value_not_proved :
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

/-- Concrete TS228 bridge ledger. -/
noncomputable def dirichletProductCutoffPartialIntegralBridgeLedger :
    DirichletProductCutoffPartialIntegralBridgeLedger where
  ts227_scaling_reduction :=
    TS227.Goldbach.dirichletProductCutoffScalingReductionLedger
  unit_product_cutoff_statement :=
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement
  unit_product_cutoff_statement_eq := rfl
  partial_integral_atTop_statement :=
    DirichletUnitPartialIntegralAtTopStatement
  partial_integral_atTop_statement_eq := rfl
  partial_integral_zero_right_statement :=
    DirichletUnitPartialIntegralZeroRightStatement
  partial_integral_zero_right_statement_eq := rfl
  finite_decomposition_statement :=
    DirichletUnitPartialIntegralDecompositionStatement
  finite_decomposition_statement_eq := rfl
  kernel_abs_bound :=
    sineDirichletKernel_one_abs_le_one
  partial_integral_abs_bound :=
    dirichletUnitPartialIntegral_abs_le_abs
  partial_integral_zero_right :=
    dirichletUnitPartialIntegralZeroRight
  finite_decomposition :=
    dirichletUnitPartialIntegral_decomposition
  partial_integral_atTop_supplies_unit_value :=
    dirichletProductCutoffUnitValue_of_partialIntegralAtTop
  partial_integral_atTop_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS228. -/
def DirichletProductCutoffPartialIntegralBridgeTarget :
    Prop :=
  Nonempty DirichletProductCutoffPartialIntegralBridgeLedger

theorem dirichletProductCutoffPartialIntegralBridgeTarget :
    DirichletProductCutoffPartialIntegralBridgeTarget :=
  Nonempty.intro dirichletProductCutoffPartialIntegralBridgeLedger

end Goldbach
end TS228
