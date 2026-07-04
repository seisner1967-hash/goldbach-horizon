import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS226.ThirdDerivativeFiniteLinearizationDischarge

namespace TS227
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS227 - Dirichlet Product-Cutoff Scaling Reduction

TS226 discharged the last compact algebra slot in the third-derivative
cutoff-value route.  The remaining analytic inputs are the product-filter
Dirichlet cutoff values at frequencies `1` and `2`.

This sprint proves that every positive frequency product-cutoff value follows
from the unit-frequency product-cutoff value by the finite change of variables
`u = a*x` and by stability of the TS219 cutoff filter under positive scaling.

It does not prove the unit-frequency Dirichlet value itself.
-/

/-- The cutoff pair scaled by a positive frequency. -/
noncomputable def scaleCutoffPair
    (a : Real)
    (p : Prod Real Real) :
    Prod Real Real :=
  (a * p.1, a * p.2)

/-- The single remaining Dirichlet product-cutoff value after scaling. -/
def DirichletProductCutoffUnitValueStatement :
    Prop :=
  TS225.Goldbach.DirichletProductCutoffValueStatement 1

private theorem tendsto_const_mul_zero_right
    (a : Real)
    (ha : 0 < a) :
    Tendsto
      (fun x : Real => a * x)
      (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
      (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  case left =>
    have hx :
        Tendsto
          (fun x : Real => x)
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
          (nhds (0 : Real)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hx.const_mul a
  case right =>
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos ha hx

/-- The TS219 cutoff filter is stable under positive scaling of both endpoints. -/
theorem scaleCutoffPair_tendsto
    (a : Real)
    (ha : 0 < a) :
    Tendsto
      (scaleCutoffPair a)
      TS219.Goldbach.cosSquareCutoffFilter
      TS219.Goldbach.cosSquareCutoffFilter := by
  unfold scaleCutoffPair
  unfold TS219.Goldbach.cosSquareCutoffFilter
  exact
    (tendsto_const_mul_zero_right a ha).comp tendsto_fst |>.prod_mk
      (Tendsto.const_mul_atTop ha tendsto_snd)

private theorem sineDirichletKernel_scale_pointwise
    (a x : Real)
    (ha : 0 < a) :
    TS213.Goldbach.sineDirichletKernel a x =
      a * TS213.Goldbach.sineDirichletKernel 1 (a * x) := by
  unfold TS213.Goldbach.sineDirichletKernel
  by_cases hx : x = 0
  case pos =>
    simp [hx]
  case neg =>
    have ha_ne : Ne a 0 := ne_of_gt ha
    have hax : Ne (a * x) 0 := mul_ne_zero ha_ne hx
    field_simp [hx, hax, ha_ne]
    ring

/--
Finite cutoff scaling:
`int_eps^T sin(a*x)/x dx = int_{a*eps}^{a*T} sin(u)/u du`.
-/
theorem dirichletProductCutoffIntegral_scale
    (a : Real)
    (ha : 0 < a)
    (p : Prod Real Real) :
    TS225.Goldbach.dirichletProductCutoffIntegral a p =
      TS225.Goldbach.dirichletProductCutoffIntegral 1
        (scaleCutoffPair a p) := by
  unfold TS225.Goldbach.dirichletProductCutoffIntegral
  unfold scaleCutoffPair
  calc
    intervalIntegral
        (fun x : Real => TS213.Goldbach.sineDirichletKernel a x)
        p.1
        p.2
        volume =
      intervalIntegral
        (fun x : Real =>
          a * TS213.Goldbach.sineDirichletKernel 1 (a * x))
        p.1
        p.2
        volume := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact sineDirichletKernel_scale_pointwise a x ha
    _ =
      a *
        intervalIntegral
          (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 (a * x))
          p.1
          p.2
          volume := by
        rw [intervalIntegral.integral_const_mul]
    _ =
      intervalIntegral
        (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
        (a * p.1)
        (a * p.2)
        volume := by
        simp [smul_eq_mul]

/--
The unit product-cutoff Dirichlet value implies every positive-frequency
product-cutoff value.
-/
theorem dirichletProductCutoffValue_of_unit
    (a : Real)
    (ha : 0 < a)
    (hunit : DirichletProductCutoffUnitValueStatement) :
    TS225.Goldbach.DirichletProductCutoffValueStatement a := by
  unfold DirichletProductCutoffUnitValueStatement at hunit
  unfold TS225.Goldbach.DirichletProductCutoffValueStatement
  have hscaled :
      Tendsto
        (fun p : Prod Real Real =>
          TS225.Goldbach.dirichletProductCutoffIntegral 1
            (scaleCutoffPair a p))
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (Real.pi / 2)) :=
    hunit.comp (scaleCutoffPair_tendsto a ha)
  exact
    hscaled.congr'
      (Eventually.of_forall
        (fun p : Prod Real Real =>
          (dirichletProductCutoffIntegral_scale a ha p).symm))

/-- The frequency `2` product-cutoff value follows from the unit value. -/
theorem dirichletProductCutoff_freq_two_of_unit
    (hunit : DirichletProductCutoffUnitValueStatement) :
    TS225.Goldbach.DirichletProductCutoffValueStatement 2 :=
  dirichletProductCutoffValue_of_unit 2 (by norm_num) hunit

/-- Unit Dirichlet evidence supplies the two frequencies needed by TS225. -/
noncomputable def thirdDerivativeDirichletProductCutoffEvidence_of_unit
    (hunit : DirichletProductCutoffUnitValueStatement) :
    TS225.Goldbach.ThirdDerivativeDirichletProductCutoffEvidence where
  frequency_one := hunit
  frequency_two := dirichletProductCutoff_freq_two_of_unit hunit

/--
With TS226 finite linearization, the single unit-frequency Dirichlet value
implies the TS219 third-derivative cutoff value.
-/
theorem cosSquareThirdDerivativeCutoffValue_of_unitDirichlet
    (hunit : DirichletProductCutoffUnitValueStatement) :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement :=
  TS225.Goldbach.cosSquareThirdDerivativeCutoffValue_of_dirichletProductCutoffs
    TS226.Goldbach.thirdDerivativeCutoffLinearization
    (thirdDerivativeDirichletProductCutoffEvidence_of_unit hunit)

/-- Ledger recording the TS227 scaling reduction. -/
structure DirichletProductCutoffScalingReductionLedger where
  ts226_finite_linearization :
    TS226.Goldbach.ThirdDerivativeFiniteLinearizationDischargeLedger

  unit_value_statement :
    Prop

  unit_value_statement_eq :
    unit_value_statement =
      DirichletProductCutoffUnitValueStatement

  cutoff_pair_scaling :
    forall a : Real,
      0 < a ->
        Tendsto
          (scaleCutoffPair a)
          TS219.Goldbach.cosSquareCutoffFilter
          TS219.Goldbach.cosSquareCutoffFilter

  finite_integral_scaling :
    forall a : Real,
      0 < a ->
        forall p : Prod Real Real,
          TS225.Goldbach.dirichletProductCutoffIntegral a p =
            TS225.Goldbach.dirichletProductCutoffIntegral 1
              (scaleCutoffPair a p)

  positive_frequency_of_unit :
    forall a : Real,
      0 < a ->
        DirichletProductCutoffUnitValueStatement ->
          TS225.Goldbach.DirichletProductCutoffValueStatement a

  frequency_two_of_unit :
    DirichletProductCutoffUnitValueStatement ->
      TS225.Goldbach.DirichletProductCutoffValueStatement 2

  unit_dirichlet_supplies_ts219_cutoff_value :
    DirichletProductCutoffUnitValueStatement ->
      TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement

  unit_dirichlet_value_not_proved :
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

/-- Concrete TS227 scaling-reduction ledger. -/
noncomputable def dirichletProductCutoffScalingReductionLedger :
    DirichletProductCutoffScalingReductionLedger where
  ts226_finite_linearization :=
    TS226.Goldbach.thirdDerivativeFiniteLinearizationDischargeLedger
  unit_value_statement :=
    DirichletProductCutoffUnitValueStatement
  unit_value_statement_eq := rfl
  cutoff_pair_scaling :=
    scaleCutoffPair_tendsto
  finite_integral_scaling :=
    dirichletProductCutoffIntegral_scale
  positive_frequency_of_unit :=
    dirichletProductCutoffValue_of_unit
  frequency_two_of_unit :=
    dirichletProductCutoff_freq_two_of_unit
  unit_dirichlet_supplies_ts219_cutoff_value :=
    cosSquareThirdDerivativeCutoffValue_of_unitDirichlet
  unit_dirichlet_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS227. -/
def DirichletProductCutoffScalingReductionTarget :
    Prop :=
  Nonempty DirichletProductCutoffScalingReductionLedger

theorem dirichletProductCutoffScalingReductionTarget :
    DirichletProductCutoffScalingReductionTarget :=
  Nonempty.intro dirichletProductCutoffScalingReductionLedger

end Goldbach
end TS227
