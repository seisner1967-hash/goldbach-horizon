import TS.Goldbach.Strong.TS243.DirichletCutoffAbelFinalValueIdentification
import TS.Goldbach.Strong.TS227.DirichletProductCutoffScalingReduction

/-!
# TS244 - Dirichlet Product-Cutoff and Third-Derivative Discharge

TS243 proved the one-sided unit-frequency Dirichlet cutoff value.  TS228
transports that value to the product cutoff filter, and TS227 transports it to
every positive frequency and to the third-derivative cutoff slot from TS219.

This sprint performs those applications without adding a new analytic input.
The remaining cos-square work is kept explicit: the cutoff integral still has
to be identified with the existing Lebesgue integral, and the TS219 limiting
assembly still has to be discharged.
-/

namespace TS244
namespace Goldbach

/-- The TS243 one-sided value supplies the unit product-filter cutoff value. -/
theorem dirichletProductCutoffUnitValue :
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement :=
  TS228.Goldbach.dirichletProductCutoffUnitValue_of_partialIntegralAtTop
    TS243.Goldbach.dirichletUnitPartialIntegralAtTop

/-- Every positive Dirichlet frequency has product-filter cutoff value `pi/2`. -/
theorem dirichletProductCutoffValue
    (a : Real)
    (ha : 0 < a) :
    TS225.Goldbach.DirichletProductCutoffValueStatement a :=
  TS227.Goldbach.dirichletProductCutoffValue_of_unit
    a
    ha
    dirichletProductCutoffUnitValue

/-- The frequency-two product-filter value needed by the residual kernel. -/
theorem dirichletProductCutoffFrequencyTwoValue :
    TS225.Goldbach.DirichletProductCutoffValueStatement 2 :=
  dirichletProductCutoffValue 2 (by norm_num)

/-- Concrete Dirichlet evidence for the two residual frequencies. -/
noncomputable def thirdDerivativeDirichletProductCutoffEvidence :
    TS225.Goldbach.ThirdDerivativeDirichletProductCutoffEvidence :=
  TS227.Goldbach.thirdDerivativeDirichletProductCutoffEvidence_of_unit
    dirichletProductCutoffUnitValue

/-- The third-derivative cutoff integral has value `pi`. -/
theorem cosSquareThirdDerivativeCutoffValue :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement :=
  TS227.Goldbach.cosSquareThirdDerivativeCutoffValue_of_unitDirichlet
    dirichletProductCutoffUnitValue

/-- Ledger recording the unconditional TS243-to-TS219 cutoff discharge. -/
structure DirichletProductCutoffThirdDerivativeDischargeLedger where
  ts243_final_value :
    TS243.Goldbach.DirichletCutoffAbelFinalValueIdentificationLedger

  ts227_scaling_reduction :
    TS227.Goldbach.DirichletProductCutoffScalingReductionLedger

  unit_product_cutoff_value_proved :
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement

  positive_frequency_product_cutoff_values_proved :
    forall a : Real,
      0 < a ->
        TS225.Goldbach.DirichletProductCutoffValueStatement a

  frequency_two_product_cutoff_value_proved :
    TS225.Goldbach.DirichletProductCutoffValueStatement 2

  third_derivative_cutoff_value_proved :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement

  improper_cutoff_convergence_not_proved : True
  cutoff_assembly_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS244 discharge ledger. -/
noncomputable def dirichletProductCutoffThirdDerivativeDischargeLedger :
    DirichletProductCutoffThirdDerivativeDischargeLedger where
  ts243_final_value :=
    TS243.Goldbach.dirichletCutoffAbelFinalValueIdentificationLedger
  ts227_scaling_reduction :=
    TS227.Goldbach.dirichletProductCutoffScalingReductionLedger
  unit_product_cutoff_value_proved :=
    dirichletProductCutoffUnitValue
  positive_frequency_product_cutoff_values_proved :=
    dirichletProductCutoffValue
  frequency_two_product_cutoff_value_proved :=
    dirichletProductCutoffFrequencyTwoValue
  third_derivative_cutoff_value_proved :=
    cosSquareThirdDerivativeCutoffValue
  improper_cutoff_convergence_not_proved := True.intro
  cutoff_assembly_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS244. -/
def DirichletProductCutoffThirdDerivativeDischargeTarget : Prop :=
  Nonempty DirichletProductCutoffThirdDerivativeDischargeLedger

/-- TS244 target: the unit cutoff value now closes the TS219 residual slot. -/
theorem dirichletProductCutoffThirdDerivativeDischargeTarget :
    DirichletProductCutoffThirdDerivativeDischargeTarget :=
  Nonempty.intro dirichletProductCutoffThirdDerivativeDischargeLedger

end Goldbach
end TS244
