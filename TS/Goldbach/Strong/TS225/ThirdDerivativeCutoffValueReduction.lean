import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS224.CosSquareIPPPrimitiveZeroRightAsymptotic
import TS.Goldbach.Strong.TS217.DirichletImproperReformulationBridge

namespace TS225
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS225 - Third-Derivative Cutoff Value Reduction

TS224 closed the boundary-vanishing side of the corrected cutoff triple-IPP
route.  The remaining residual slot in TS219 is the cutoff value of the
third-derivative kernel

`(-2 * sin x + 4 * sin (2*x)) / x`.

This sprint reduces that value to Dirichlet cutoff values at frequencies `1`
and `2`.  It does not prove the Dirichlet cutoff theorem itself.
-/

/-- Product-filter Dirichlet cutoff integral at frequency `a`. -/
noncomputable def dirichletProductCutoffIntegral
    (a : Real)
    (p : Prod Real Real) :
    Real :=
  intervalIntegral
    (fun x : Real => TS213.Goldbach.sineDirichletKernel a x)
    p.1
    p.2
    volume

/--
The product-filter Dirichlet cutoff value at a fixed positive frequency.

This is the formulation needed by the TS219 cutoff filter:
`eps -> 0+` and `T -> +infty` simultaneously.
-/
def DirichletProductCutoffValueStatement
    (a : Real) :
    Prop :=
  Tendsto
    (fun p : Prod Real Real =>
      dirichletProductCutoffIntegral a p)
    TS219.Goldbach.cosSquareCutoffFilter
    (nhds (Real.pi / 2))

/-- Dirichlet product-cutoff evidence at the two frequencies used by `f'''`. -/
structure ThirdDerivativeDirichletProductCutoffEvidence where
  frequency_one :
    DirichletProductCutoffValueStatement 1

  frequency_two :
    DirichletProductCutoffValueStatement 2

/--
Pointwise algebraic decomposition of the TS213 third-derivative kernel into
the two Dirichlet sine kernels.
-/
theorem cosSquareThirdDerivativeKernel_eq_dirichletCombination
    (x : Real) :
    TS213.Goldbach.cosSquareThirdDerivativeKernel x =
      (-2 : Real) * TS213.Goldbach.sineDirichletKernel 1 x +
        4 * TS213.Goldbach.sineDirichletKernel 2 x := by
  unfold TS213.Goldbach.cosSquareThirdDerivativeKernel
  unfold TS213.Goldbach.sineDirichletKernel
  ring_nf

/--
The combined Dirichlet cutoff expression attached to the third-derivative
kernel.
-/
noncomputable def thirdDerivativeDirichletCombination
    (p : Prod Real Real) :
    Real :=
  (-2 : Real) * dirichletProductCutoffIntegral 1 p +
    4 * dirichletProductCutoffIntegral 2 p

/--
Dirichlet cutoff values at frequencies `1` and `2` imply that the combined
third-derivative Dirichlet expression tends to `pi`.
-/
theorem thirdDerivativeDirichletCombination_tendsto
    (evidence : ThirdDerivativeDirichletProductCutoffEvidence) :
    Tendsto
      thirdDerivativeDirichletCombination
      TS219.Goldbach.cosSquareCutoffFilter
      (nhds Real.pi) := by
  unfold thirdDerivativeDirichletCombination
  have hcombo :
      Tendsto
        (fun p : Prod Real Real =>
          (-2 : Real) * dirichletProductCutoffIntegral 1 p +
            4 * dirichletProductCutoffIntegral 2 p)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds
          ((-2 : Real) * (Real.pi / 2) +
            4 * (Real.pi / 2))) :=
    (evidence.frequency_one.const_mul (-2 : Real)).add
      (evidence.frequency_two.const_mul (4 : Real))
  have hpi :
      -(2 * (Real.pi / 2)) +
          4 * (Real.pi / 2) =
        Real.pi := by
    ring
  simpa [hpi] using hcombo

/--
Finite-integral linearization needed to identify the TS219 residual cutoff
with the Dirichlet combination.

This is a compact interval-integral algebra statement; it is separated from
the Dirichlet convergence value so that no analytic convergence is hidden.
-/
def ThirdDerivativeCutoffLinearizationStatement :
    Prop :=
  Filter.Eventually
    (fun p : Prod Real Real =>
      intervalIntegral
          (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
          p.1
          p.2
          volume =
        thirdDerivativeDirichletCombination p)
    TS219.Goldbach.cosSquareCutoffFilter

/--
Once the finite linearization and the two Dirichlet product-cutoff values are
supplied, the TS219 third-derivative cutoff value follows.
-/
theorem cosSquareThirdDerivativeCutoffValue_of_dirichletProductCutoffs
    (hlinear : ThirdDerivativeCutoffLinearizationStatement)
    (evidence : ThirdDerivativeDirichletProductCutoffEvidence) :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement := by
  unfold TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement
  have hlinear_symm :
      Filter.Eventually
        (fun p : Prod Real Real =>
          thirdDerivativeDirichletCombination p =
            intervalIntegral
              (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
              p.1
              p.2
              volume)
        TS219.Goldbach.cosSquareCutoffFilter :=
    hlinear.mono
      (fun p hp => hp.symm)
  exact
    (thirdDerivativeDirichletCombination_tendsto evidence).congr'
      hlinear_symm

/-- Evidence package for the TS225 reduction. -/
structure ThirdDerivativeCutoffValueReductionEvidence where
  finite_linearization :
    ThirdDerivativeCutoffLinearizationStatement

  dirichlet_product_cutoffs :
    ThirdDerivativeDirichletProductCutoffEvidence

/-- TS225 evidence supplies the TS219 third-derivative cutoff value. -/
theorem cosSquareThirdDerivativeCutoffValue_of_reductionEvidence
    (evidence : ThirdDerivativeCutoffValueReductionEvidence) :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement :=
  cosSquareThirdDerivativeCutoffValue_of_dirichletProductCutoffs
    evidence.finite_linearization
    evidence.dirichlet_product_cutoffs

/-- Ledger recording the TS225 third-derivative cutoff-value reduction. -/
structure ThirdDerivativeCutoffValueReductionLedger where
  ts224_boundary_vanishing :
    TS224.Goldbach.CosSquareIPPPrimitiveZeroRightAsymptoticLedger

  product_cutoff_frequency_one_statement :
    Prop

  product_cutoff_frequency_one_statement_eq :
    product_cutoff_frequency_one_statement =
      DirichletProductCutoffValueStatement 1

  product_cutoff_frequency_two_statement :
    Prop

  product_cutoff_frequency_two_statement_eq :
    product_cutoff_frequency_two_statement =
      DirichletProductCutoffValueStatement 2

  pointwise_kernel_decomposition :
    forall x : Real,
      TS213.Goldbach.cosSquareThirdDerivativeKernel x =
        (-2 : Real) * TS213.Goldbach.sineDirichletKernel 1 x +
          4 * TS213.Goldbach.sineDirichletKernel 2 x

  dirichlet_combination_tends_to_pi :
    ThirdDerivativeDirichletProductCutoffEvidence ->
      Tendsto
        thirdDerivativeDirichletCombination
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds Real.pi)

  finite_linearization_statement :
    Prop

  finite_linearization_statement_eq :
    finite_linearization_statement =
      ThirdDerivativeCutoffLinearizationStatement

  reduction_evidence_supplies_ts219_cutoff_value :
    ThirdDerivativeCutoffValueReductionEvidence ->
      TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement

  finite_linearization_not_proved :
    True

  dirichlet_product_cutoffs_not_proved :
    True

  dirichlet_cutoff_or_abel_not_proved :
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

/-- Concrete TS225 reduction ledger. -/
noncomputable def thirdDerivativeCutoffValueReductionLedger :
    ThirdDerivativeCutoffValueReductionLedger where
  ts224_boundary_vanishing :=
    TS224.Goldbach.cosSquareIPPPrimitiveZeroRightAsymptoticLedger
  product_cutoff_frequency_one_statement :=
    DirichletProductCutoffValueStatement 1
  product_cutoff_frequency_one_statement_eq := rfl
  product_cutoff_frequency_two_statement :=
    DirichletProductCutoffValueStatement 2
  product_cutoff_frequency_two_statement_eq := rfl
  pointwise_kernel_decomposition :=
    cosSquareThirdDerivativeKernel_eq_dirichletCombination
  dirichlet_combination_tends_to_pi :=
    thirdDerivativeDirichletCombination_tendsto
  finite_linearization_statement :=
    ThirdDerivativeCutoffLinearizationStatement
  finite_linearization_statement_eq := rfl
  reduction_evidence_supplies_ts219_cutoff_value :=
    cosSquareThirdDerivativeCutoffValue_of_reductionEvidence
  finite_linearization_not_proved := True.intro
  dirichlet_product_cutoffs_not_proved := True.intro
  dirichlet_cutoff_or_abel_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS225. -/
def ThirdDerivativeCutoffValueReductionTarget :
    Prop :=
  Nonempty ThirdDerivativeCutoffValueReductionLedger

theorem thirdDerivativeCutoffValueReductionTarget :
    ThirdDerivativeCutoffValueReductionTarget :=
  Nonempty.intro thirdDerivativeCutoffValueReductionLedger

end Goldbach
end TS225
