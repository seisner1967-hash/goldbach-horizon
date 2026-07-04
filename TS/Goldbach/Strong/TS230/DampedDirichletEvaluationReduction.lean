import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import TS.Goldbach.Strong.TS229.DirichletExponentialRegularizationSetup

/-!
# TS230 - Damped Dirichlet Evaluation Reduction

TS229 introduced the Abel route for the remaining Dirichlet cutoff value.
This sprint keeps the route fail-closed: it proves the scalar arctangent
tail calculation and isolates the two analytic obligations still needed to
evaluate the damped Dirichlet integral.
-/

namespace TS230
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The Laplace transform kernel for the sine function. -/
noncomputable def laplaceSineKernel (s x : Real) : Real :=
  Real.exp (-(s * x)) * Real.sin x

/-- The finite partial integral of the Laplace sine kernel. -/
noncomputable def laplaceSinePartialIntegral
    (s T : Real) :
    Real :=
  intervalIntegral
    (fun x : Real => laplaceSineKernel s x)
    0
    T
    volume

/--
The Laplace sine transform statement needed by the Abel/Fubini route.

This is intentionally kept as a future analytic obligation: it is the
standard value
`int_0^infty exp(-s*x) * sin x dx = 1 / (1 + s^2)` for `s > 0`.
-/
def LaplaceSineTransformStatement : Prop :=
  forall s : Real, 0 < s ->
    Tendsto
      (fun T : Real => laplaceSinePartialIntegral s T)
      atTop
      (nhds ((1 : Real) / (1 + s ^ 2)))

/--
The scalar arctangent tail statement which converts the Laplace sine
transform in the parameter variable to the expected damped value.
-/
def ArctanTailEvaluationStatement : Prop :=
  forall b : Real, 0 < b ->
    Tendsto
      (fun A : Real =>
        intervalIntegral
          (fun s : Real => (1 : Real) / (1 + s ^ 2))
          b
          A
          volume)
      atTop
      (nhds (Real.pi / 2 - Real.arctan b))

/--
The remaining Fubini/arctangent bridge for the damped Dirichlet value.

It is the future analytic step saying that the Laplace sine transform,
together with the scalar arctangent tail calculation, evaluates the damped
Dirichlet integral from TS229.
-/
def DampedDirichletFubiniBridgeStatement : Prop :=
  LaplaceSineTransformStatement ->
    ArctanTailEvaluationStatement ->
      TS229.Goldbach.DampedDirichletEvaluationTarget

/-- The interval integral of `1 / (1 + s^2)` is the arctangent difference. -/
theorem arctan_intervalIntegral_inv_one_add_sq
    (a b : Real) :
    intervalIntegral
      (fun s : Real => (1 : Real) / (1 + s ^ 2))
      a
      b
      volume =
      Real.arctan b - Real.arctan a := by
  simp [one_div, integral_inv_one_add_sq]

/-- The scalar arctangent tail needed by the damped Dirichlet route. -/
theorem arctanTailEvaluation :
    ArctanTailEvaluationStatement := by
  intro b hb
  have harctan :
      Tendsto
        (fun A : Real => Real.arctan A)
        atTop
        (nhds (Real.pi / 2)) := by
    exact Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have htail :
      Tendsto
        (fun A : Real => Real.arctan A - Real.arctan b)
        atTop
        (nhds (Real.pi / 2 - Real.arctan b)) := by
    simpa using harctan.sub tendsto_const_nhds
  refine htail.congr' ?_
  exact Eventually.of_forall fun A =>
    (arctan_intervalIntegral_inv_one_add_sq b A).symm

/--
Evidence package for the TS230 reduction.

The scalar arctangent tail is proved in this sprint.  The Laplace sine
transform and the Fubini bridge remain explicit analytic obligations.
-/
structure DampedDirichletEvaluationReductionEvidence where
  ts229_abel_setup :
    TS229.Goldbach.DirichletExponentialRegularizationSetupLedger

  laplace_sine_transform_statement : Prop
  laplace_sine_transform_statement_eq :
    laplace_sine_transform_statement = LaplaceSineTransformStatement

  arctan_tail_statement : Prop
  arctan_tail_statement_eq :
    arctan_tail_statement = ArctanTailEvaluationStatement
  arctan_tail_proved :
    arctan_tail_statement

  fubini_bridge_statement : Prop
  fubini_bridge_statement_eq :
    fubini_bridge_statement = DampedDirichletFubiniBridgeStatement

  damped_evaluation_reduction :
    laplace_sine_transform_statement ->
      fubini_bridge_statement ->
        TS229.Goldbach.DampedDirichletEvaluationTarget

  laplace_sine_transform_not_proved : True
  fubini_bridge_not_proved : True
  damped_dirichlet_evaluation_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  dirichlet_cutoff_value_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  goldbach_not_claimed : True

/-- The proved scalar tail and future Fubini bridge imply the TS229 damped target. -/
theorem dampedDirichletEvaluation_of_reductionInputs
    (hLaplace : LaplaceSineTransformStatement)
    (hBridge : DampedDirichletFubiniBridgeStatement) :
    TS229.Goldbach.DampedDirichletEvaluationTarget := by
  exact hBridge hLaplace arctanTailEvaluation

/-- Concrete TS230 reduction ledger. -/
noncomputable def dampedDirichletEvaluationReductionEvidence :
    DampedDirichletEvaluationReductionEvidence where
  ts229_abel_setup :=
    TS229.Goldbach.dirichletExponentialRegularizationSetupLedger
  laplace_sine_transform_statement := LaplaceSineTransformStatement
  laplace_sine_transform_statement_eq := rfl
  arctan_tail_statement := ArctanTailEvaluationStatement
  arctan_tail_statement_eq := rfl
  arctan_tail_proved := arctanTailEvaluation
  fubini_bridge_statement := DampedDirichletFubiniBridgeStatement
  fubini_bridge_statement_eq := rfl
  damped_evaluation_reduction := fun hLaplace hBridge =>
    dampedDirichletEvaluation_of_reductionInputs hLaplace hBridge
  laplace_sine_transform_not_proved := True.intro
  fubini_bridge_not_proved := True.intro
  damped_dirichlet_evaluation_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  dirichlet_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS230. -/
def DampedDirichletEvaluationReductionTarget : Prop :=
  Nonempty DampedDirichletEvaluationReductionEvidence

/-- TS230 target: the damped evaluation route is reduced to named analytic inputs. -/
theorem dampedDirichletEvaluationReductionTarget :
    DampedDirichletEvaluationReductionTarget :=
  Nonempty.intro dampedDirichletEvaluationReductionEvidence

end Goldbach
end TS230
