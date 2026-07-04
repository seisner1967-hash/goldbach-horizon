import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS231.LaplaceSineTransformDischarge

/-!
# TS232 - Damped Dirichlet Fubini Bridge Reduction

TS231 proved the Laplace sine transform input isolated by TS230.  This sprint
keeps the next Abel step fail-closed: it records the corrected interval-integral
Fubini route to the damped Dirichlet evaluation, proves the definitional links
to TS229, and proves that a future Fubini bridge now combines with TS231 to
give the TS229 damped evaluation target.

No Fubini theorem, auxiliary damping estimate, Abel-to-cutoff theorem, or
Dirichlet cutoff value is proved here.
-/

namespace TS232
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The damped Dirichlet partial integral from `0` to `T`. -/
noncomputable def dampedPartialIntegral (b T : Real) : Real :=
  intervalIntegral
    (fun x : Real => TS229.Goldbach.dampedDirichletKernel b x)
    0
    T
    volume

/-- The atTop value statement for the damped partial integral family. -/
def DampedPartialIntegralAtTopStatement
    (b value : Real) :
    Prop :=
  Tendsto
    (fun T : Real => dampedPartialIntegral b T)
    atTop
    (nhds value)

/-- The TS232 partial-integral statement is definitionally the TS229 one. -/
theorem dampedPartialIntegralAtTopStatement_eq_ts229
    (b value : Real) :
    DampedPartialIntegralAtTopStatement b value =
      TS229.Goldbach.DampedDirichletIntegralStatement b value := by
  rfl

/-- The damped evaluation target restated at the TS232 layer. -/
def DampedDirichletFubiniEvaluationStatement :
    Prop :=
  TS229.Goldbach.DampedDirichletEvaluationTarget

/-- The TS232 damped evaluation target is exactly the TS229 target. -/
theorem dampedDirichletFubiniEvaluationStatement_eq_ts229 :
    DampedDirichletFubiniEvaluationStatement =
      TS229.Goldbach.DampedDirichletEvaluationTarget := by
  rfl

/--
Correct finite compact Fubini identity for the damped difference.

For `0 < b < A` and `0 <= T`, this is the finite-rectangle statement obtained
by integrating
`exp(-b*x) * D_1(x) - exp(-A*x) * D_1(x)` through the parameter variable.
It deliberately uses `intervalIntegral`, not an improper set integral.
-/
def CompactFubiniIdentityStatement :
    Prop :=
  forall b A T : Real,
    0 < b ->
      b < A ->
        0 <= T ->
          dampedPartialIntegral b T - dampedPartialIntegral A T =
            intervalIntegral
              (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T)
              b
              A
              volume

/--
Uniform vanishing of the TS231 finite boundary after integrating in the
Laplace parameter over a compact interval `[b, A]`.
-/
def LaplaceBoundaryUniformLimitStatement :
    Prop :=
  forall b A : Real,
    0 < b ->
      b < A ->
        Tendsto
          (fun T : Real =>
            intervalIntegral
              (fun s : Real =>
                Real.exp (-(s * T)) *
                  (s * Real.sin T + Real.cos T) /
                    (1 + s ^ 2))
              b
              A
              volume)
          atTop
          (nhds (0 : Real))

/--
The finite Fubini identity plus the uniform TS231 boundary control should make
the damped difference converge to the arctangent difference.
-/
def DampedDifferenceAtTopStatement :
    Prop :=
  forall b A : Real,
    0 < b ->
      b < A ->
        Tendsto
          (fun T : Real =>
            dampedPartialIntegral b T - dampedPartialIntegral A T)
          atTop
          (nhds (Real.arctan A - Real.arctan b))

/--
The auxiliary high-damping bound needed to let `A -> +infty` in the damped
difference route.
-/
def AuxiliaryDampingUniformBoundStatement :
    Prop :=
  forall A T : Real,
    0 < A ->
      0 <= T ->
        |dampedPartialIntegral A T| <= (1 : Real) / A

/--
The corrected Fubini execution route: compact Fubini, uniform TS231 boundary
control, and the auxiliary damping bound should imply the TS230 bridge.

This is kept as a future analytic input rather than silently asserted.
-/
def CorrectedFubiniExecutionStatement :
    Prop :=
  CompactFubiniIdentityStatement ->
    LaplaceBoundaryUniformLimitStatement ->
      DampedDifferenceAtTopStatement ->
        AuxiliaryDampingUniformBoundStatement ->
          TS230.Goldbach.DampedDirichletFubiniBridgeStatement

/-- A proved damped evaluation target trivially supplies the TS230 bridge. -/
theorem dampedDirichletFubiniBridge_of_evaluation
    (hEval : DampedDirichletFubiniEvaluationStatement) :
    TS230.Goldbach.DampedDirichletFubiniBridgeStatement := by
  intro hLaplace hArctan
  exact hEval

/--
After TS231, the only missing TS230 input is the Fubini bridge itself.  A future
proof of that bridge immediately gives the TS229 damped evaluation target.
-/
theorem dampedDirichletEvaluation_of_ts231_and_fubiniBridge
    (hBridge : TS230.Goldbach.DampedDirichletFubiniBridgeStatement) :
    TS229.Goldbach.DampedDirichletEvaluationTarget :=
  TS230.Goldbach.dampedDirichletEvaluation_of_reductionInputs
    TS231.Goldbach.laplaceSineTransform
    hBridge

/-- Ledger recording the TS232 Fubini bridge reduction. -/
structure DampedDirichletFubiniBridgeReductionLedger where
  ts231_laplace_discharge :
    TS231.Goldbach.LaplaceSineTransformDischargeLedger

  damped_partial_integral_family :
    Real -> Real -> Real
  damped_partial_integral_family_eq :
    damped_partial_integral_family = dampedPartialIntegral

  damped_partial_integral_statement :
    Real -> Real -> Prop
  damped_partial_integral_statement_eq :
    damped_partial_integral_statement =
      DampedPartialIntegralAtTopStatement

  damped_partial_integral_statement_eq_ts229 :
    forall b value : Real,
      DampedPartialIntegralAtTopStatement b value =
        TS229.Goldbach.DampedDirichletIntegralStatement b value

  compact_fubini_identity_statement :
    Prop
  compact_fubini_identity_statement_eq :
    compact_fubini_identity_statement =
      CompactFubiniIdentityStatement

  laplace_boundary_uniform_limit_statement :
    Prop
  laplace_boundary_uniform_limit_statement_eq :
    laplace_boundary_uniform_limit_statement =
      LaplaceBoundaryUniformLimitStatement

  damped_difference_atTop_statement :
    Prop
  damped_difference_atTop_statement_eq :
    damped_difference_atTop_statement =
      DampedDifferenceAtTopStatement

  auxiliary_damping_uniform_bound_statement :
    Prop
  auxiliary_damping_uniform_bound_statement_eq :
    auxiliary_damping_uniform_bound_statement =
      AuxiliaryDampingUniformBoundStatement

  corrected_fubini_execution_statement :
    Prop
  corrected_fubini_execution_statement_eq :
    corrected_fubini_execution_statement =
      CorrectedFubiniExecutionStatement

  fubini_bridge_statement :
    Prop
  fubini_bridge_statement_eq :
    fubini_bridge_statement =
      TS230.Goldbach.DampedDirichletFubiniBridgeStatement

  damped_evaluation_statement :
    Prop
  damped_evaluation_statement_eq :
    damped_evaluation_statement =
      DampedDirichletFubiniEvaluationStatement
  damped_evaluation_statement_eq_ts229 :
    DampedDirichletFubiniEvaluationStatement =
      TS229.Goldbach.DampedDirichletEvaluationTarget

  evaluation_supplies_fubini_bridge :
    DampedDirichletFubiniEvaluationStatement ->
      TS230.Goldbach.DampedDirichletFubiniBridgeStatement

  ts231_plus_fubini_bridge_supplies_evaluation :
    TS230.Goldbach.DampedDirichletFubiniBridgeStatement ->
      TS229.Goldbach.DampedDirichletEvaluationTarget

  compact_fubini_identity_not_proved :
    True
  laplace_boundary_uniform_limit_not_proved :
    True
  damped_difference_atTop_not_proved :
    True
  auxiliary_damping_uniform_bound_not_proved :
    True
  corrected_fubini_execution_not_proved :
    True
  damped_dirichlet_evaluation_not_proved :
    True
  abel_to_cutoff_bridge_not_proved :
    True
  dirichlet_cutoff_value_not_proved :
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

/-- Concrete TS232 ledger. -/
noncomputable def dampedDirichletFubiniBridgeReductionLedger :
    DampedDirichletFubiniBridgeReductionLedger where
  ts231_laplace_discharge :=
    TS231.Goldbach.laplaceSineTransformDischargeLedger
  damped_partial_integral_family :=
    dampedPartialIntegral
  damped_partial_integral_family_eq := rfl
  damped_partial_integral_statement :=
    DampedPartialIntegralAtTopStatement
  damped_partial_integral_statement_eq := rfl
  damped_partial_integral_statement_eq_ts229 :=
    dampedPartialIntegralAtTopStatement_eq_ts229
  compact_fubini_identity_statement :=
    CompactFubiniIdentityStatement
  compact_fubini_identity_statement_eq := rfl
  laplace_boundary_uniform_limit_statement :=
    LaplaceBoundaryUniformLimitStatement
  laplace_boundary_uniform_limit_statement_eq := rfl
  damped_difference_atTop_statement :=
    DampedDifferenceAtTopStatement
  damped_difference_atTop_statement_eq := rfl
  auxiliary_damping_uniform_bound_statement :=
    AuxiliaryDampingUniformBoundStatement
  auxiliary_damping_uniform_bound_statement_eq := rfl
  corrected_fubini_execution_statement :=
    CorrectedFubiniExecutionStatement
  corrected_fubini_execution_statement_eq := rfl
  fubini_bridge_statement :=
    TS230.Goldbach.DampedDirichletFubiniBridgeStatement
  fubini_bridge_statement_eq := rfl
  damped_evaluation_statement :=
    DampedDirichletFubiniEvaluationStatement
  damped_evaluation_statement_eq := rfl
  damped_evaluation_statement_eq_ts229 :=
    dampedDirichletFubiniEvaluationStatement_eq_ts229
  evaluation_supplies_fubini_bridge :=
    dampedDirichletFubiniBridge_of_evaluation
  ts231_plus_fubini_bridge_supplies_evaluation :=
    dampedDirichletEvaluation_of_ts231_and_fubiniBridge
  compact_fubini_identity_not_proved := True.intro
  laplace_boundary_uniform_limit_not_proved := True.intro
  damped_difference_atTop_not_proved := True.intro
  auxiliary_damping_uniform_bound_not_proved := True.intro
  corrected_fubini_execution_not_proved := True.intro
  damped_dirichlet_evaluation_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  dirichlet_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS232. -/
def DampedDirichletFubiniBridgeReductionTarget :
    Prop :=
  Nonempty DampedDirichletFubiniBridgeReductionLedger

/-- TS232 target: the corrected Fubini bridge route is isolated and routed. -/
theorem dampedDirichletFubiniBridgeReductionTarget :
    DampedDirichletFubiniBridgeReductionTarget :=
  Nonempty.intro dampedDirichletFubiniBridgeReductionLedger

end Goldbach
end TS232
