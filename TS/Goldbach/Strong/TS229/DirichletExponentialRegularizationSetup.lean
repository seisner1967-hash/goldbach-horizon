import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS228.DirichletProductCutoffPartialIntegralBridge

namespace TS229
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS229 - Dirichlet Exponential Regularization Setup

TS228 reduced the Wall 1 scalar chain to the single one-variable cutoff
limit

`int_0^T sin x / x dx -> pi/2` as `T -> +infty`.

This sprint prepares the Abel regularization route without claiming the
analytic theorem.  It defines the exponentially damped Dirichlet kernel,
names the damped evaluation target, names the Abel-to-cutoff bridge, and proves
the purely logical routing from those future inputs to the TS228 and TS227
targets.

No damped integral evaluation, parametric differentiation, Abel-to-cutoff
Tauberian theorem, or final Dirichlet value is proved here.
-/

/-- The exponentially damped unit-frequency Dirichlet kernel. -/
noncomputable def dampedDirichletKernel
    (b x : Real) :
    Real :=
  Real.exp (-b * x) * TS213.Goldbach.sineDirichletKernel 1 x

/--
The improper value of the damped kernel, encoded as convergence of partial
integrals over `[0, T]`.
-/
def DampedDirichletIntegralStatement
    (b value : Real) :
    Prop :=
  Tendsto
    (fun T : Real =>
      intervalIntegral
        (fun x : Real => dampedDirichletKernel b x)
        0
        T
        volume)
    atTop
    (nhds value)

/--
The target Abel evaluation for positive damping.  This is the classical formula
usually proved by differentiating under the integral sign or by a Laplace/Fubini
argument.
-/
def DampedDirichletEvaluationTarget :
    Prop :=
  forall b : Real,
    0 < b ->
      DampedDirichletIntegralStatement
        b
        (Real.pi / 2 - Real.arctan b)

/--
The Abel limit target at the origin.  It records only the limiting value of the
damped partial-integral family as `b -> 0+`, not the cutoff value itself.
-/
def DampedDirichletAbelLimitStatement :
    Prop :=
  Tendsto
    (fun b : Real => Real.pi / 2 - Real.arctan b)
    (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
    (nhds (Real.pi / 2))

/-- The elementary Abel-side scalar limit at the origin. -/
theorem dampedDirichletAbelLimit :
    DampedDirichletAbelLimitStatement := by
  unfold DampedDirichletAbelLimitStatement
  have hb :
      Tendsto
        (fun b : Real => b)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have harctan :
      Tendsto
        (fun b : Real => Real.arctan b)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (Real.arctan 0)) :=
    Real.continuousAt_arctan.tendsto.comp hb
  have hlim :
      Tendsto
        (fun b : Real => Real.pi / 2 - Real.arctan b)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (Real.pi / 2 - Real.arctan 0)) :=
    tendsto_const_nhds.sub harctan
  simpa [Real.arctan_zero] using hlim

/--
The Tauberian/continuity bridge needed to convert the Abel route into the
ordinary cutoff value from TS228.  This is deliberately a separate named target:
Abel convergence alone is not silently identified with cutoff convergence.
-/
def AbelToCutoffBridgeStatement :
    Prop :=
  DampedDirichletEvaluationTarget ->
    DampedDirichletAbelLimitStatement ->
      TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement

/-- Abel route evidence for the TS228 cutoff target. -/
structure DirichletAbelCutoffRouteEvidence where
  damped_evaluation :
    DampedDirichletEvaluationTarget

  damped_abel_limit :
    DampedDirichletAbelLimitStatement

  abel_to_cutoff_bridge :
    AbelToCutoffBridgeStatement

/-- The packaged Abel evidence supplies the TS228 one-variable cutoff target. -/
theorem dirichletUnitPartialIntegralAtTop_of_abelEvidence
    (evidence : DirichletAbelCutoffRouteEvidence) :
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement :=
  evidence.abel_to_cutoff_bridge
    evidence.damped_evaluation
    evidence.damped_abel_limit

/--
The packaged Abel evidence supplies the TS227 unit product-cutoff value through
the TS228 bridge.
-/
theorem dirichletProductCutoffUnitValue_of_abelEvidence
    (evidence : DirichletAbelCutoffRouteEvidence) :
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement :=
  TS228.Goldbach.dirichletProductCutoffUnitValue_of_partialIntegralAtTop
    (dirichletUnitPartialIntegralAtTop_of_abelEvidence evidence)

/--
The packaged Abel evidence also supplies the TS219 third-derivative cutoff
value through TS227, TS226, and TS225.
-/
theorem cosSquareThirdDerivativeCutoffValue_of_abelEvidence
    (evidence : DirichletAbelCutoffRouteEvidence) :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement :=
  TS227.Goldbach.cosSquareThirdDerivativeCutoffValue_of_unitDirichlet
    (dirichletProductCutoffUnitValue_of_abelEvidence evidence)

/-- Ledger recording the TS229 Abel setup. -/
structure DirichletExponentialRegularizationSetupLedger where
  ts228_partial_integral_bridge :
    TS228.Goldbach.DirichletProductCutoffPartialIntegralBridgeLedger

  damped_kernel_defined :
    True

  damped_integral_statement_family :
    Real -> Real -> Prop

  damped_integral_statement_family_eq :
    damped_integral_statement_family =
      DampedDirichletIntegralStatement

  damped_evaluation_target :
    Prop

  damped_evaluation_target_eq :
    damped_evaluation_target =
      DampedDirichletEvaluationTarget

  damped_abel_limit_statement :
    Prop

  damped_abel_limit_statement_eq :
    damped_abel_limit_statement =
      DampedDirichletAbelLimitStatement

  abel_to_cutoff_bridge_statement :
    Prop

  abel_to_cutoff_bridge_statement_eq :
    abel_to_cutoff_bridge_statement =
      AbelToCutoffBridgeStatement

  abel_evidence_supplies_ts228_atTop :
    DirichletAbelCutoffRouteEvidence ->
      TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement

  abel_evidence_supplies_ts227_unit :
    DirichletAbelCutoffRouteEvidence ->
      TS227.Goldbach.DirichletProductCutoffUnitValueStatement

  abel_evidence_supplies_ts219_cutoff_value :
    DirichletAbelCutoffRouteEvidence ->
      TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement

  damped_abel_limit :
    DampedDirichletAbelLimitStatement

  damped_evaluation_not_proved :
    True

  abel_to_cutoff_bridge_not_proved :
    True

  ts228_atTop_not_proved :
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

/-- Concrete TS229 setup ledger. -/
noncomputable def dirichletExponentialRegularizationSetupLedger :
    DirichletExponentialRegularizationSetupLedger where
  ts228_partial_integral_bridge :=
    TS228.Goldbach.dirichletProductCutoffPartialIntegralBridgeLedger
  damped_kernel_defined := True.intro
  damped_integral_statement_family :=
    DampedDirichletIntegralStatement
  damped_integral_statement_family_eq := rfl
  damped_evaluation_target :=
    DampedDirichletEvaluationTarget
  damped_evaluation_target_eq := rfl
  damped_abel_limit_statement :=
    DampedDirichletAbelLimitStatement
  damped_abel_limit_statement_eq := rfl
  abel_to_cutoff_bridge_statement :=
    AbelToCutoffBridgeStatement
  abel_to_cutoff_bridge_statement_eq := rfl
  abel_evidence_supplies_ts228_atTop :=
    dirichletUnitPartialIntegralAtTop_of_abelEvidence
  abel_evidence_supplies_ts227_unit :=
    dirichletProductCutoffUnitValue_of_abelEvidence
  abel_evidence_supplies_ts219_cutoff_value :=
    cosSquareThirdDerivativeCutoffValue_of_abelEvidence
  damped_abel_limit :=
    dampedDirichletAbelLimit
  damped_evaluation_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  ts228_atTop_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS229. -/
def DirichletExponentialRegularizationSetupTarget :
    Prop :=
  Nonempty DirichletExponentialRegularizationSetupLedger

theorem dirichletExponentialRegularizationSetupTarget :
    DirichletExponentialRegularizationSetupTarget :=
  Nonempty.intro dirichletExponentialRegularizationSetupLedger

end Goldbach
end TS229
