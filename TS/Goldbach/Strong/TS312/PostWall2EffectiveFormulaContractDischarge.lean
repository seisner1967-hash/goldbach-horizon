import Mathlib.Tactic
import TS.Goldbach.Strong.TS181.ExplicitFormulaTraceBlueprint
import TS.Goldbach.Strong.TS199.OTSAStrategicDashboardSynthesis
import TS.Goldbach.Strong.TS204.FinalAnalyticInputsSpecification
import TS.Goldbach.Strong.TS311.InfiniteExplicitIdentity

namespace TS312
namespace Goldbach

open Filter

noncomputable section

/-!
# Post-Wall-2 effective-formula contract discharge

TS311 proves the infinite explicit identity and TS292 proves absolute
summability with an effective spectral tail.  This module records those facts
in the parametric TS204 interface.  It also registers the exact conditional
adapter required by TS181 without claiming that its rational trace packaging
or half-budget has been constructed.
-/

/-! ## Exact TS181 adapter boundary -/

/--
The additional rational data required to consume the TS181 trace blueprint.

This is intentionally stronger than the analytic identity proved in TS311:
it asks for a TS93 zero-family ledger, nonnegative rational TS95 terms, and a
positive rational budget at most one half controlling their total.
-/
structure TS181TraceBudgetAdapterData where
  zeroFamily :
    TS93.Goldbach.ZetaZeroFamilyLedger
  zeroContribution :
    TS95.Goldbach.NontrivialZeroTraceContribution
  residuals :
    TS95.Goldbach.ExplicitFormulaResidualTerms
  traceBudget :
    Rat
  traceBudget_pos :
    0 < traceBudget
  traceBudget_le_half :
    traceBudget <= 1 / 2
  trace_budget_controls_formula :
    zeroContribution.value +
        TS95.Goldbach.ExplicitFormulaResidualTerms.total residuals <=
      traceBudget

/-- Convert the named TS312 adapter data into the exact TS181 contract. -/
def TS181TraceBudgetAdapterData.toTS181Contracts
    (D : TS181TraceBudgetAdapterData) :
    TS181.Goldbach.TriangleSplineExplicitFormulaContracts where
  zeroFamily := D.zeroFamily
  zeroContribution := D.zeroContribution
  residuals := D.residuals
  traceBudget := D.traceBudget
  traceBudget_pos := D.traceBudget_pos
  traceBudget_le_half := D.traceBudget_le_half
  explicit_formula_comparison_ready := True.intro
  zero_sum_trace_bridge_ready := True.intro
  residual_error_control_ready := True.intro
  trace_budget_controls_formula := D.trace_budget_controls_formula

/--
Any completed TS312 adapter package supplies the downstream TS95 trace target.
The existence of such a package is deliberately not asserted here.
-/
theorem explicitFormulaTraceBridgeTarget_of_adapter
    (D : TS181TraceBudgetAdapterData) :
    TS95.Goldbach.ExplicitFormulaTraceBridgeTarget := by
  exact TS181.Goldbach.explicitFormulaTraceBridgeTarget_of_contracts
    TS180.Goldbach.triangleSplineTS94KernelEvidenceLedger
    D.toTS181Contracts

/-! ## Concrete TS204 statements -/

/-- Both developed infinite explicit identities exported by TS311. -/
def PostWall2ExplicitFormulaIdentityStatement : Prop :=
  forall (x : Nat), 0 < x ->
    (((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
          Real) : Complex) =
        (x : Complex) / 2 - TS292.Goldbach.infiniteZeroContribution x +
          TS311.Goldbach.infiniteExceptionalResidueContribution x +
            TS293.Goldbach.normalizeContourIntegral
              (TS305.Goldbach.fixedLeftBoundaryLimit x)) /\
      (TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x =
        TS293.Goldbach.triangleSplinePerronMainTerm x -
          (TS292.Goldbach.infiniteZeroContribution x).re +
            (TS311.Goldbach.infiniteExceptionalResidueContribution x).re +
              (TS293.Goldbach.normalizeContourIntegral
                (TS305.Goldbach.fixedLeftBoundaryLimit x)).re)

/-- The canonical Perron main term is exactly `x / 2`. -/
def PostWall2MainTermIdentificationStatement : Prop :=
  forall x : Nat,
    TS293.Goldbach.triangleSplinePerronMainTerm x = (x : Real) / 2

/-- Absolute zero summability together with the closed TS292 tail bound. -/
def PostWall2ZeroContributionBoundStatement : Prop :=
  (forall x : Nat,
    Summable (fun rho : TS292.Goldbach.ConcreteNontrivialZero =>
      norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho))) /\
  (forall (x T : Nat), 1 <= T ->
    norm (TS292.Goldbach.infiniteZeroContribution x -
        TS292.Goldbach.truncatedInfiniteZeroContribution x T) <=
      max 1 (x : Real) *
        (TS292.Goldbach.infiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate T))

/-- The componentwise post-contour residual bound proved in TS311. -/
def PostWall2ResidualBoundStatement : Prop :=
  forall x : Nat,
    norm (TS311.Goldbach.infiniteContourResidualComplex x) <=
      TS311.Goldbach.infiniteContourResidualBound x

/-- Closed nonnegative tail constant and a rate tending to zero. -/
def PostWall2EffectiveConstantsStatement : Prop :=
  0 <= TS292.Goldbach.infiniteZeroResidualTailConstant /\
    Tendsto TS292.Goldbach.logarithmicTailRate atTop (nhds 0)

/-- Conditional compatibility with the stronger TS181 rational trace layer. -/
def PostWall2TS181CompatibilityStatement : Prop :=
  TS181TraceBudgetAdapterData ->
    TS95.Goldbach.ExplicitFormulaTraceBridgeTarget

theorem postWall2ExplicitFormulaIdentity :
    PostWall2ExplicitFormulaIdentityStatement := by
  intro x hx
  exact And.intro
    (TS311.Goldbach.infiniteExplicitIdentity_complex_expanded x hx)
    (TS311.Goldbach.infiniteExplicitIdentity_real_expanded x hx)

theorem postWall2MainTermIdentification :
    PostWall2MainTermIdentificationStatement := by
  intro x
  rfl

theorem postWall2ZeroContributionBound :
    PostWall2ZeroContributionBoundStatement := by
  exact And.intro
    TS292.Goldbach.infiniteZeroSpectralTerm_norm_summable
    TS292.Goldbach.infiniteZeroContribution_sub_truncated_norm_le

theorem postWall2ResidualBound :
    PostWall2ResidualBoundStatement :=
  TS311.Goldbach.infiniteContourResidualComplex_norm_le

theorem postWall2EffectiveConstants :
    PostWall2EffectiveConstantsStatement := by
  exact And.intro
    TS292.Goldbach.infiniteZeroResidualTailConstant_nonnegative
    TS311.Goldbach.logarithmicTailRate_tendsto_zero

theorem postWall2TS181Compatibility :
    PostWall2TS181CompatibilityStatement :=
  explicitFormulaTraceBridgeTarget_of_adapter

/-! ## TS204 contract and evidence -/

/-- The concrete effective-formula contract supplied after TS311. -/
def postWall2ExplicitFormulaEffectiveInputContract :
    TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract where
  explicit_formula_identity_statement :=
    PostWall2ExplicitFormulaIdentityStatement
  main_term_identification_statement :=
    PostWall2MainTermIdentificationStatement
  zero_contribution_bound_statement :=
    PostWall2ZeroContributionBoundStatement
  residual_bound_statement :=
    PostWall2ResidualBoundStatement
  effective_constants_statement :=
    PostWall2EffectiveConstantsStatement
  compatibility_with_ts181_blueprint_statement :=
    PostWall2TS181CompatibilityStatement

/-- All six concrete TS204 fields are discharged. -/
def postWall2ExplicitFormulaEffectiveInputEvidence :
    TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
      postWall2ExplicitFormulaEffectiveInputContract where
  explicit_formula_identity := postWall2ExplicitFormulaIdentity
  main_term_identification := postWall2MainTermIdentification
  zero_contribution_bound := postWall2ZeroContributionBound
  residual_bound := postWall2ResidualBound
  effective_constants := postWall2EffectiveConstants
  compatibility_with_ts181_blueprint := postWall2TS181Compatibility

/-- Top-level target for the post-Wall-2 TS204 discharge. -/
def PostWall2EffectiveFormulaContractDischargeTarget : Prop :=
  Nonempty
    (TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
      postWall2ExplicitFormulaEffectiveInputContract)

theorem postWall2EffectiveFormulaContractDischargeTarget :
    PostWall2EffectiveFormulaContractDischargeTarget :=
  Nonempty.intro postWall2ExplicitFormulaEffectiveInputEvidence

/-! ## New strategic status without rewriting TS199 -/

/--
Mechanized post-TS311 status.  The embedded TS199 value is retained as the
historical dashboard "after TS198"; the new fields record the later facts.
-/
structure PostWall2EffectiveFormulaStatus where
  historical_dashboard :
    TS199.Goldbach.OTSAStrategicDashboardLedger
  effective_formula_evidence :
    TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
      postWall2ExplicitFormulaEffectiveInputContract
  spectral_absolute_summability :
    forall x : Nat,
      Summable (fun rho : TS292.Goldbach.ConcreteNontrivialZero =>
        norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho))
  spectral_effective_tail :
    forall (x T : Nat), 1 <= T ->
      norm (TS292.Goldbach.infiniteZeroContribution x -
          TS292.Goldbach.truncatedInfiniteZeroContribution x T) <=
        max 1 (x : Real) *
          (TS292.Goldbach.infiniteZeroResidualTailConstant *
            TS292.Goldbach.logarithmicTailRate T)
  componentwise_residual_bound :
    forall x : Nat,
      norm (TS311.Goldbach.infiniteContourResidualComplex x) <=
        TS311.Goldbach.infiniteContourResidualBound x

def postWall2EffectiveFormulaStatus : PostWall2EffectiveFormulaStatus where
  historical_dashboard := TS199.Goldbach.otsaStrategicDashboardLedger
  effective_formula_evidence :=
    postWall2ExplicitFormulaEffectiveInputEvidence
  spectral_absolute_summability :=
    TS292.Goldbach.infiniteZeroSpectralTerm_norm_summable
  spectral_effective_tail :=
    TS292.Goldbach.infiniteZeroContribution_sub_truncated_norm_le
  componentwise_residual_bound :=
    TS311.Goldbach.infiniteContourResidualComplex_norm_le

/-! ## Fail-closed ledger -/

structure TS312Ledger where
  post_wall2_status : PostWall2EffectiveFormulaStatus
  wall_2_effective_formula_discharged : True
  wall_3_summability_recorded : True
  componentwise_bound_routed : True
  ts181_adapter_registered : True
  ts181_rational_trace_packaging_not_discharged : True
  ts181_trace_budget_half_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts312Ledger : TS312Ledger where
  post_wall2_status := postWall2EffectiveFormulaStatus
  wall_2_effective_formula_discharged := True.intro
  wall_3_summability_recorded := True.intro
  componentwise_bound_routed := True.intro
  ts181_adapter_registered := True.intro
  ts181_rational_trace_packaging_not_discharged := True.intro
  ts181_trace_budget_half_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS312
