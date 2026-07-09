import Mathlib.Tactic
import TS.Goldbach.Strong.TS236.AuxiliaryDampingUniformBoundDischarge

/-!
# TS237 - Corrected Fubini Execution Assembly

TS236 discharged the final auxiliary estimate isolated by TS232.  This sprint
assembles the corrected Fubini execution statement:

`TS232.Goldbach.CorrectedFubiniExecutionStatement`.

The only nontrivial connective step is the standard two-parameter passage:
use the damped-difference limit for fixed `0 < b < A`, use the auxiliary
bound to remove the strongly damped `A` term, then let `A -> +infty`.

No Abel-to-cutoff bridge, ordinary Dirichlet cutoff value, cos-square value,
sinc-fourth value, Plancherel evidence, or Goldbach statement is proved here.
-/

namespace TS237
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The arctangent difference tends to the damped Dirichlet value as `A -> +infty`. -/
theorem arctanDifference_atTop
    (b : Real) :
    Tendsto
      (fun A : Real => Real.arctan A - Real.arctan b)
      atTop
      (nhds (Real.pi / 2 - Real.arctan b)) := by
  exact
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).sub
      tendsto_const_nhds

/-- The scalar high-damping error `1 / A` vanishes as `A -> +infty`. -/
theorem one_div_atTop_zero :
    Tendsto (fun A : Real => (1 : Real) / A) atTop (nhds (0 : Real)) := by
  simpa [one_div] using
    ((tendsto_const_nhds (x := (1 : Real))).div_atTop
      (show Tendsto (fun A : Real => A) atTop atTop from tendsto_id))

/--
The damped-difference limit and the auxiliary high-damping bound imply the full
damped Dirichlet evaluation target.
-/
theorem dampedEvaluationTarget_of_difference_and_auxiliaryBound
    (hDiff : TS232.Goldbach.DampedDifferenceAtTopStatement)
    (hAux : TS232.Goldbach.AuxiliaryDampingUniformBoundStatement) :
    TS229.Goldbach.DampedDirichletEvaluationTarget := by
  intro b hb
  unfold TS229.Goldbach.DampedDirichletIntegralStatement
  change
    Tendsto
      (fun T : Real => TS232.Goldbach.dampedPartialIntegral b T)
      atTop
      (nhds (Real.pi / 2 - Real.arctan b))
  rw [Metric.tendsto_atTop]
  intro eps heps
  let eta : Real := eps / 3
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hArcMetric :=
    (Metric.tendsto_atTop.1 (arctanDifference_atTop b) eta heta)
  have hInvMetric :=
    (Metric.tendsto_atTop.1 one_div_atTop_zero eta heta)
  let Aarc : Real := Classical.choose hArcMetric
  have hAarc :
      forall n : Real, Aarc <= n ->
        dist (Real.arctan n - Real.arctan b)
          (Real.pi / 2 - Real.arctan b) < eta :=
    Classical.choose_spec hArcMetric
  let Ainv : Real := Classical.choose hInvMetric
  have hAinv :
      forall n : Real, Ainv <= n ->
        dist ((1 : Real) / n) (0 : Real) < eta :=
    Classical.choose_spec hInvMetric
  let A : Real := max (max Aarc Ainv) (max (b + 1) 1)
  have hA_ge_arc : Aarc <= A := by
    dsimp [A]
    exact le_trans (le_max_left Aarc Ainv) (le_max_left _ _)
  have hA_ge_inv : Ainv <= A := by
    dsimp [A]
    exact le_trans (le_max_right Aarc Ainv) (le_max_left _ _)
  have hbA : b < A := by
    dsimp [A]
    have hb_le : b + 1 <= max (b + 1) (1 : Real) := le_max_left _ _
    have hmax_le : max (b + 1) (1 : Real) <=
        max (max Aarc Ainv) (max (b + 1) 1) := le_max_right _ _
    linarith
  have hApos : 0 < A := by
    dsimp [A]
    have hone_le : (1 : Real) <= max (b + 1) (1 : Real) := le_max_right _ _
    have hmax_le : max (b + 1) (1 : Real) <=
        max (max Aarc Ainv) (max (b + 1) 1) := le_max_right _ _
    linarith
  have hArcA_dist :
      dist (Real.arctan A - Real.arctan b)
        (Real.pi / 2 - Real.arctan b) < eta :=
    hAarc A hA_ge_arc
  have hInvA_dist :
      dist ((1 : Real) / A) (0 : Real) < eta :=
    hAinv A hA_ge_inv
  have hArcA_abs :
      |(Real.arctan A - Real.arctan b) -
        (Real.pi / 2 - Real.arctan b)| < eta := by
    simpa [Real.dist_eq] using hArcA_dist
  have hInvA_abs :
      (1 : Real) / A < eta := by
    have hDistEq :
        dist ((1 : Real) / A) (0 : Real) = (1 : Real) / A := by
      rw [Real.dist_eq]
      have hDivPos : 0 < (1 : Real) / A := one_div_pos.mpr hApos
      have hSub : (1 : Real) / A - 0 = (1 : Real) / A := by ring
      rw [hSub, abs_of_pos hDivPos]
    rwa [hDistEq] at hInvA_dist
  have hDifference :=
    hDiff b A hb hbA
  have hDiffMetric := Metric.tendsto_atTop.1 hDifference eta heta
  let Ndiff : Real := Classical.choose hDiffMetric
  have hNdiff :
      forall n : Real, Ndiff <= n ->
        dist
          (TS232.Goldbach.dampedPartialIntegral b n -
            TS232.Goldbach.dampedPartialIntegral A n)
          (Real.arctan A - Real.arctan b) < eta :=
    Classical.choose_spec hDiffMetric
  refine Exists.intro (max Ndiff 0) ?_
  intro T hT
  have hTdiff : Ndiff <= T := le_trans (le_max_left Ndiff 0) hT
  have hTnonneg : 0 <= T := le_trans (le_max_right Ndiff 0) hT
  have hDiffT_dist :
      dist
        (TS232.Goldbach.dampedPartialIntegral b T -
          TS232.Goldbach.dampedPartialIntegral A T)
        (Real.arctan A - Real.arctan b) < eta :=
    hNdiff T hTdiff
  have hDiffT_abs :
      |(TS232.Goldbach.dampedPartialIntegral b T -
          TS232.Goldbach.dampedPartialIntegral A T) -
        (Real.arctan A - Real.arctan b)| < eta := by
    simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hDiffT_dist
  have hAuxT :
      |TS232.Goldbach.dampedPartialIntegral A T| <= (1 : Real) / A :=
    hAux A T hApos hTnonneg
  have hTri :
      |TS232.Goldbach.dampedPartialIntegral b T -
          (Real.pi / 2 - Real.arctan b)| <=
        |(TS232.Goldbach.dampedPartialIntegral b T -
            TS232.Goldbach.dampedPartialIntegral A T) -
          (Real.arctan A - Real.arctan b)| +
          |TS232.Goldbach.dampedPartialIntegral A T| +
          |(Real.arctan A - Real.arctan b) -
            (Real.pi / 2 - Real.arctan b)| := by
    set Fb := TS232.Goldbach.dampedPartialIntegral b T
    set FA := TS232.Goldbach.dampedPartialIntegral A T
    set dA := Real.arctan A - Real.arctan b
    set L := Real.pi / 2 - Real.arctan b
    have hsplit :
        Fb - L = ((Fb - FA) - dA) + FA + (dA - L) := by ring
    calc
      |Fb - L|
          = |((Fb - FA) - dA) + FA + (dA - L)| := by rw [hsplit]
      _ <= |((Fb - FA) - dA) + FA| + |dA - L| := by
          exact abs_add _ _
      _ <= (|((Fb - FA) - dA)| + |FA|) + |dA - L| := by
          exact add_le_add_right (abs_add _ _) _
      _ =
          |((Fb - FA) - dA)| + |FA| + |dA - L| := by ring
  have hSum :
      |(TS232.Goldbach.dampedPartialIntegral b T -
          TS232.Goldbach.dampedPartialIntegral A T) -
        (Real.arctan A - Real.arctan b)| +
          |TS232.Goldbach.dampedPartialIntegral A T| +
          |(Real.arctan A - Real.arctan b) -
            (Real.pi / 2 - Real.arctan b)| < eps := by
    have hAuxEta :
        |TS232.Goldbach.dampedPartialIntegral A T| < eta :=
      lt_of_le_of_lt hAuxT hInvA_abs
    have heta_eq : eps = 3 * eta := by
      dsimp [eta]
      ring
    nlinarith
  have hAbs :
      |TS232.Goldbach.dampedPartialIntegral b T -
          (Real.pi / 2 - Real.arctan b)| < eps :=
    lt_of_le_of_lt hTri hSum
  rw [Real.dist_eq]
  exact hAbs

/-- The corrected Fubini execution statement from TS232. -/
theorem correctedFubiniExecution :
    TS232.Goldbach.CorrectedFubiniExecutionStatement := by
  intro hCompact hBoundary hDiff hAux
  intro hLaplace hArctan
  exact dampedEvaluationTarget_of_difference_and_auxiliaryBound hDiff hAux

/-- The TS233--TS236 discharges supply the TS230 Fubini bridge. -/
theorem dampedDirichletFubiniBridge :
    TS230.Goldbach.DampedDirichletFubiniBridgeStatement :=
  correctedFubiniExecution
    TS233.Goldbach.compactFubiniIdentity
    TS234.Goldbach.laplaceBoundaryUniformLimit
    TS235.Goldbach.dampedDifferenceAtTop
    TS236.Goldbach.auxiliaryDampingUniformBound

/-- The proved Fubini bridge and TS231 supply the damped Dirichlet evaluation. -/
theorem dampedDirichletEvaluationTarget :
    TS229.Goldbach.DampedDirichletEvaluationTarget :=
  TS232.Goldbach.dampedDirichletEvaluation_of_ts231_and_fubiniBridge
    dampedDirichletFubiniBridge

/-- Ledger recording the corrected Fubini execution assembly. -/
structure CorrectedFubiniExecutionAssemblyLedger where
  ts236_auxiliary_damping :
    TS236.Goldbach.AuxiliaryDampingUniformBoundDischargeLedger

  compact_fubini_identity_statement : Prop
  compact_fubini_identity_statement_eq :
    compact_fubini_identity_statement =
      TS232.Goldbach.CompactFubiniIdentityStatement
  compact_fubini_identity_proved :
    compact_fubini_identity_statement

  laplace_boundary_uniform_limit_statement : Prop
  laplace_boundary_uniform_limit_statement_eq :
    laplace_boundary_uniform_limit_statement =
      TS232.Goldbach.LaplaceBoundaryUniformLimitStatement
  laplace_boundary_uniform_limit_proved :
    laplace_boundary_uniform_limit_statement

  damped_difference_atTop_statement : Prop
  damped_difference_atTop_statement_eq :
    damped_difference_atTop_statement =
      TS232.Goldbach.DampedDifferenceAtTopStatement
  damped_difference_atTop_proved :
    damped_difference_atTop_statement

  auxiliary_damping_uniform_bound_statement : Prop
  auxiliary_damping_uniform_bound_statement_eq :
    auxiliary_damping_uniform_bound_statement =
      TS232.Goldbach.AuxiliaryDampingUniformBoundStatement
  auxiliary_damping_uniform_bound_proved :
    auxiliary_damping_uniform_bound_statement

  corrected_fubini_execution_statement : Prop
  corrected_fubini_execution_statement_eq :
    corrected_fubini_execution_statement =
      TS232.Goldbach.CorrectedFubiniExecutionStatement
  corrected_fubini_execution_proved :
    corrected_fubini_execution_statement

  fubini_bridge_statement : Prop
  fubini_bridge_statement_eq :
    fubini_bridge_statement =
      TS230.Goldbach.DampedDirichletFubiniBridgeStatement
  fubini_bridge_proved :
    fubini_bridge_statement

  damped_evaluation_target : Prop
  damped_evaluation_target_eq :
    damped_evaluation_target =
      TS229.Goldbach.DampedDirichletEvaluationTarget
  damped_evaluation_target_proved :
    damped_evaluation_target

  arctan_atTop_used : True
  high_damping_error_vanishing_used : True

  abel_to_cutoff_bridge_not_proved : True
  dirichlet_cutoff_value_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS237 assembly ledger. -/
noncomputable def correctedFubiniExecutionAssemblyLedger :
    CorrectedFubiniExecutionAssemblyLedger where
  ts236_auxiliary_damping :=
    TS236.Goldbach.auxiliaryDampingUniformBoundDischargeLedger
  compact_fubini_identity_statement :=
    TS232.Goldbach.CompactFubiniIdentityStatement
  compact_fubini_identity_statement_eq := rfl
  compact_fubini_identity_proved :=
    TS233.Goldbach.compactFubiniIdentity
  laplace_boundary_uniform_limit_statement :=
    TS232.Goldbach.LaplaceBoundaryUniformLimitStatement
  laplace_boundary_uniform_limit_statement_eq := rfl
  laplace_boundary_uniform_limit_proved :=
    TS234.Goldbach.laplaceBoundaryUniformLimit
  damped_difference_atTop_statement :=
    TS232.Goldbach.DampedDifferenceAtTopStatement
  damped_difference_atTop_statement_eq := rfl
  damped_difference_atTop_proved :=
    TS235.Goldbach.dampedDifferenceAtTop
  auxiliary_damping_uniform_bound_statement :=
    TS232.Goldbach.AuxiliaryDampingUniformBoundStatement
  auxiliary_damping_uniform_bound_statement_eq := rfl
  auxiliary_damping_uniform_bound_proved :=
    TS236.Goldbach.auxiliaryDampingUniformBound
  corrected_fubini_execution_statement :=
    TS232.Goldbach.CorrectedFubiniExecutionStatement
  corrected_fubini_execution_statement_eq := rfl
  corrected_fubini_execution_proved :=
    correctedFubiniExecution
  fubini_bridge_statement :=
    TS230.Goldbach.DampedDirichletFubiniBridgeStatement
  fubini_bridge_statement_eq := rfl
  fubini_bridge_proved :=
    dampedDirichletFubiniBridge
  damped_evaluation_target :=
    TS229.Goldbach.DampedDirichletEvaluationTarget
  damped_evaluation_target_eq := rfl
  damped_evaluation_target_proved :=
    dampedDirichletEvaluationTarget
  arctan_atTop_used := True.intro
  high_damping_error_vanishing_used := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  dirichlet_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS237. -/
def CorrectedFubiniExecutionAssemblyTarget : Prop :=
  Nonempty CorrectedFubiniExecutionAssemblyLedger

/-- TS237 target: the corrected Fubini execution and damped evaluation are proved. -/
theorem correctedFubiniExecutionAssemblyTarget :
    CorrectedFubiniExecutionAssemblyTarget :=
  Nonempty.intro correctedFubiniExecutionAssemblyLedger

end Goldbach
end TS237
