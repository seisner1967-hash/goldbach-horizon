import Mathlib.Tactic
import TS.Goldbach.Strong.TS216.DirichletUnitFrequencyValueProbe

namespace TS217
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS217 - Dirichlet Improper Reformulation Bridge

TS213 originally recorded the Dirichlet sine integral with a Lebesgue integral
over `(0, infinity)`.  TS215 and TS216 made the issue visible: the mathematically
useful Dirichlet value is a conditionally convergent improper value, so the
future route should use cutoff convergence or Abel regularization instead of
treating the Lebesgue target as the final analytic statement.

This sprint performs that fail-closed reformulation.  It archives the current
Lebesgue statement as a legacy target, promotes cutoff and Abel formulations to
the official future targets, and keeps the old TS213 Lebesgue slot explicitly
unproved and not consumed.

No non-integrability theorem, Dirichlet value, cutoff convergence, Abel theorem,
improper IPP, Plancherel theorem, or Goldbach theorem is claimed.
-/

/-- Status markers for the TS217 Dirichlet reformulation. -/
inductive DirichletImproperReformulationStatus where
  /-- The old Lebesgue formulation is retained only as a legacy target. -/
  | lebesgueTargetArchived
  /-- Cutoff-improper convergence is selected as an official future target. -/
  | cutoffRouteSelected
  /-- Abel regularization is selected as an official future target. -/
  | abelRouteSelected
  /-- The old Lebesgue target is not used as the final route. -/
  | lebesgueTargetNotFinal
  deriving DecidableEq, Repr

/-- The legacy unit-frequency Lebesgue target inherited from TS216. -/
def LegacyDirichletUnitFrequencyLebesgueStatement :
    Prop :=
  TS216.Goldbach.DirichletUnitFrequencyLebesgueStatement

/-- The unit-frequency cutoff-improper target inherited from TS216. -/
def DirichletUnitFrequencyCutoffTarget :
    Prop :=
  TS216.Goldbach.DirichletUnitFrequencyCutoffStatement

/-- The unit-frequency Abel-regularized target inherited from TS216. -/
def DirichletUnitFrequencyAbelTarget :
    Prop :=
  TS216.Goldbach.DirichletUnitFrequencyAbelStatement

/--
The positive-frequency cutoff-improper Dirichlet target.

This is the intended replacement for the old Lebesgue all-frequency TS213 slot
when the proof is run by cutoffs.
-/
def DirichletPositiveFrequencyCutoffStatement :
    Prop :=
  forall a : Real,
    0 < a ->
      Tendsto
        (fun R : Real =>
          intervalIntegral
            (fun x : Real => TS213.Goldbach.sineDirichletKernel a x)
            0
            R
            volume)
        atTop
        (nhds (Real.pi / 2))

/--
The positive-frequency Abel-regularized Dirichlet target.

This is the intended replacement for the old Lebesgue all-frequency TS213 slot
when the proof is run through Abel damping.
-/
def DirichletPositiveFrequencyAbelStatement :
    Prop :=
  forall a : Real,
    0 < a ->
      Tendsto
        (fun eps : Real =>
          integral
            (volume.restrict (Set.Ioi (0 : Real)))
            (fun x : Real =>
              Real.exp (-(eps * x)) *
                TS213.Goldbach.sineDirichletKernel a x))
        (nhdsWithin 0 (Set.Ioi (0 : Real)))
        (nhds (Real.pi / 2))

/-- Evidence wrapper for the cutoff-improper Dirichlet route. -/
structure DirichletCutoffEvidence where
  unit_cutoff_value :
    DirichletUnitFrequencyCutoffTarget

  positive_frequency_cutoff :
    DirichletPositiveFrequencyCutoffStatement

/-- Evidence wrapper for the Abel-regularized Dirichlet route. -/
structure DirichletAbelEvidence where
  unit_abel_value :
    DirichletUnitFrequencyAbelTarget

  positive_frequency_abel :
    DirichletPositiveFrequencyAbelStatement

/-- A corrected Dirichlet route may be supplied by cutoffs or by Abel damping. -/
inductive DirichletImproperRouteEvidence where
  | cutoff : DirichletCutoffEvidence -> DirichletImproperRouteEvidence
  | abel : DirichletAbelEvidence -> DirichletImproperRouteEvidence

/-- The corrected all-frequency Dirichlet target exposed by TS217. -/
def CorrectedDirichletSineIntegralTarget :
    Prop :=
  Nonempty DirichletImproperRouteEvidence

/-- Cutoff evidence supplies the corrected TS217 target. -/
theorem correctedDirichletTarget_of_cutoffEvidence
    (evidence : DirichletCutoffEvidence) :
    CorrectedDirichletSineIntegralTarget :=
  Nonempty.intro (DirichletImproperRouteEvidence.cutoff evidence)

/-- Abel evidence supplies the corrected TS217 target. -/
theorem correctedDirichletTarget_of_abelEvidence
    (evidence : DirichletAbelEvidence) :
    CorrectedDirichletSineIntegralTarget :=
  Nonempty.intro (DirichletImproperRouteEvidence.abel evidence)

/-- The TS217 legacy Lebesgue target is exactly the TS216 Lebesgue target. -/
theorem legacyDirichletUnitFrequencyLebesgueStatement_eq_ts216 :
    LegacyDirichletUnitFrequencyLebesgueStatement =
      TS216.Goldbach.DirichletUnitFrequencyLebesgueStatement := by
  rfl

/-- The TS217 cutoff unit target is exactly the TS216 cutoff target. -/
theorem dirichletUnitFrequencyCutoffTarget_eq_ts216 :
    DirichletUnitFrequencyCutoffTarget =
      TS216.Goldbach.DirichletUnitFrequencyCutoffStatement := by
  rfl

/-- The TS217 Abel unit target is exactly the TS216 Abel target. -/
theorem dirichletUnitFrequencyAbelTarget_eq_ts216 :
    DirichletUnitFrequencyAbelTarget =
      TS216.Goldbach.DirichletUnitFrequencyAbelStatement := by
  rfl

/-- Ledger recording the TS217 improper reformulation bridge. -/
structure DirichletImproperReformulationLedger where
  ts216_unit_frequency_probe :
    TS216.Goldbach.DirichletUnitFrequencyValueProbeLedger

  lebesgue_status :
    DirichletImproperReformulationStatus

  lebesgue_status_eq :
    lebesgue_status =
      DirichletImproperReformulationStatus.lebesgueTargetArchived

  cutoff_status :
    DirichletImproperReformulationStatus

  cutoff_status_eq :
    cutoff_status =
      DirichletImproperReformulationStatus.cutoffRouteSelected

  abel_status :
    DirichletImproperReformulationStatus

  abel_status_eq :
    abel_status =
      DirichletImproperReformulationStatus.abelRouteSelected

  lebesgue_final_status :
    DirichletImproperReformulationStatus

  lebesgue_final_status_eq :
    lebesgue_final_status =
      DirichletImproperReformulationStatus.lebesgueTargetNotFinal

  legacy_lebesgue_statement :
    Prop

  legacy_lebesgue_statement_eq :
    legacy_lebesgue_statement =
      LegacyDirichletUnitFrequencyLebesgueStatement

  cutoff_unit_statement :
    Prop

  cutoff_unit_statement_eq :
    cutoff_unit_statement =
      DirichletUnitFrequencyCutoffTarget

  abel_unit_statement :
    Prop

  abel_unit_statement_eq :
    abel_unit_statement =
      DirichletUnitFrequencyAbelTarget

  cutoff_positive_frequency_statement :
    Prop

  cutoff_positive_frequency_statement_eq :
    cutoff_positive_frequency_statement =
      DirichletPositiveFrequencyCutoffStatement

  abel_positive_frequency_statement :
    Prop

  abel_positive_frequency_statement_eq :
    abel_positive_frequency_statement =
      DirichletPositiveFrequencyAbelStatement

  corrected_dirichlet_target :
    Prop

  corrected_dirichlet_target_eq :
    corrected_dirichlet_target =
      CorrectedDirichletSineIntegralTarget

  cutoff_evidence_supplies_corrected_target :
    DirichletCutoffEvidence ->
      corrected_dirichlet_target

  abel_evidence_supplies_corrected_target :
    DirichletAbelEvidence ->
      corrected_dirichlet_target

  lebesgue_statement_not_used_as_final_target :
    True

  cutoff_route_available_as_target :
    True

  abel_route_available_as_target :
    True

  lebesgue_nonintegrability_not_proved :
    True

  dirichlet_value_not_proved :
    True

  cutoff_convergence_not_proved :
    True

  abel_convergence_not_proved :
    True

  old_ts213_lebesgue_dirichlet_not_proved :
    True

  improper_triple_ipp_not_proved :
    True

  sinc_fourth_scaling_not_proved :
    True

  sinc_fourth_evenness_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved :
    True

  plancherel_not_used :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS217 improper reformulation ledger. -/
noncomputable def dirichletImproperReformulationLedger :
    DirichletImproperReformulationLedger where
  ts216_unit_frequency_probe :=
    TS216.Goldbach.dirichletUnitFrequencyValueProbeLedger
  lebesgue_status :=
    DirichletImproperReformulationStatus.lebesgueTargetArchived
  lebesgue_status_eq := rfl
  cutoff_status :=
    DirichletImproperReformulationStatus.cutoffRouteSelected
  cutoff_status_eq := rfl
  abel_status :=
    DirichletImproperReformulationStatus.abelRouteSelected
  abel_status_eq := rfl
  lebesgue_final_status :=
    DirichletImproperReformulationStatus.lebesgueTargetNotFinal
  lebesgue_final_status_eq := rfl
  legacy_lebesgue_statement :=
    LegacyDirichletUnitFrequencyLebesgueStatement
  legacy_lebesgue_statement_eq := rfl
  cutoff_unit_statement :=
    DirichletUnitFrequencyCutoffTarget
  cutoff_unit_statement_eq := rfl
  abel_unit_statement :=
    DirichletUnitFrequencyAbelTarget
  abel_unit_statement_eq := rfl
  cutoff_positive_frequency_statement :=
    DirichletPositiveFrequencyCutoffStatement
  cutoff_positive_frequency_statement_eq := rfl
  abel_positive_frequency_statement :=
    DirichletPositiveFrequencyAbelStatement
  abel_positive_frequency_statement_eq := rfl
  corrected_dirichlet_target :=
    CorrectedDirichletSineIntegralTarget
  corrected_dirichlet_target_eq := rfl
  cutoff_evidence_supplies_corrected_target :=
    correctedDirichletTarget_of_cutoffEvidence
  abel_evidence_supplies_corrected_target :=
    correctedDirichletTarget_of_abelEvidence
  lebesgue_statement_not_used_as_final_target := True.intro
  cutoff_route_available_as_target := True.intro
  abel_route_available_as_target := True.intro
  lebesgue_nonintegrability_not_proved := True.intro
  dirichlet_value_not_proved := True.intro
  cutoff_convergence_not_proved := True.intro
  abel_convergence_not_proved := True.intro
  old_ts213_lebesgue_dirichlet_not_proved := True.intro
  improper_triple_ipp_not_proved := True.intro
  sinc_fourth_scaling_not_proved := True.intro
  sinc_fourth_evenness_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  plancherel_not_used := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS217. -/
def DirichletImproperReformulationTarget :
    Prop :=
  Nonempty DirichletImproperReformulationLedger

/-- The TS217 improper-reformulation target is populated. -/
theorem dirichletImproperReformulationTarget :
    DirichletImproperReformulationTarget :=
  Nonempty.intro dirichletImproperReformulationLedger

end Goldbach
end TS217
