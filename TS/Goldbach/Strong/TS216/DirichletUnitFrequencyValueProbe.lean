import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS215.DirichletSineIntegralAPIProbe

namespace TS216
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS216 - Dirichlet Unit-Frequency Value Probe

TS215 split the TS213 positive-frequency Dirichlet sine integral into a
unit-frequency value and a positive-frequency scaling statement.  TS216 probes
the unit-frequency side.

The bundled Mathlib API does not expose a ready-made theorem for
`integral_0^infty sin x / x = pi / 2` under the names checked in TS215.  This
sprint therefore keeps the current TS215 Lebesgue-integral target as an explicit
open statement, records two more natural future formulations for a conditional
Dirichlet integral (cutoff improper convergence and Abel regularization), and
proves the pointwise simplification of the project kernel at frequency `1`.

No Dirichlet value, cutoff convergence, Abel theorem, improper IPP, Plancherel,
or Goldbach theorem is claimed.
-/

/-- Status of the unit-frequency Dirichlet value probe. -/
inductive DirichletUnitFrequencyProbeStatus where
  /-- No ready-made local Mathlib value theorem was located. -/
  | readyMadeValueNotLocated
  /-- The current TS215 Lebesgue-target statement is explicitly named. -/
  | lebesgueTargetSpecified
  /-- A cutoff-improper convergence target is explicitly named. -/
  | cutoffImproperTargetSpecified
  /-- An Abel-regularized convergence target is explicitly named. -/
  | abelRegularizedTargetSpecified
  /-- The frequency-one kernel was simplified to `sin x / x`. -/
  | unitKernelIdentified
  deriving DecidableEq, Repr

/-- The current TS215 unit-frequency Lebesgue target. -/
def DirichletUnitFrequencyLebesgueStatement :
    Prop :=
  TS215.Goldbach.DirichletUnitFrequencyStatement

/--
The cutoff-improper unit-frequency Dirichlet target.

This is the classical conditional-integral shape:
`int_0^R sin x / x dx -> pi/2` as `R -> infinity`.
-/
def DirichletUnitFrequencyCutoffStatement :
    Prop :=
  Tendsto
    (fun R : Real =>
      intervalIntegral
        (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
        0
        R
        volume)
    atTop
    (nhds (Real.pi / 2))

/--
The Abel-regularized unit-frequency Dirichlet target.

This names the standard damping route:
`int_0^infty exp(-eps*x) * sin x / x dx -> pi/2` as `eps -> 0+`.
-/
def DirichletUnitFrequencyAbelStatement :
    Prop :=
  Tendsto
    (fun eps : Real =>
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (fun x : Real =>
          Real.exp (-(eps * x)) *
            TS213.Goldbach.sineDirichletKernel 1 x))
    (nhdsWithin 0 (Set.Ioi (0 : Real)))
    (nhds (Real.pi / 2))

/-- At frequency `1`, the TS213 Dirichlet kernel is the usual `sin x / x`. -/
theorem unitFrequencyKernel_eq_sin_div
    (x : Real) :
    TS213.Goldbach.sineDirichletKernel 1 x =
      Real.sin x / x := by
  simp [TS213.Goldbach.sineDirichletKernel]

/-- The TS216 Lebesgue target is exactly the TS215 unit-frequency target. -/
theorem dirichletUnitFrequencyLebesgueStatement_eq_ts215 :
    DirichletUnitFrequencyLebesgueStatement =
      TS215.Goldbach.DirichletUnitFrequencyStatement := by
  rfl

/--
The TS213 positive-frequency Dirichlet slot still follows from the TS216
unit-frequency Lebesgue target plus the TS215 positive-frequency scaling slot.
-/
theorem dirichletSineIntegral_of_unitLebesgue_and_scaling
    (h_unit :
      DirichletUnitFrequencyLebesgueStatement)
    (h_scaling :
      TS215.Goldbach.DirichletPositiveFrequencyScalingStatement) :
    TS213.Goldbach.DirichletSineIntegralStatement :=
  TS215.Goldbach.dirichletSineIntegral_of_unitValue_and_scaling
    h_unit
    h_scaling

/-- Ledger recording the TS216 unit-frequency value probe. -/
structure DirichletUnitFrequencyValueProbeLedger where
  ts215_api_probe :
    TS215.Goldbach.DirichletSineIntegralAPIProbeLedger

  ready_made_value_status :
    DirichletUnitFrequencyProbeStatus

  ready_made_value_status_eq :
    ready_made_value_status =
      DirichletUnitFrequencyProbeStatus.readyMadeValueNotLocated

  lebesgue_target_status :
    DirichletUnitFrequencyProbeStatus

  lebesgue_target_status_eq :
    lebesgue_target_status =
      DirichletUnitFrequencyProbeStatus.lebesgueTargetSpecified

  cutoff_target_status :
    DirichletUnitFrequencyProbeStatus

  cutoff_target_status_eq :
    cutoff_target_status =
      DirichletUnitFrequencyProbeStatus.cutoffImproperTargetSpecified

  abel_target_status :
    DirichletUnitFrequencyProbeStatus

  abel_target_status_eq :
    abel_target_status =
      DirichletUnitFrequencyProbeStatus.abelRegularizedTargetSpecified

  unit_kernel_status :
    DirichletUnitFrequencyProbeStatus

  unit_kernel_status_eq :
    unit_kernel_status =
      DirichletUnitFrequencyProbeStatus.unitKernelIdentified

  lebesgue_statement :
    Prop

  lebesgue_statement_eq :
    lebesgue_statement = DirichletUnitFrequencyLebesgueStatement

  cutoff_statement :
    Prop

  cutoff_statement_eq :
    cutoff_statement = DirichletUnitFrequencyCutoffStatement

  abel_statement :
    Prop

  abel_statement_eq :
    abel_statement = DirichletUnitFrequencyAbelStatement

  unit_kernel_identification :
    forall x : Real,
      TS213.Goldbach.sineDirichletKernel 1 x =
        Real.sin x / x

  unit_lebesgue_and_scaling_imply_ts213_dirichlet :
    lebesgue_statement ->
      TS215.Goldbach.DirichletPositiveFrequencyScalingStatement ->
        TS213.Goldbach.DirichletSineIntegralStatement

  lebesgue_dirichlet_value_not_proved :
    True

  cutoff_improper_dirichlet_value_not_proved :
    True

  abel_regularized_dirichlet_value_not_proved :
    True

  positive_frequency_scaling_not_proved :
    True

  ts213_dirichlet_statement_not_proved :
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

/-- Concrete TS216 unit-frequency value probe ledger. -/
noncomputable def dirichletUnitFrequencyValueProbeLedger :
    DirichletUnitFrequencyValueProbeLedger where
  ts215_api_probe :=
    TS215.Goldbach.dirichletSineIntegralAPIProbeLedger
  ready_made_value_status :=
    DirichletUnitFrequencyProbeStatus.readyMadeValueNotLocated
  ready_made_value_status_eq := rfl
  lebesgue_target_status :=
    DirichletUnitFrequencyProbeStatus.lebesgueTargetSpecified
  lebesgue_target_status_eq := rfl
  cutoff_target_status :=
    DirichletUnitFrequencyProbeStatus.cutoffImproperTargetSpecified
  cutoff_target_status_eq := rfl
  abel_target_status :=
    DirichletUnitFrequencyProbeStatus.abelRegularizedTargetSpecified
  abel_target_status_eq := rfl
  unit_kernel_status :=
    DirichletUnitFrequencyProbeStatus.unitKernelIdentified
  unit_kernel_status_eq := rfl
  lebesgue_statement :=
    DirichletUnitFrequencyLebesgueStatement
  lebesgue_statement_eq := rfl
  cutoff_statement :=
    DirichletUnitFrequencyCutoffStatement
  cutoff_statement_eq := rfl
  abel_statement :=
    DirichletUnitFrequencyAbelStatement
  abel_statement_eq := rfl
  unit_kernel_identification :=
    unitFrequencyKernel_eq_sin_div
  unit_lebesgue_and_scaling_imply_ts213_dirichlet :=
    dirichletSineIntegral_of_unitLebesgue_and_scaling
  lebesgue_dirichlet_value_not_proved := True.intro
  cutoff_improper_dirichlet_value_not_proved := True.intro
  abel_regularized_dirichlet_value_not_proved := True.intro
  positive_frequency_scaling_not_proved := True.intro
  ts213_dirichlet_statement_not_proved := True.intro
  improper_triple_ipp_not_proved := True.intro
  sinc_fourth_scaling_not_proved := True.intro
  sinc_fourth_evenness_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  plancherel_not_used := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS216. -/
def DirichletUnitFrequencyValueProbeTarget :
    Prop :=
  Nonempty DirichletUnitFrequencyValueProbeLedger

/-- The TS216 unit-frequency value-probe target is populated. -/
theorem dirichletUnitFrequencyValueProbeTarget :
    DirichletUnitFrequencyValueProbeTarget :=
  Nonempty.intro dirichletUnitFrequencyValueProbeLedger

end Goldbach
end TS216
