import Mathlib.Tactic
import TS.Goldbach.Strong.TS94.TraceKernelSpectralDataLedger

namespace TS95
namespace Goldbach

/-!
# TS95 - Explicit Formula Trace Bridge Ledger

TS92 names an `ExplicitFormulaTraceBridge` component. TS93 supplies the
zero-family ledger and TS94 supplies the trace-kernel ledger. This sprint
connects those two sides by recording the local explicit-formula obligations:
the non-trivial zero contribution, the pole/trivial-zero/contour residuals,
and the rational trace budget expected from the future analytic proof.

No Riemann-von Mangoldt explicit formula is proved here. The analytic theorem
remains the local contract `ExplicitFormulaTraceBridgeLedger`.
-/

/-- Contribution of the non-trivial zeta zeros to the trace side. -/
structure NontrivialZeroTraceContribution where
  value :
    Rat

  nonneg :
    0 <= value

/--
Residual terms in the explicit formula: the pole at `s = 1`, trivial zeros,
and contour/error terms.
-/
structure ExplicitFormulaResidualTerms where
  poleTerm :
    Rat

  trivialZeroTerm :
    Rat

  contourError :
    Rat

  pole_nonneg :
    0 <= poleTerm

  trivial_nonneg :
    0 <= trivialZeroTerm

  contour_nonneg :
    0 <= contourError

namespace ExplicitFormulaResidualTerms

/-- Total residual budget carried by the explicit-formula ledger. -/
def total
    (R : ExplicitFormulaResidualTerms) :
    Rat :=
  R.poleTerm + R.trivialZeroTerm + R.contourError

end ExplicitFormulaResidualTerms

/--
Explicit-formula bridge ledger.

The ledger ties a concrete zero-family ledger and a concrete kernel ledger to a
rational trace budget. The final `traceBudget_le_half` field is the numerical
side needed later to assemble the `Ct <= 1/2` spectral trace majorant.
-/
structure ExplicitFormulaTraceBridgeLedger where
  zeroFamily :
    TS93.Goldbach.ZetaZeroFamilyLedger

  kernelData :
    TS94.Goldbach.TraceKernelSpectralDataLedger

  zeroContribution :
    NontrivialZeroTraceContribution

  residuals :
    ExplicitFormulaResidualTerms

  traceBudget :
    Rat

  traceBudget_pos :
    0 < traceBudget

  traceBudget_le_half :
    traceBudget <= 1 / 2

  explicit_formula_comparison_ready :
    True

  zero_sum_trace_bridge_ready :
    True

  residual_error_control_ready :
    True

  trace_budget_controls_formula :
    zeroContribution.value + ExplicitFormulaResidualTerms.total residuals <=
      traceBudget

/--
Roadmap ledger for the explicit-formula bridge front.

This records the API state only. It is populated unconditionally because the
real analytic estimate remains in `ExplicitFormulaTraceBridgeLedger`.
-/
structure ExplicitFormulaTraceBridgeRoadmap where
  zero_contribution_required :
    True

  pole_term_required :
    True

  trivial_zero_term_required :
    True

  contour_error_required :
    True

  rational_trace_budget_required :
    True

/-- Concrete roadmap ledger for TS95. -/
def explicitFormulaTraceBridgeRoadmap :
    ExplicitFormulaTraceBridgeRoadmap where
  zero_contribution_required := True.intro
  pole_term_required := True.intro
  trivial_zero_term_required := True.intro
  contour_error_required := True.intro
  rational_trace_budget_required := True.intro

/-- A concrete explicit-formula ledger supplies the coarser TS92 bridge marker. -/
def explicitFormulaTraceBridge_of_ledger
    (H : ExplicitFormulaTraceBridgeLedger) :
    TS92.Goldbach.ExplicitFormulaTraceBridge where
  von_mangoldt_formula_ready :=
    H.explicit_formula_comparison_ready
  zero_sum_trace_bridge_ready :=
    H.zero_sum_trace_bridge_ready
  residual_error_control_ready :=
    H.residual_error_control_ready

/-- Target proposition for the roadmap ledger. -/
def ExplicitFormulaTraceBridgeRoadmapTarget : Prop :=
  Nonempty ExplicitFormulaTraceBridgeRoadmap

/-- Target proposition for the concrete explicit-formula bridge ledger. -/
def ExplicitFormulaTraceBridgeLedgerTarget : Prop :=
  Nonempty ExplicitFormulaTraceBridgeLedger

/-- Local target for the TS92 explicit-formula bridge component. -/
def ExplicitFormulaTraceBridgeTarget : Prop :=
  Nonempty TS92.Goldbach.ExplicitFormulaTraceBridge

/-- The TS95 explicit-formula roadmap ledger is populated. -/
theorem explicitFormulaTraceBridgeRoadmapTarget :
    ExplicitFormulaTraceBridgeRoadmapTarget :=
  Nonempty.intro explicitFormulaTraceBridgeRoadmap

/-- A concrete explicit-formula ledger supplies the TS92 bridge target. -/
theorem explicitFormulaTraceBridgeTarget_of_ledgerTarget
    (H : ExplicitFormulaTraceBridgeLedgerTarget) :
    ExplicitFormulaTraceBridgeTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (explicitFormulaTraceBridge_of_ledger h)

/-- A concrete explicit-formula ledger supplies the TS93 zero-family target. -/
theorem zetaZeroFamilyLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget
    (H : ExplicitFormulaTraceBridgeLedgerTarget) :
    TS93.Goldbach.ZetaZeroFamilyLedgerTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.zeroFamily

/-- A concrete explicit-formula ledger supplies the TS94 kernel-data target. -/
theorem traceKernelSpectralDataLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget
    (H : ExplicitFormulaTraceBridgeLedgerTarget) :
    TS94.Goldbach.TraceKernelSpectralDataLedgerTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.kernelData

end Goldbach
end TS95
