import Mathlib.Tactic
import TS.Goldbach.Strong.TS95.ExplicitFormulaTraceBridgeLedger
import TS.Goldbach.Strong.TS160.SelbergPhiDenominatorCandidate

namespace TS161
namespace Goldbach

/-!
# TS161 - Phi Premortem and Spectral Pivot Ledger

TS160 shows that the phi denominator candidate escapes the old TS154
`D < 2` barrier.  This sprint records the next architectural fact: the phi
candidate cannot reuse the TS149 error-envelope mechanism, because the crucial
Jordan-two absorption

`sigma_1(d) <= J2(d)`

has no phi analogue.  In fact `sigma_1(2) = 3` while `phi(2) = 1`.

TS161 therefore archives the phi candidate as a useful probe rather than a
completed repair, and opens the spectral trace pivot by pointing back to the
TS94/TS95 roadmap ledgers.
-/

/-- The divisor-mass side at `2` is `3`. -/
theorem sigmaOne_two_eq_three :
    (ArithmeticFunction.sigma 1 2 : Rat) = 3 := by
  native_decide

/-- Euler's totient at `2` is `1`, viewed in `Rat`. -/
theorem totient_two_eq_one_rat :
    (Nat.totient 2 : Rat) = 1 := by
  native_decide

/-- The TS149-style absorption inequality fails for `phi` already at `2`. -/
theorem sigmaOne_two_gt_totient_two :
    (Nat.totient 2 : Rat) < (ArithmeticFunction.sigma 1 2 : Rat) := by
  native_decide

/--
There is no global positive-level inequality `sigma_1(d) <= phi(d)`.

This is the formal local obstruction to reusing the TS149 divisor-envelope
refinement with the TS160 phi denominator.
-/
theorem not_sigmaOne_le_totient_on_positive_levels :
    Not
      (forall d : Nat,
        0 < d ->
          (ArithmeticFunction.sigma 1 d : Rat) <=
            (Nat.totient d : Rat)) := by
  intro h
  have hle := h 2 (by norm_num)
  have hlt := sigmaOne_two_gt_totient_two
  linarith

/-- Named causes in the TS161 pre-mortem ledger. -/
inductive PhiPremortemCause where
  | divisorMassNotAbsorbedByTotient
  | goldbachDimensionRequiresSeparateInterface
  | scaleBottleneckRequiresSeparateAnalysis
  deriving DecidableEq, Repr

/-- Named spectral fronts opened after archiving the phi probe. -/
inductive SpectralPivotFront where
  | traceKernelData
  | explicitFormulaBridge
  deriving DecidableEq, Repr

/--
Ledger for the phi pre-mortem and the spectral pivot.

The first obstruction is formalized as a theorem.  The dimension and scale
issues are recorded as design obligations, not as proved impossibility
theorems.
-/
structure PhiPremortemSpectralPivotLedger where
  phiCandidate :
    TS160.Goldbach.SelbergPhiDenominatorCandidateLedger

  phi_crosses_old_two_cap :
    (2 : Rat) < TS160.Goldbach.selbergPhiDenominator 3

  divisor_absorption_cause :
    PhiPremortemCause

  divisor_absorption_cause_eq :
    divisor_absorption_cause =
      PhiPremortemCause.divisorMassNotAbsorbedByTotient

  no_sigmaOne_le_totient :
    Not
      (forall d : Nat,
        0 < d ->
          (ArithmeticFunction.sigma 1 d : Rat) <=
            (Nat.totient d : Rat))

  goldbach_dimension_obligation :
    PhiPremortemCause

  goldbach_dimension_obligation_eq :
    goldbach_dimension_obligation =
      PhiPremortemCause.goldbachDimensionRequiresSeparateInterface

  scale_bottleneck_obligation :
    PhiPremortemCause

  scale_bottleneck_obligation_eq :
    scale_bottleneck_obligation =
      PhiPremortemCause.scaleBottleneckRequiresSeparateAnalysis

  trace_kernel_front :
    SpectralPivotFront

  trace_kernel_front_eq :
    trace_kernel_front = SpectralPivotFront.traceKernelData

  explicit_formula_front :
    SpectralPivotFront

  explicit_formula_front_eq :
    explicit_formula_front = SpectralPivotFront.explicitFormulaBridge

  trace_kernel_roadmap :
    TS94.Goldbach.TraceKernelSpectralDataRoadmapTarget

  explicit_formula_roadmap :
    TS95.Goldbach.ExplicitFormulaTraceBridgeRoadmapTarget

  no_claim_phi_is_universally_impossible :
    True

  no_concrete_spectral_kernel_supplied :
    True

/-- Concrete TS161 pre-mortem and pivot ledger. -/
def phiPremortemSpectralPivotLedger :
    PhiPremortemSpectralPivotLedger where
  phiCandidate := TS160.Goldbach.selbergPhiDenominatorCandidateLedger
  phi_crosses_old_two_cap :=
    TS160.Goldbach.selbergPhiDenominator_three_gt_two
  divisor_absorption_cause :=
    PhiPremortemCause.divisorMassNotAbsorbedByTotient
  divisor_absorption_cause_eq := rfl
  no_sigmaOne_le_totient := not_sigmaOne_le_totient_on_positive_levels
  goldbach_dimension_obligation :=
    PhiPremortemCause.goldbachDimensionRequiresSeparateInterface
  goldbach_dimension_obligation_eq := rfl
  scale_bottleneck_obligation :=
    PhiPremortemCause.scaleBottleneckRequiresSeparateAnalysis
  scale_bottleneck_obligation_eq := rfl
  trace_kernel_front := SpectralPivotFront.traceKernelData
  trace_kernel_front_eq := rfl
  explicit_formula_front := SpectralPivotFront.explicitFormulaBridge
  explicit_formula_front_eq := rfl
  trace_kernel_roadmap :=
    TS94.Goldbach.traceKernelSpectralDataRoadmapTarget
  explicit_formula_roadmap :=
    TS95.Goldbach.explicitFormulaTraceBridgeRoadmapTarget
  no_claim_phi_is_universally_impossible := True.intro
  no_concrete_spectral_kernel_supplied := True.intro

/-- Target proposition for TS161. -/
def PhiPremortemSpectralPivotTarget : Prop :=
  Nonempty PhiPremortemSpectralPivotLedger

/-- The TS161 phi pre-mortem and spectral-pivot target is populated. -/
theorem phiPremortemSpectralPivotTarget :
    PhiPremortemSpectralPivotTarget :=
  Nonempty.intro phiPremortemSpectralPivotLedger

end Goldbach
end TS161
