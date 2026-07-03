import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS218.SincFourthScalingEvennessDischarge

namespace TS219
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS219 - Cos-Square Triple IPP Cutoff Reformulation

TS217 corrected the Dirichlet sine-integral side of the direct `sinc^4` route:
the value `int_0^infty sin(a*x)/x dx = pi/2` must be treated as a cutoff or
Abel improper value, not as a Lebesgue integral over the half-line.

The same issue affects the TS213 triple-IPP statement.  Its right-hand side is
the Lebesgue integral of

`(-2 * sin x + 4 * sin (2*x)) / x`,

which is another conditionally convergent Dirichlet-type expression.  This
sprint archives that old Lebesgue statement as a legacy target and records the
correct cutoff formulation:

* finite triple IPP on `[eps, T]`;
* explicit boundary terms;
* vanishing of those boundary terms as `eps -> 0+` and `T -> +infty`;
* cutoff value `pi` for the third-derivative kernel;
* a fail-closed bridge from these inputs to
  `TS213.Goldbach.CosSquareIntegralValueStatement`.

TS219 does not prove the finite IPP, boundary vanishing, cutoff value, or final
cos-square value.  It only reformulates the target correctly.
-/

/-- Status markers for the TS219 triple-IPP reformulation. -/
inductive CosSquareTripleIPPReformulationStatus where
  /-- The old TS213 Lebesgue triple-IPP statement is retained only as legacy. -/
  | lebesgueTargetArchived
  /-- The corrected cutoff route is selected as the future target. -/
  | cutoffRouteSelected
  /-- The old Lebesgue target is not used as the final route. -/
  | lebesgueTargetNotFinal
  deriving DecidableEq, Repr

/-- The legacy Lebesgue triple-IPP target inherited from TS213. -/
def LegacyCosSquareTripleIPPLebesgueStatement :
    Prop :=
  TS213.Goldbach.CosSquareTripleIPPStatement

/--
The product cutoff filter `(eps, T) -> (0+, +infty)`.

The first coordinate tends to zero within the positive half-line and the second
coordinate tends to `atTop`.
-/
noncomputable def cosSquareCutoffFilter :
    Filter (Prod Real Real) :=
  Filter.prod
    (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
    atTop

/-- First boundary term produced by the triple IPP. -/
noncomputable def cosSquareTripleIPPBoundaryTerm1
    (x : Real) :
    Real :=
  -(TS213.Goldbach.cosSquareRemainder x / (3 * x ^ 3))

/-- Second boundary term produced by the triple IPP. -/
noncomputable def cosSquareTripleIPPBoundaryTerm2
    (x : Real) :
    Real :=
  -(((1 - Real.cos x) * Real.sin x) / (3 * x ^ 2))

/-- Third boundary term produced by the triple IPP. -/
noncomputable def cosSquareTripleIPPBoundaryTerm3
    (x : Real) :
    Real :=
  -((1 + Real.cos x - 2 * Real.cos x ^ 2) / (3 * x))

/-- Boundary jump `[b]_eps^T = b(T) - b(eps)`. -/
noncomputable def boundaryJump
    (b : Real -> Real)
    (eps T : Real) :
    Real :=
  b T - b eps

/-- Sum of the three boundary jumps in the cutoff triple IPP. -/
noncomputable def cosSquareTripleIPPBoundarySum
    (eps T : Real) :
    Real :=
  boundaryJump cosSquareTripleIPPBoundaryTerm1 eps T +
    boundaryJump cosSquareTripleIPPBoundaryTerm2 eps T +
      boundaryJump cosSquareTripleIPPBoundaryTerm3 eps T

/-- The left cutoff integral tends to the existing Lebesgue value. -/
def CosSquareImproperCutoffConvergenceStatement :
    Prop :=
  Tendsto
    (fun p : Prod Real Real =>
      intervalIntegral
        (fun x : Real => TS213.Goldbach.cosSquareHaarKernel x)
        p.1
        p.2
        volume)
    cosSquareCutoffFilter
    (nhds TS213.Goldbach.cosSquareImproperIntegral)

/--
The finite-interval triple IPP statement on `[eps, T]`.

This is the future purely finite calculus identity; no improper convergence is
hidden inside it.
-/
def CosSquareFiniteTripleIPPStatement :
    Prop :=
  forall eps T : Real,
    0 < eps ->
      eps < T ->
        intervalIntegral
          (fun x : Real => TS213.Goldbach.cosSquareHaarKernel x)
          eps
          T
          volume =
        (1 / 6 : Real) *
          intervalIntegral
            (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
            eps
            T
            volume +
          cosSquareTripleIPPBoundarySum eps T

/-- The boundary sum tends to zero along the product cutoff filter. -/
def CosSquareBoundaryVanishingStatement :
    Prop :=
  Tendsto
    (fun p : Prod Real Real =>
      cosSquareTripleIPPBoundarySum p.1 p.2)
    cosSquareCutoffFilter
    (nhds (0 : Real))

/--
Correct cutoff value of the third-derivative kernel.

The expected value is `pi`, not `pi/2`: formally it corresponds to
`-2*(pi/2) + 4*(pi/2) = pi` once the Dirichlet cutoff values at frequencies
`1` and `2` are supplied.
-/
def CosSquareThirdDerivativeCutoffValueStatement :
    Prop :=
  Tendsto
    (fun p : Prod Real Real =>
      intervalIntegral
        (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
        p.1
        p.2
        volume)
    cosSquareCutoffFilter
    (nhds Real.pi)

/--
Corrected cutoff bridge from the finite IPP route to the cos-square value.

This remains an explicit future obligation: TS219 names the corrected route but
does not prove the limiting assembly.
-/
def CosSquareTripleIPPCutoffAssemblyStatement :
    Prop :=
  CosSquareImproperCutoffConvergenceStatement ->
    CosSquareFiniteTripleIPPStatement ->
      CosSquareBoundaryVanishingStatement ->
        CosSquareThirdDerivativeCutoffValueStatement ->
          TS213.Goldbach.CosSquareIntegralValueStatement

/-- Fail-closed bridge package for the corrected triple-IPP route. -/
structure CosSquareTripleIPPCutoffBridge where
  assembly :
    CosSquareTripleIPPCutoffAssemblyStatement

/-- Evidence package for the corrected cutoff triple-IPP route. -/
structure CosSquareTripleIPPCutoffEvidence where
  improper_cutoff_convergence :
    CosSquareImproperCutoffConvergenceStatement

  finite_triple_ipp :
    CosSquareFiniteTripleIPPStatement

  boundary_vanishing :
    CosSquareBoundaryVanishingStatement

  third_derivative_cutoff_value :
    CosSquareThirdDerivativeCutoffValueStatement

  cutoff_bridge :
    CosSquareTripleIPPCutoffBridge

/-- The corrected triple-IPP target exposed by TS219. -/
def CorrectedCosSquareTripleIPPTarget :
    Prop :=
  Nonempty CosSquareTripleIPPCutoffEvidence

/-- Cutoff evidence supplies the corrected TS219 triple-IPP target. -/
theorem correctedCosSquareTripleIPPTarget_of_cutoffEvidence
    (evidence : CosSquareTripleIPPCutoffEvidence) :
    CorrectedCosSquareTripleIPPTarget :=
  Nonempty.intro evidence

/--
If all corrected cutoff evidence and the assembly bridge are supplied, the
cos-square value statement follows.
-/
theorem cosSquareIntegralValue_of_cutoffEvidence
    (evidence : CosSquareTripleIPPCutoffEvidence) :
    TS213.Goldbach.CosSquareIntegralValueStatement :=
  evidence.cutoff_bridge.assembly
    evidence.improper_cutoff_convergence
    evidence.finite_triple_ipp
    evidence.boundary_vanishing
    evidence.third_derivative_cutoff_value

/-- The TS219 legacy triple-IPP target is exactly the old TS213 target. -/
theorem legacyCosSquareTripleIPPLebesgueStatement_eq_ts213 :
    LegacyCosSquareTripleIPPLebesgueStatement =
      TS213.Goldbach.CosSquareTripleIPPStatement := by
  rfl

/-- Ledger recording the TS219 cutoff reformulation. -/
structure CosSquareTripleIPPCutoffReformulationLedger where
  ts218_scaling_evenness :
    TS218.Goldbach.SincFourthScalingEvennessDischargeLedger

  lebesgue_status :
    CosSquareTripleIPPReformulationStatus

  lebesgue_status_eq :
    lebesgue_status =
      CosSquareTripleIPPReformulationStatus.lebesgueTargetArchived

  cutoff_status :
    CosSquareTripleIPPReformulationStatus

  cutoff_status_eq :
    cutoff_status =
      CosSquareTripleIPPReformulationStatus.cutoffRouteSelected

  lebesgue_final_status :
    CosSquareTripleIPPReformulationStatus

  lebesgue_final_status_eq :
    lebesgue_final_status =
      CosSquareTripleIPPReformulationStatus.lebesgueTargetNotFinal

  legacy_lebesgue_statement :
    Prop

  legacy_lebesgue_statement_eq :
    legacy_lebesgue_statement =
      LegacyCosSquareTripleIPPLebesgueStatement

  improper_cutoff_convergence_statement :
    Prop

  improper_cutoff_convergence_statement_eq :
    improper_cutoff_convergence_statement =
      CosSquareImproperCutoffConvergenceStatement

  finite_triple_ipp_statement :
    Prop

  finite_triple_ipp_statement_eq :
    finite_triple_ipp_statement =
      CosSquareFiniteTripleIPPStatement

  boundary_vanishing_statement :
    Prop

  boundary_vanishing_statement_eq :
    boundary_vanishing_statement =
      CosSquareBoundaryVanishingStatement

  third_derivative_cutoff_value_statement :
    Prop

  third_derivative_cutoff_value_statement_eq :
    third_derivative_cutoff_value_statement =
      CosSquareThirdDerivativeCutoffValueStatement

  cutoff_assembly_statement :
    Prop

  cutoff_assembly_statement_eq :
    cutoff_assembly_statement =
      CosSquareTripleIPPCutoffAssemblyStatement

  corrected_triple_ipp_target :
    Prop

  corrected_triple_ipp_target_eq :
    corrected_triple_ipp_target =
      CorrectedCosSquareTripleIPPTarget

  cutoff_evidence_supplies_target :
    CosSquareTripleIPPCutoffEvidence ->
      CorrectedCosSquareTripleIPPTarget

  cutoff_evidence_supplies_cos_square_value :
    CosSquareTripleIPPCutoffEvidence ->
      TS213.Goldbach.CosSquareIntegralValueStatement

  legacy_lebesgue_not_final :
    True

  finite_triple_ipp_not_proved :
    True

  boundary_vanishing_not_proved :
    True

  third_derivative_cutoff_value_not_proved :
    True

  cutoff_assembly_not_proved :
    True

  dirichlet_cutoff_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS219 cutoff reformulation ledger. -/
noncomputable def cosSquareTripleIPPCutoffReformulationLedger :
    CosSquareTripleIPPCutoffReformulationLedger where
  ts218_scaling_evenness :=
    TS218.Goldbach.sincFourthScalingEvennessDischargeLedger
  lebesgue_status :=
    CosSquareTripleIPPReformulationStatus.lebesgueTargetArchived
  lebesgue_status_eq := rfl
  cutoff_status :=
    CosSquareTripleIPPReformulationStatus.cutoffRouteSelected
  cutoff_status_eq := rfl
  lebesgue_final_status :=
    CosSquareTripleIPPReformulationStatus.lebesgueTargetNotFinal
  lebesgue_final_status_eq := rfl
  legacy_lebesgue_statement :=
    LegacyCosSquareTripleIPPLebesgueStatement
  legacy_lebesgue_statement_eq := rfl
  improper_cutoff_convergence_statement :=
    CosSquareImproperCutoffConvergenceStatement
  improper_cutoff_convergence_statement_eq := rfl
  finite_triple_ipp_statement :=
    CosSquareFiniteTripleIPPStatement
  finite_triple_ipp_statement_eq := rfl
  boundary_vanishing_statement :=
    CosSquareBoundaryVanishingStatement
  boundary_vanishing_statement_eq := rfl
  third_derivative_cutoff_value_statement :=
    CosSquareThirdDerivativeCutoffValueStatement
  third_derivative_cutoff_value_statement_eq := rfl
  cutoff_assembly_statement :=
    CosSquareTripleIPPCutoffAssemblyStatement
  cutoff_assembly_statement_eq := rfl
  corrected_triple_ipp_target :=
    CorrectedCosSquareTripleIPPTarget
  corrected_triple_ipp_target_eq := rfl
  cutoff_evidence_supplies_target :=
    correctedCosSquareTripleIPPTarget_of_cutoffEvidence
  cutoff_evidence_supplies_cos_square_value :=
    cosSquareIntegralValue_of_cutoffEvidence
  legacy_lebesgue_not_final := True.intro
  finite_triple_ipp_not_proved := True.intro
  boundary_vanishing_not_proved := True.intro
  third_derivative_cutoff_value_not_proved := True.intro
  cutoff_assembly_not_proved := True.intro
  dirichlet_cutoff_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS219. -/
def CosSquareTripleIPPCutoffReformulationTarget :
    Prop :=
  Nonempty CosSquareTripleIPPCutoffReformulationLedger

theorem cosSquareTripleIPPCutoffReformulationTarget :
    CosSquareTripleIPPCutoffReformulationTarget :=
  Nonempty.intro cosSquareTripleIPPCutoffReformulationLedger

end Goldbach
end TS219
