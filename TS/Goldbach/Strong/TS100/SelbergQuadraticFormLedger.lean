import Mathlib.Tactic
import TS.Goldbach.Strong.TS99.SelbergSieveWeightLedger

namespace TS100
namespace Goldbach

/-!
# TS100 - Selberg Quadratic Form Ledger

TS99 refines the final Brun-Titchmarsh input into Selberg weight data plus the
TS30 majorant, sieve, and budget obligations. This sprint opens the next layer:
the quadratic-form data expected to generate those weights and obligations.

No Selberg sieve theorem, Mobius inversion, quadratic-form diagonalization,
Brun-Titchmarsh theorem, or prime-count estimate is proved here. The hard
arithmetic content remains explicitly packaged as local ledgers.
-/

/--
Roadmap marker for the Selberg quadratic-form front.

The real mathematical data live in `SelbergQuadraticFormLedger` and
`SelbergQuadraticFormInfrastructure`.
-/
structure SelbergQuadraticFormRoadmap where
  divisor_algebra_required :
    True

  mobius_inversion_required :
    True

  quadratic_form_diagonalization_required :
    True

  budget_comparison_required :
    True

/-- Concrete roadmap marker for TS100. -/
def selbergQuadraticFormRoadmap :
    SelbergQuadraticFormRoadmap where
  divisor_algebra_required := True.intro
  mobius_inversion_required := True.intro
  quadratic_form_diagonalization_required := True.intro
  budget_comparison_required := True.intro

/--
Selberg quadratic-form ledger.

The field `weight` is the future Selberg weight sequence. The field
`quadraticKernel` is the future finite quadratic kernel controlling the Selberg
majorant. The remaining fields record the local algebraic obligations expected
before producing the TS99 Selberg-weight infrastructure.
-/
structure SelbergQuadraticFormLedger where
  level :
    Nat

  weight :
    Nat -> Rat

  support_bound :
    forall d : Nat,
      ((weight d = 0) -> False) ->
        d <= level

  weight_one :
    weight 1 = 1

  quadraticKernel :
    Nat -> Nat -> Rat

  finite_sum_ready :
    True

  mobius_inversion_ready :
    True

  nonnegative_quadratic_form_ready :
    True

  diagonalization_ready :
    True

  divisor_square_majorant_ready :
    True

/--
Selberg quadratic-form infrastructure sufficient to recover the TS99
Selberg-weight infrastructure.

The TS30 `sieve` and `budget` fields remain the hard Brun-Titchmarsh/Selberg
obligations. This sprint only records that a future quadratic-form proof should
produce them from the quadratic ledger.
-/
structure SelbergQuadraticFormInfrastructure where
  quadratic :
    SelbergQuadraticFormLedger

  weightLedger :
    TS99.Goldbach.SelbergSieveWeightLedger

  weight_agreement :
    forall d : Nat,
      weightLedger.weight d = quadratic.weight d

  majorant :
    TS30.Goldbach.SelbergIntervalMajorant

  sieve :
    TS30.Goldbach.SelbergSieveIntervalBound majorant

  budget :
    TS30.Goldbach.SelbergMajorantBudgetComparison majorant

  majorant_from_quadratic_ready :
    True

  sieve_from_quadratic_ready :
    True

  budget_from_diagonalization_ready :
    True

/-- Target proposition for the TS100 roadmap marker. -/
def SelbergQuadraticFormRoadmapTarget : Prop :=
  Nonempty SelbergQuadraticFormRoadmap

/-- Target proposition for raw Selberg quadratic-form data. -/
def SelbergQuadraticFormLedgerTarget : Prop :=
  Nonempty SelbergQuadraticFormLedger

/-- Target proposition for the full Selberg quadratic-form infrastructure. -/
def SelbergQuadraticFormInfrastructureTarget : Prop :=
  Nonempty SelbergQuadraticFormInfrastructure

/-- The TS100 roadmap marker is populated. -/
theorem selbergQuadraticFormRoadmapTarget :
    SelbergQuadraticFormRoadmapTarget :=
  Nonempty.intro selbergQuadraticFormRoadmap

/--
Full quadratic-form infrastructure supplies the TS99 Selberg-weight
infrastructure.
-/
def selbergSieveWeightInfrastructure_of_quadraticFormInfrastructure
    (H : SelbergQuadraticFormInfrastructure) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure where
  weights := H.weightLedger
  majorant := H.majorant
  sieve := H.sieve
  budget := H.budget
  majorant_from_weights_ready := True.intro

/--
A quadratic-form infrastructure target supplies the TS99 Selberg-weight
infrastructure target.
-/
theorem selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget
    (H : SelbergQuadraticFormInfrastructureTarget) :
    TS99.Goldbach.SelbergSieveWeightInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (selbergSieveWeightInfrastructure_of_quadraticFormInfrastructure h)

/--
Quadratic-form infrastructure supplies the TS97 final Brun-Titchmarsh input
target through TS99.
-/
theorem brunTitchmarshFinalInputLedgerTarget_of_quadraticFormInfrastructureTarget
    (H : SelbergQuadraticFormInfrastructureTarget) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget :=
  TS99.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_weightInfrastructureTarget
    (selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget H)

/--
Quadratic-form infrastructure plus the TS95 trace ledger and TS83 Mellin-tail
contracts supply the TS98 final root input package.
-/
theorem finalHorizonInputsTarget_of_selbergQuadratic_trace_mellin
    (Hs : SelbergQuadraticFormInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS99.Goldbach.finalHorizonInputsTarget_of_selbergWeight_trace_mellin
    (selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Quadratic-form infrastructure plus the TS95 trace ledger and TS83 Mellin-tail
contracts feed the TS84 padded final API route through TS99.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_selbergQuadratic_trace_mellin
    (Hs : SelbergQuadraticFormInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS99.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergWeight_trace_mellin
    (selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Quadratic-form infrastructure plus the TS95 trace ledger and TS83 Mellin-tail
contracts feed the full TS25 padded-scale infrastructure through TS99.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_selbergQuadratic_trace_mellin
    (Hs : SelbergQuadraticFormInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS99.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergWeight_trace_mellin
    (selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS100
