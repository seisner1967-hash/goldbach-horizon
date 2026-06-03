import Mathlib.Tactic
import TS.Goldbach.Strong.TS30.BrunTitchmarshSelbergRoadmap
import TS.Goldbach.Strong.TS98.FinalThreeObligationAssembly

namespace TS99
namespace Goldbach

/-!
# TS99 - Selberg Sieve Weight Ledger

TS97 isolates the final Brun-Titchmarsh input, and TS30 already shows that a
Selberg Brun-Titchmarsh infrastructure implies that input. This sprint opens
the next layer down: the Selberg weight data expected to generate the TS30
majorant, sieve bound, and budget comparison.

No Selberg sieve theorem, Mobius inversion, quadratic-form diagonalization, or
prime-count estimate is proved here. The analytic and arithmetic content
remains explicitly packaged as local ledgers.
-/

/--
Roadmap marker for the Selberg-weight front.

The real mathematical data live in `SelbergSieveWeightLedger` and
`SelbergSieveWeightInfrastructure`.
-/
structure SelbergSieveWeightRoadmap where
  finite_weight_support_required :
    True

  quadratic_form_required :
    True

  majorant_property_required :
    True

  budget_comparison_required :
    True

/-- Concrete roadmap marker for TS99. -/
def selbergSieveWeightRoadmap :
    SelbergSieveWeightRoadmap where
  finite_weight_support_required := True.intro
  quadratic_form_required := True.intro
  majorant_property_required := True.intro
  budget_comparison_required := True.intro

/--
Selberg weight ledger.

The field `weight` is the future Selberg weight sequence. The support and
normalization fields record the finite algebraic conditions expected before
building the interval majorant.
-/
structure SelbergSieveWeightLedger where
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

  finite_support_ready :
    True

  quadratic_form_ready :
    True

  divisor_sum_majorant_ready :
    True

/--
Selberg weight infrastructure sufficient to recover the TS30 Selberg roadmap.

The fields `sieve` and `budget` remain the hard Selberg/Brun-Titchmarsh
obligations; this sprint only packages them with the explicit weight data.
-/
structure SelbergSieveWeightInfrastructure where
  weights :
    SelbergSieveWeightLedger

  majorant :
    TS30.Goldbach.SelbergIntervalMajorant

  sieve :
    TS30.Goldbach.SelbergSieveIntervalBound majorant

  budget :
    TS30.Goldbach.SelbergMajorantBudgetComparison majorant

  majorant_from_weights_ready :
    True

/-- Target proposition for the TS99 roadmap marker. -/
def SelbergSieveWeightRoadmapTarget : Prop :=
  Nonempty SelbergSieveWeightRoadmap

/-- Target proposition for raw Selberg weight data. -/
def SelbergSieveWeightLedgerTarget : Prop :=
  Nonempty SelbergSieveWeightLedger

/-- Target proposition for the full Selberg-weight infrastructure. -/
def SelbergSieveWeightInfrastructureTarget : Prop :=
  Nonempty SelbergSieveWeightInfrastructure

/-- The TS99 roadmap marker is populated. -/
theorem selbergSieveWeightRoadmapTarget :
    SelbergSieveWeightRoadmapTarget :=
  Nonempty.intro selbergSieveWeightRoadmap

/--
Full Selberg-weight infrastructure supplies the TS30 Selberg Brun-Titchmarsh
infrastructure.
-/
def selbergBrunTitchmarshInfrastructure_of_weightInfrastructure
    (H : SelbergSieveWeightInfrastructure) :
    TS30.Goldbach.SelbergBrunTitchmarshInfrastructure where
  majorant := H.majorant
  sieve := H.sieve
  budget := H.budget

/--
Full Selberg-weight infrastructure supplies the TS97 final Brun-Titchmarsh
input ledger.
-/
noncomputable def brunTitchmarshFinalInputLedger_of_weightInfrastructure
    (H : SelbergSieveWeightInfrastructure) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger where
  bt :=
    TS30.Goldbach.brunTitchmarshNatIntervalBound_from_selberg
      (selbergBrunTitchmarshInfrastructure_of_weightInfrastructure H)

/--
A Selberg-weight infrastructure target supplies the TS97 final
Brun-Titchmarsh input target.
-/
theorem brunTitchmarshFinalInputLedgerTarget_of_weightInfrastructureTarget
    (H : SelbergSieveWeightInfrastructureTarget) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (brunTitchmarshFinalInputLedger_of_weightInfrastructure h)

/--
Selberg weights plus the TS95 trace ledger and TS83 Mellin-tail contracts
supply the TS98 final root input package.
-/
theorem finalHorizonInputsTarget_of_selbergWeight_trace_mellin
    (Hs : SelbergSieveWeightInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  Nonempty.intro
    { brunTitchmarsh :=
        brunTitchmarshFinalInputLedgerTarget_of_weightInfrastructureTarget Hs,
      explicitTrace := Ht,
      mellinTail := Hm }

/--
Selberg weights plus the TS95 trace ledger and TS83 Mellin-tail contracts
feed the TS84 padded final API route through TS98.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_selbergWeight_trace_mellin
    (Hs : SelbergSieveWeightInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS98.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_finalHorizonInputsTarget
    (finalHorizonInputsTarget_of_selbergWeight_trace_mellin
      Hs
      Ht
      Hm)

/--
Selberg weights plus the TS95 trace ledger and TS83 Mellin-tail contracts
feed the full TS25 padded-scale infrastructure through TS98.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_selbergWeight_trace_mellin
    (Hs : SelbergSieveWeightInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS98.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalHorizonInputsTarget
    (finalHorizonInputsTarget_of_selbergWeight_trace_mellin
      Hs
      Ht
      Hm)

end Goldbach
end TS99
