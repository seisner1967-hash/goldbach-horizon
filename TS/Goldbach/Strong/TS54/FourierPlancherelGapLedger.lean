import Mathlib.Tactic
import TS.Goldbach.Strong.TS53.FourierConcreteSymbolsProbe
import TS.Goldbach.Strong.TS52.FourierMathlibAPIBinding

namespace TS54
namespace MellinJackson

open MeasureTheory
open scoped ENNReal

/-!
# TS54 - Fourier Plancherel L2 Gap Ledger

TS53 located concrete Mathlib symbols for `Real.fourierIntegral`, its inverse,
the real-line kernel formulas, and the derivative-rule theorem. It did not
locate a compatible Plancherel/L2 isometry theorem matching the TS52 `snorm`
interface.

This sprint records that gap as a local Lean object and states the exact
Plancherel contract needed to proceed.
-/

/--
Ledger recording the concrete Fourier symbol status after TS53.

The key field is `plancherel_not_located`: it keeps the missing L2/snorm
Plancherel symbol explicit rather than hiding it inside prose.
-/
structure FourierPlancherelGapLedger where
  /-- Concrete symbol ledger produced by TS53. -/
  symbols :
    TS53.MellinJackson.FourierConcreteSymbolLedger
  /-- The forward Fourier transform symbol was checked. -/
  fourierTransform_checked :
    symbols.fourierTransformStatus =
      TS53.MellinJackson.FourierConcreteSymbolStatus.checked
  /-- The inverse Fourier transform symbol was checked. -/
  fourierTransformInv_checked :
    symbols.fourierTransformInvStatus =
      TS53.MellinJackson.FourierConcreteSymbolStatus.checked
  /-- The derivative-rule symbol was checked. -/
  derivativeRule_checked :
    symbols.derivativeRuleStatus =
      TS53.MellinJackson.FourierConcreteSymbolStatus.checked
  /-- A compatible Plancherel/L2 symbol was not located in TS53. -/
  plancherel_not_located :
    symbols.plancherelStatus =
      TS53.MellinJackson.FourierConcreteSymbolStatus.notLocatedYet

/-- The concrete gap ledger obtained from the TS53 symbol probe. -/
noncomputable def fourierPlancherelGapLedger :
    FourierPlancherelGapLedger where
  symbols := TS53.MellinJackson.fourierConcreteSymbolLedger
  fourierTransform_checked := rfl
  fourierTransformInv_checked := rfl
  derivativeRule_checked := rfl
  plancherel_not_located := rfl

/--
Plancherel/L2 contract for the concrete Fourier route.

This is the exact theorem shape needed by the TS52 binding layer: `snorm`
control for the selected Fourier transform, with the TS41 real normalization
constant transported to `ENNReal`.
-/
structure FourierPlancherelL2Contract where
  /-- The Fourier normalization ledger whose transform is being controlled. -/
  ledger :
    TS41.MellinJackson.FourierAPINormalizationLedger

  /-- The compatible Plancherel/L2 `snorm` comparison. -/
  plancherel_snorm_bound :
    forall (f : Real -> Complex),
      snorm (ledger.fourierTransform f) 2 (volume : Measure Real)
        <=
      ENNReal.ofReal ledger.plancherelConstant *
        snorm f 2 (volume : Measure Real)

/-- Target proposition for the missing Plancherel/L2 contract. -/
def FourierPlancherelL2Target : Prop :=
  Nonempty FourierPlancherelL2Contract

/-- Any supplied Plancherel/L2 contract discharges the TS54 target. -/
theorem FourierPlancherelL2Target.of_contract
    (H : FourierPlancherelL2Contract) :
    FourierPlancherelL2Target :=
  Nonempty.intro H

/-- Extract the Plancherel/L2 contract from a full TS52 Mathlib binding. -/
def fourierPlancherelL2Contract_of_binding
    (H : TS52.MellinJackson.MathlibFourierAPIBinding) :
    FourierPlancherelL2Contract where
  ledger := H.ledger
  plancherel_snorm_bound := H.plancherel_binding

/-- A full TS52 Mathlib binding supplies the TS54 Plancherel/L2 target. -/
theorem FourierPlancherelL2Target_of_binding
    (H : TS52.MellinJackson.MathlibFourierAPIBinding) :
    FourierPlancherelL2Target :=
  FourierPlancherelL2Target.of_contract
    (fourierPlancherelL2Contract_of_binding H)

/--
Joint package recording a future Mathlib Fourier binding together with an
explicit compatible Plancherel/L2 contract.
-/
structure FourierBindingWithPlancherel where
  /-- Future TS52 binding package. -/
  binding :
    TS52.MellinJackson.MathlibFourierAPIBinding
  /-- Compatible Plancherel/L2 contract. -/
  plancherel :
    FourierPlancherelL2Contract
  /-- The two packages use the same TS41 normalization ledger. -/
  ledger_eq :
    binding.ledger = plancherel.ledger

/-- A full TS52 binding yields a compatible TS54 joint package. -/
def FourierBindingWithPlancherel.of_binding
    (H : TS52.MellinJackson.MathlibFourierAPIBinding) :
    FourierBindingWithPlancherel where
  binding := H
  plancherel := fourierPlancherelL2Contract_of_binding H
  ledger_eq := rfl

end MellinJackson
end TS54
