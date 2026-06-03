import Mathlib.Tactic
import TS.Goldbach.Strong.TS96.SpectralTraceMajorantDischarge

namespace TS97
namespace Goldbach

/-!
# TS97 - Brun-Titchmarsh Final Input Ledger

TS96 shows that the padded TS25 infrastructure follows from three inputs:
the TS95 explicit-formula trace ledger, the TS83 Mellin-tail final API
contracts, and the TS22 natural-interval Brun-Titchmarsh theorem.

This sprint isolates that last arithmetic input. It does not prove
Brun-Titchmarsh or Selberg's sieve. It records the exact object still needed
and gives the mechanical bridges from that object to the TS84/TS25 assembly
routes already wired by TS96.
-/

/--
Roadmap marker for the final Brun-Titchmarsh input.

This marker is populated unconditionally because it is only a status ledger.
The mathematical interval theorem itself remains in
`BrunTitchmarshFinalInputLedger`.
-/
structure BrunTitchmarshFinalInputRoadmap where
  natural_interval_bound_required :
    True

  selberg_or_external_proof_required :
    True

  padded_scale_feed_required :
    True

/-- Concrete roadmap ledger for TS97. -/
def brunTitchmarshFinalInputRoadmap :
    BrunTitchmarshFinalInputRoadmap where
  natural_interval_bound_required := True.intro
  selberg_or_external_proof_required := True.intro
  padded_scale_feed_required := True.intro

/--
Final arithmetic input ledger for the padded-scale route.

Supplying this structure is exactly supplying the natural-interval
Brun-Titchmarsh theorem expected by TS22.
-/
structure BrunTitchmarshFinalInputLedger where
  bt :
    TS22.Goldbach.BrunTitchmarshNatIntervalBound

/-- Target proposition for the TS97 roadmap marker. -/
def BrunTitchmarshFinalInputRoadmapTarget : Prop :=
  Nonempty BrunTitchmarshFinalInputRoadmap

/-- Target proposition for the final Brun-Titchmarsh input ledger. -/
def BrunTitchmarshFinalInputLedgerTarget : Prop :=
  Nonempty BrunTitchmarshFinalInputLedger

/-- The roadmap marker is populated. -/
theorem brunTitchmarshFinalInputRoadmapTarget :
    BrunTitchmarshFinalInputRoadmapTarget :=
  Nonempty.intro brunTitchmarshFinalInputRoadmap

/-- A final Brun-Titchmarsh input ledger supplies the raw TS22 input target. -/
theorem brunTitchmarshNatIntervalBoundTarget_of_finalInputLedgerTarget
    (H : BrunTitchmarshFinalInputLedgerTarget) :
    Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound := by
  cases H with
  | intro h =>
      exact Nonempty.intro h.bt

/--
The final Brun-Titchmarsh input, together with the TS96 spectral route and the
TS83 Mellin-tail route, supplies the TS84 padded final API package.
-/
noncomputable def paddedScaleTransferFinalAPIContracts_of_finalInputLedger
    (HBT : BrunTitchmarshFinalInputLedger)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContracts where
  BT := HBT.bt
  majorants :=
    Classical.choice
      (TS96.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_explicitFormulaTrace_mellin
        Ht
        Hm)

/--
A final Brun-Titchmarsh input target plus the TS95/TS83 final contracts gives
the TS84 padded final API target.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin
    (HBT : BrunTitchmarshFinalInputLedgerTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget := by
  cases HBT with
  | intro hbt =>
      exact
        Nonempty.intro
          (paddedScaleTransferFinalAPIContracts_of_finalInputLedger
            hbt
            Ht
            Hm)

/--
The TS97 final Brun-Titchmarsh input target, TS95 trace ledger target, and TS83
Mellin-tail target feed the full TS25 padded-scale infrastructure through TS96.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin
    (HBT : BrunTitchmarshFinalInputLedgerTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS96.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_explicitFormulaTrace_mellin
    (brunTitchmarshNatIntervalBoundTarget_of_finalInputLedgerTarget
      HBT)
    Ht
    Hm

end Goldbach
end TS97
