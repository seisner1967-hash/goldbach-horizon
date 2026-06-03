import Mathlib.Tactic
import TS.Goldbach.Strong.TS84.ScaleTransferMajorantRoadmap

namespace TS85
namespace Goldbach

/-!
# TS85 - Scale Transfer Variance Ledger

TS84 records the final scale-transfer API contract needed for `Cscale <= 2`.
This sprint opens the next layer down: a Gallagher-style variance transfer
contract whose job is to produce the padded TS23 scale-to-OTSA control and the
compatible rational scale majorant required by TS84.

This is still a ledger, not a proof of Gallagher's large-sieve variance
estimate. The analytic content remains in the explicit
`GallagherVarianceTransferContract`.
-/

/--
Roadmap ledger for the variance-transfer proof layer.

The future analytic proof should explain how local short-interval information
is integrated into the global OTSA variance with a transfer factor at most `2`.
-/
structure ScaleTransferVarianceLedger where
  gallagher_variance_required :
    True

  local_to_global_transfer_required :
    True

  padded_scale_compatibility_required :
    True

  rational_factor_two_required :
    True

/-- Concrete ledger for the current variance-transfer front. -/
def scaleTransferVarianceLedger :
    ScaleTransferVarianceLedger where
  gallagher_variance_required := True.intro
  local_to_global_transfer_required := True.intro
  padded_scale_compatibility_required := True.intro
  rational_factor_two_required := True.intro

/--
Gallagher-style variance transfer contract for an explicit TS22 scale.

The field `scale_transfer_bound` is the precise bridge needed by the TS23
scale-to-OTSA control. A future analytic proof may derive this field from a
Gallagher variance theorem, a large-sieve inequality, or another scale-transfer
argument.
-/
structure GallagherVarianceTransferContract
    (S : TS22.Goldbach.ShortIntervalScale) where
  Cscale_bound :
    Rat

  Cscale_pos :
    0 < Cscale_bound

  Cscale_le_two :
    Cscale_bound <= 2

  scale_transfer_bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      S.scale x Q <= (Cscale_bound : Real) * S.scale x Q

/-- The Gallagher variance contract gives the TS23 scale-to-OTSA control. -/
noncomputable def scaleToOTSAControl_of_gallagherVariance
    {S : TS22.Goldbach.ShortIntervalScale}
    (H : GallagherVarianceTransferContract S) :
    TS23.Goldbach.ScaleToOTSAControl S where
  Cscale := (H.Cscale_bound : Real)
  Cscale_pos := by exact_mod_cast H.Cscale_pos
  scale_bound := H.scale_transfer_bound

/--
The padded closed-form scale is the scale used by the current OTSA v3
scale-transfer route.
-/
abbrev PaddedGallagherVarianceTransferContract : Type :=
  GallagherVarianceTransferContract
    TS24.Goldbach.brunTitchmarshPaddedClosedFormScale

/-- A padded Gallagher contract gives the TS84 scale-transfer API package. -/
noncomputable def scaleTransferMajorantAPIContracts_of_paddedGallagher
    (H : PaddedGallagherVarianceTransferContract) :
    TS84.Goldbach.ScaleTransferMajorantAPIContracts where
  scaleControl := scaleToOTSAControl_of_gallagherVariance H
  Cscale_bound := H.Cscale_bound
  Cscale_pos := H.Cscale_pos
  Cscale_le_two := H.Cscale_le_two
  Cscale_matches_control := rfl

/-- Target proposition for the variance-transfer ledger. -/
def ScaleTransferVarianceLedgerTarget : Prop :=
  Nonempty ScaleTransferVarianceLedger

/-- Target proposition for a Gallagher variance transfer contract at scale `S`. -/
def GallagherVarianceTransferContractTarget
    (S : TS22.Goldbach.ShortIntervalScale) : Prop :=
  Nonempty (GallagherVarianceTransferContract S)

/-- Target proposition for the padded Gallagher variance transfer contract. -/
def PaddedGallagherVarianceTransferContractTarget : Prop :=
  Nonempty PaddedGallagherVarianceTransferContract

/-- The TS85 variance-transfer ledger is populated. -/
theorem scaleTransferVarianceLedgerTarget :
    ScaleTransferVarianceLedgerTarget :=
  Nonempty.intro scaleTransferVarianceLedger

/-- A Gallagher target at scale `S` gives a TS23 scale-to-OTSA control target. -/
theorem scaleToOTSAControlTarget_of_gallagherVarianceTarget
    {S : TS22.Goldbach.ShortIntervalScale}
    (H : GallagherVarianceTransferContractTarget S) :
    Nonempty (TS23.Goldbach.ScaleToOTSAControl S) := by
  cases H with
  | intro h =>
      exact Nonempty.intro (scaleToOTSAControl_of_gallagherVariance h)

/-- A padded Gallagher target gives the TS84 scale-transfer API target. -/
theorem scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget
    (H : PaddedGallagherVarianceTransferContractTarget) :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (scaleTransferMajorantAPIContracts_of_paddedGallagher h)

/-- A padded Gallagher target gives the TS33 scale-transfer majorant target. -/
theorem scaleTransferMajorantContractTarget_of_paddedGallagherTarget
    (H : PaddedGallagherVarianceTransferContractTarget) :
    Nonempty TS33.Goldbach.ScaleTransferMajorantContract :=
  TS84.Goldbach.scaleTransferMajorantContractTarget_of_apiContractsTarget
    (scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget H)

/--
Trace, Mellin-tail, and padded Gallagher contracts give the final TS84 OTSA
majorant package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (Hg : PaddedGallagherVarianceTransferContractTarget) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget := by
  cases Ht with
  | intro ht =>
      cases Hm with
      | intro hm =>
          cases Hg with
          | intro hg =>
              exact
                Nonempty.intro
                  { trace := ht
                    mellin := hm
                    scale :=
                      scaleTransferMajorantAPIContracts_of_paddedGallagher
                        hg }

/--
Adding a Brun-Titchmarsh interval input gives the final padded-scale TS84
contract package.
-/
theorem PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (Hg : PaddedGallagherVarianceTransferContractTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget := by
  cases HBT with
  | intro hbt =>
      cases
        OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher
          Ht Hm Hg with
      | intro hmajor =>
          exact
            Nonempty.intro
              { BT := hbt
                majorants := hmajor }

/--
The TS85 contracts feed the TS25 padded-scale analytic infrastructure through
TS84.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (Hg : PaddedGallagherVarianceTransferContractTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS84.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalAPIContractsTarget
    (PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
      HBT Ht Hm Hg)

end Goldbach
end TS85
