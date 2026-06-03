import Mathlib.Tactic
import TS.Goldbach.Strong.TS85.ScaleTransferVarianceLedger

namespace TS86
namespace Goldbach

/-!
# TS86 - Grand Sieve Variance Roadmap

TS85 isolates the Gallagher-style variance transfer contract. This sprint opens
the next layer down: the grand-sieve/Farey-spacing infrastructure expected to
produce that Gallagher contract.

No grand-sieve theorem is proved here. The analytic inequality is still an
explicit field in `DualLargeSieveVarianceBound`. TS86 only records the
interface and proves that a compatible grand-sieve variance package feeds TS85,
TS84, and the padded-scale TS25 infrastructure.
-/

/--
Roadmap ledger for the grand-sieve variance front.

The future analytic proof should provide the spacing/covering geometry, the
dual large-sieve variance bound, and the translation from that bound to the
Gallagher-style scale transfer.
-/
structure GrandSieveVarianceRoadmap where
  farey_spacing_required :
    True

  dual_large_sieve_required :
    True

  gallagher_covering_required :
    True

  padded_scale_specialization_required :
    True

/-- Concrete ledger for the grand-sieve variance front. -/
def grandSieveVarianceRoadmap :
    GrandSieveVarianceRoadmap where
  farey_spacing_required := True.intro
  dual_large_sieve_required := True.intro
  gallagher_covering_required := True.intro
  padded_scale_specialization_required := True.intro

/--
Farey-spacing and rational-point geometry for the grand-sieve argument.

The fields are markers here; a later sprint may replace them by concrete
separation, covering, and counting inequalities for the selected rational
points.
-/
structure FareySpacingInfrastructure where
  spacing_separation_ready :
    True

  spacing_cover_ready :
    True

  spacing_count_ready :
    True

/--
Dual large-sieve variance bound at a selected TS22 scale.

This is the analytic inequality that should eventually be proved from the
grand sieve. It has the same numeric shape as the TS85 Gallagher contract, but
keeps the grand-sieve provenance explicit.
-/
structure DualLargeSieveVarianceBound
    (S : TS22.Goldbach.ShortIntervalScale) where
  Cscale_bound :
    Rat

  Cscale_pos :
    0 < Cscale_bound

  Cscale_le_two :
    Cscale_bound <= 2

  variance_transfer_bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      S.scale x Q <= (Cscale_bound : Real) * S.scale x Q

/--
Grand-sieve variance infrastructure at a selected TS22 scale.

This packages the geometric Farey-spacing layer together with the dual
large-sieve variance estimate.
-/
structure GrandSieveVarianceInfrastructure
    (S : TS22.Goldbach.ShortIntervalScale) where
  farey :
    FareySpacingInfrastructure

  dualLargeSieve :
    DualLargeSieveVarianceBound S

  gallagher_covering_ready :
    True

/--
Grand-sieve variance infrastructure supplies the TS85 Gallagher contract at the
same scale.
-/
noncomputable def gallagherVarianceTransferContract_of_grandSieveVariance
    {S : TS22.Goldbach.ShortIntervalScale}
    (H : GrandSieveVarianceInfrastructure S) :
    TS85.Goldbach.GallagherVarianceTransferContract S where
  Cscale_bound := H.dualLargeSieve.Cscale_bound
  Cscale_pos := H.dualLargeSieve.Cscale_pos
  Cscale_le_two := H.dualLargeSieve.Cscale_le_two
  scale_transfer_bound := H.dualLargeSieve.variance_transfer_bound

/-- Grand-sieve variance infrastructure specialized to the TS24 padded scale. -/
abbrev PaddedGrandSieveVarianceInfrastructure : Type :=
  GrandSieveVarianceInfrastructure
    TS24.Goldbach.brunTitchmarshPaddedClosedFormScale

/-- A padded grand-sieve package supplies the padded Gallagher contract. -/
noncomputable def paddedGallagherVarianceTransferContract_of_grandSieveVariance
    (H : PaddedGrandSieveVarianceInfrastructure) :
    TS85.Goldbach.PaddedGallagherVarianceTransferContract :=
  gallagherVarianceTransferContract_of_grandSieveVariance H

/-- Target proposition for the grand-sieve variance roadmap. -/
def GrandSieveVarianceRoadmapTarget : Prop :=
  Nonempty GrandSieveVarianceRoadmap

/-- Target proposition for the Farey-spacing infrastructure. -/
def FareySpacingInfrastructureTarget : Prop :=
  Nonempty FareySpacingInfrastructure

/-- Target proposition for the dual large-sieve variance bound at scale `S`. -/
def DualLargeSieveVarianceBoundTarget
    (S : TS22.Goldbach.ShortIntervalScale) : Prop :=
  Nonempty (DualLargeSieveVarianceBound S)

/-- Target proposition for grand-sieve variance infrastructure at scale `S`. -/
def GrandSieveVarianceInfrastructureTarget
    (S : TS22.Goldbach.ShortIntervalScale) : Prop :=
  Nonempty (GrandSieveVarianceInfrastructure S)

/-- Target proposition for the padded grand-sieve variance package. -/
def PaddedGrandSieveVarianceInfrastructureTarget : Prop :=
  Nonempty PaddedGrandSieveVarianceInfrastructure

/-- The TS86 grand-sieve variance roadmap ledger is populated. -/
theorem grandSieveVarianceRoadmapTarget :
    GrandSieveVarianceRoadmapTarget :=
  Nonempty.intro grandSieveVarianceRoadmap

/--
Farey spacing plus a dual large-sieve variance bound give grand-sieve
variance infrastructure at scale `S`.
-/
def grandSieveVarianceInfrastructure_of_farey_dualLargeSieve
    {S : TS22.Goldbach.ShortIntervalScale}
    (HF : FareySpacingInfrastructure)
    (HD : DualLargeSieveVarianceBound S) :
    GrandSieveVarianceInfrastructure S where
  farey := HF
  dualLargeSieve := HD
  gallagher_covering_ready := True.intro

/--
Farey-spacing and dual large-sieve targets give grand-sieve variance target at
scale `S`.
-/
theorem grandSieveVarianceInfrastructureTarget_of_farey_dualLargeSieveTargets
    {S : TS22.Goldbach.ShortIntervalScale}
    (HF : FareySpacingInfrastructureTarget)
    (HD : DualLargeSieveVarianceBoundTarget S) :
    GrandSieveVarianceInfrastructureTarget S := by
  cases HF with
  | intro hf =>
      cases HD with
      | intro hd =>
          exact
            Nonempty.intro
              (grandSieveVarianceInfrastructure_of_farey_dualLargeSieve
                hf hd)

/-- A grand-sieve variance target gives the TS85 Gallagher target. -/
theorem gallagherVarianceTransferContractTarget_of_grandSieveVarianceTarget
    {S : TS22.Goldbach.ShortIntervalScale}
    (H : GrandSieveVarianceInfrastructureTarget S) :
    TS85.Goldbach.GallagherVarianceTransferContractTarget S := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (gallagherVarianceTransferContract_of_grandSieveVariance h)

/-- A padded grand-sieve target gives the TS85 padded Gallagher target. -/
theorem paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget
    (H : PaddedGrandSieveVarianceInfrastructureTarget) :
    TS85.Goldbach.PaddedGallagherVarianceTransferContractTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (paddedGallagherVarianceTransferContract_of_grandSieveVariance h)

/-- A padded grand-sieve target gives the TS84 scale-transfer API target. -/
theorem scaleTransferMajorantAPIContractsTarget_of_paddedGrandSieveTarget
    (H : PaddedGrandSieveVarianceInfrastructureTarget) :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget :=
  TS85.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget
    (paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget H)

/-- A padded grand-sieve target gives the TS33 scale-transfer majorant target. -/
theorem scaleTransferMajorantContractTarget_of_paddedGrandSieveTarget
    (H : PaddedGrandSieveVarianceInfrastructureTarget) :
    Nonempty TS33.Goldbach.ScaleTransferMajorantContract :=
  TS85.Goldbach.scaleTransferMajorantContractTarget_of_paddedGallagherTarget
    (paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget H)

/--
Trace, Mellin-tail, and padded grand-sieve contracts give the final TS84 OTSA
majorant package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGrandSieve
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (Hg : PaddedGrandSieveVarianceInfrastructureTarget) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  TS85.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher
    Ht
    Hm
    (paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget Hg)

/--
Adding Brun-Titchmarsh gives the TS84 final padded-scale API package from the
grand-sieve variance layer.
-/
theorem PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (Hg : PaddedGrandSieveVarianceInfrastructureTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS85.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
    HBT
    Ht
    Hm
    (paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget Hg)

/--
The grand-sieve variance layer feeds the TS25 padded-scale infrastructure
through TS85 and TS84.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (Hg : PaddedGrandSieveVarianceInfrastructureTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS85.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
    HBT
    Ht
    Hm
    (paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget Hg)

end Goldbach
end TS86
