import Mathlib.Tactic
import TS.Goldbach.Strong.TS86.GrandSieveVarianceRoadmap

namespace TS87
namespace Goldbach

/-!
# TS87 - Farey Spacing Roadmap

TS86 isolates the Farey-spacing infrastructure needed by the grand-sieve
variance layer. This sprint opens that geometry one layer further.

No Farey separation theorem is proved here. The classical lower bound
`|a/q - a'/q'| >= 1 / (q q')` remains an explicit local contract. TS87 only
fixes the rational-point API, records the separation/covering/counting
obligations, and proves that those contracts feed the TS86 infrastructure.
-/

/-- A rational point represented by an integer numerator and positive natural
denominator. Reducedness is left as a marker until the Farey layer is
instantiated concretely. -/
structure FareyPoint where
  num :
    Int

  den :
    Nat

  den_pos :
    0 < den

  reduced_ready :
    True

namespace FareyPoint

/-- Real value of a Farey point. -/
noncomputable def value
    (p : FareyPoint) :
    Real :=
  (p.num : Real) / (p.den : Real)

/-- Denominator bound for points selected from a Farey window of height `Q`. -/
def denBound
    (Q : Nat)
    (p : FareyPoint) :
    Prop :=
  p.den <= Q

/-- Distinctness at the level of embedded real values. -/
def valueDistinct
    (p r : FareyPoint) :
    Prop :=
  value p != value r

end FareyPoint

/--
The classical Farey separation statement in the form needed by the large
sieve: two distinct rational points with denominators `q` and `q'` are
separated by at least `1 / (q q')`.
-/
def FareySeparationStatement : Prop :=
  forall p r : FareyPoint,
    FareyPoint.valueDistinct p r ->
      (1 : Real) / ((p.den : Real) * (r.den : Real)) <=
        |FareyPoint.value p - FareyPoint.value r|

/-- Contract for the Farey separation inequality. -/
structure FareySeparationContract where
  separation :
    FareySeparationStatement

/-- Contract for the covering geometry used by Gallagher's variance transfer. -/
structure FareyCoveringContract where
  covering_ready :
    True

/-- Contract for counting the selected rational points in Farey windows. -/
structure FareyCountingContract where
  counting_ready :
    True

/--
Farey-spacing package below the TS86 marker infrastructure.

The separation field is the arithmetic heart of the future proof. The covering
and counting fields keep the analytic large-sieve geometry explicit.
-/
structure FareySpacingContract where
  separation :
    FareySeparationContract

  covering :
    FareyCoveringContract

  counting :
    FareyCountingContract

/-- Roadmap ledger for the Farey-spacing front. -/
structure FareySpacingRoadmap where
  rational_point_api_ready :
    True

  separation_contract_ready :
    True

  covering_contract_ready :
    True

  counting_contract_ready :
    True

/-- Concrete roadmap ledger for TS87. -/
def fareySpacingRoadmap :
    FareySpacingRoadmap where
  rational_point_api_ready := True.intro
  separation_contract_ready := True.intro
  covering_contract_ready := True.intro
  counting_contract_ready := True.intro

/--
A concrete Farey-spacing contract supplies the coarser TS86 marker
infrastructure.
-/
def fareySpacingInfrastructure_of_contract
    (H : FareySpacingContract) :
    TS86.Goldbach.FareySpacingInfrastructure where
  spacing_separation_ready := by
    have _hsep : FareySeparationStatement :=
      H.separation.separation
    exact True.intro
  spacing_cover_ready :=
    H.covering.covering_ready
  spacing_count_ready :=
    H.counting.counting_ready

/-- Target proposition for the TS87 roadmap ledger. -/
def FareySpacingRoadmapTarget : Prop :=
  Nonempty FareySpacingRoadmap

/-- Target proposition for the Farey separation contract. -/
def FareySeparationContractTarget : Prop :=
  Nonempty FareySeparationContract

/-- Target proposition for the Farey covering contract. -/
def FareyCoveringContractTarget : Prop :=
  Nonempty FareyCoveringContract

/-- Target proposition for the Farey counting contract. -/
def FareyCountingContractTarget : Prop :=
  Nonempty FareyCountingContract

/-- Target proposition for the combined Farey-spacing contract. -/
def FareySpacingContractTarget : Prop :=
  Nonempty FareySpacingContract

/-- The TS87 roadmap ledger is populated. -/
theorem fareySpacingRoadmapTarget :
    FareySpacingRoadmapTarget :=
  Nonempty.intro fareySpacingRoadmap

/-- Separation, covering, and counting targets give a Farey-spacing target. -/
theorem fareySpacingContractTarget_of_components
    (Hs : FareySeparationContractTarget)
    (Hc : FareyCoveringContractTarget)
    (Hn : FareyCountingContractTarget) :
    FareySpacingContractTarget := by
  cases Hs with
  | intro hs =>
      cases Hc with
      | intro hc =>
          cases Hn with
          | intro hn =>
              exact
                Nonempty.intro
                  { separation := hs
                    covering := hc
                    counting := hn }

/-- A Farey-spacing contract target gives the TS86 Farey infrastructure target. -/
theorem fareySpacingInfrastructureTarget_of_contractTarget
    (H : FareySpacingContractTarget) :
    TS86.Goldbach.FareySpacingInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (fareySpacingInfrastructure_of_contract h)

/--
Farey-spacing contracts plus the dual large-sieve variance target give the
TS86 grand-sieve variance target at scale `S`.
-/
theorem grandSieveVarianceInfrastructureTarget_of_fareyContract_dualLargeSieveTarget
    {S : TS22.Goldbach.ShortIntervalScale}
    (HF : FareySpacingContractTarget)
    (HD : TS86.Goldbach.DualLargeSieveVarianceBoundTarget S) :
    TS86.Goldbach.GrandSieveVarianceInfrastructureTarget S :=
  TS86.Goldbach.grandSieveVarianceInfrastructureTarget_of_farey_dualLargeSieveTargets
    (fareySpacingInfrastructureTarget_of_contractTarget HF)
    HD

/--
Farey-spacing contracts plus a padded dual large-sieve target give the padded
grand-sieve variance infrastructure.
-/
theorem paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
    (HF : FareySpacingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS86.Goldbach.PaddedGrandSieveVarianceInfrastructureTarget :=
  grandSieveVarianceInfrastructureTarget_of_fareyContract_dualLargeSieveTarget
    HF
    HD

/--
Farey-spacing contracts plus a padded dual large-sieve target give the TS85
padded Gallagher variance target.
-/
theorem paddedGallagherVarianceTransferContractTarget_of_fareyContract_paddedDualLargeSieveTarget
    (HF : FareySpacingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS85.Goldbach.PaddedGallagherVarianceTransferContractTarget :=
  TS86.Goldbach.paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget
    (paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
      HF
      HD)

/--
Farey-spacing contracts plus a padded dual large-sieve target give the TS84
scale-transfer API target.
-/
theorem scaleTransferMajorantAPIContractsTarget_of_fareyContract_paddedDualLargeSieveTarget
    (HF : FareySpacingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget :=
  TS86.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedGrandSieveTarget
    (paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
      HF
      HD)

/--
Trace, Mellin-tail, Farey-spacing, and padded dual large-sieve contracts give
the final TS84 OTSA majorant package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_farey_paddedDualLargeSieve
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (HF : FareySpacingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  TS86.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGrandSieve
    Ht
    Hm
    (paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
      HF
      HD)

/--
Adding Brun-Titchmarsh gives the final padded-scale API package from the Farey
and dual large-sieve layer.
-/
theorem PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (HF : FareySpacingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS86.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
    HBT
    Ht
    Hm
    (paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
      HF
      HD)

/--
The Farey-spacing and dual large-sieve layer feeds the TS25 padded-scale
infrastructure through TS86, TS85, and TS84.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (HF : FareySpacingContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS86.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
    HBT
    Ht
    Hm
    (paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
      HF
      HD)

end Goldbach
end TS87
