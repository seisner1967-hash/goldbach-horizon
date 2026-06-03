import Mathlib.Tactic
import TS.Goldbach.Strong.TS89.FareyCountingProof

namespace TS90
namespace Goldbach

/-!
# TS90 - Farey Covering Proof

TS87 isolates the Farey covering layer as a local contract. In the current
TS87 API, this contract is a marker field `covering_ready : True`; it does not
yet encode a Dirichlet approximation theorem or a concrete interval-covering
statement.

This sprint therefore discharges exactly the contract that exists today, and
then combines TS88 separation, TS89 counting, and this covering marker into the
full Farey-spacing package. The remaining analytic input below the scale
transfer front is the dual large-sieve variance bound.
-/

/-- Concrete Farey covering contract for the current TS87 marker interface. -/
def fareyCoveringContract :
    TS87.Goldbach.FareyCoveringContract where
  covering_ready := True.intro

/-- TS90 discharges the TS87 Farey covering target. -/
theorem fareyCoveringContractTarget :
    TS87.Goldbach.FareyCoveringContractTarget :=
  Nonempty.intro fareyCoveringContract

/-- Local target for TS90. -/
def FareyCoveringProofTarget : Prop :=
  TS87.Goldbach.FareyCoveringContractTarget

/-- The local TS90 target is discharged. -/
theorem fareyCoveringProofTarget :
    FareyCoveringProofTarget :=
  fareyCoveringContractTarget

/-- TS88, TS89, and TS90 give the full TS87 Farey-spacing contract target. -/
theorem fareySpacingContractTarget :
    TS87.Goldbach.FareySpacingContractTarget :=
  TS89.Goldbach.fareySpacingContractTarget_of_covering
    fareyCoveringContractTarget

/-- TS88, TS89, and TS90 give the TS86 Farey-spacing infrastructure target. -/
theorem fareySpacingInfrastructureTarget :
    TS86.Goldbach.FareySpacingInfrastructureTarget :=
  TS89.Goldbach.fareySpacingInfrastructureTarget_of_covering
    fareyCoveringContractTarget

/--
After TS90, a padded dual large-sieve bound is enough to produce the padded
grand-sieve variance infrastructure.
-/
theorem paddedGrandSieveVarianceInfrastructureTarget_of_paddedDualLargeSieveTarget
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS86.Goldbach.PaddedGrandSieveVarianceInfrastructureTarget :=
  TS87.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
    fareySpacingContractTarget
    HD

/--
After TS90, a padded dual large-sieve bound is enough to produce the padded
Gallagher variance-transfer target.
-/
theorem paddedGallagherVarianceTransferContractTarget_of_paddedDualLargeSieveTarget
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS85.Goldbach.PaddedGallagherVarianceTransferContractTarget :=
  TS87.Goldbach.paddedGallagherVarianceTransferContractTarget_of_fareyContract_paddedDualLargeSieveTarget
    fareySpacingContractTarget
    HD

/--
After TS90, a padded dual large-sieve bound is enough to produce the TS84
scale-transfer API target.
-/
theorem scaleTransferMajorantAPIContractsTarget_of_paddedDualLargeSieveTarget
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget :=
  TS89.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_paddedDualLargeSieveTarget
    fareyCoveringContractTarget
    HD

/--
Trace, Mellin-tail, and a padded dual large-sieve bound now give the final TS84
OTSA majorant API package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedDualLargeSieve
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  TS87.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_farey_paddedDualLargeSieve
    Ht
    Hm
    fareySpacingContractTarget
    HD

/--
Adding Brun-Titchmarsh leaves only the trace, Mellin-tail, and padded dual
large-sieve inputs for the TS25 padded-scale analytic infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedDualLargeSieve
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS87.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
    HBT
    Ht
    Hm
    fareySpacingContractTarget
    HD

end Goldbach
end TS90
