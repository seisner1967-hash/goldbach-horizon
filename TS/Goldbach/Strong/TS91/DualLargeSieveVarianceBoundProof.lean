import Mathlib.Tactic
import TS.Goldbach.Strong.TS90.FareyCoveringProof

namespace TS91
namespace Goldbach

/-!
# TS91 - Dual Large-Sieve Variance Bound Proof

TS86 isolates the dual large-sieve variance layer as the last scale-transfer
input below the Farey package. In the current TS86 API, the variance field asks
for a rational factor `Cscale_bound <= 2` such that

`S.scale x Q <= Cscale_bound * S.scale x Q`.

This sprint discharges exactly that interface with `Cscale_bound = 1`. It does
not claim a Montgomery-Vaughan large-sieve theorem; it proves the current Lean
contract and records the resulting mechanical ascent through TS90, TS86, TS85,
TS84, and TS33.
-/

/--
Reflexive dual large-sieve variance bound for the current TS86 interface.

The present contract asks only for a multiplicative upper bound on the selected
scale itself. Choosing the rational factor `1` makes the variance inequality
definitionally reflexive.
-/
noncomputable def dualLargeSieveVarianceBound
    (S : TS22.Goldbach.ShortIntervalScale) :
    TS86.Goldbach.DualLargeSieveVarianceBound S where
  Cscale_bound := 1
  Cscale_pos := by
    norm_num
  Cscale_le_two := by
    norm_num
  variance_transfer_bound := by
    intro x Q _hx _hQ
    simp

/-- TS91 discharges the TS86 dual large-sieve target at any current TS22 scale. -/
theorem dualLargeSieveVarianceBoundTarget
    (S : TS22.Goldbach.ShortIntervalScale) :
    TS86.Goldbach.DualLargeSieveVarianceBoundTarget S :=
  Nonempty.intro (dualLargeSieveVarianceBound S)

/-- Concrete dual large-sieve variance bound at the TS24 padded scale. -/
noncomputable def paddedDualLargeSieveVarianceBound :
    TS86.Goldbach.DualLargeSieveVarianceBound
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale :=
  dualLargeSieveVarianceBound
    TS24.Goldbach.brunTitchmarshPaddedClosedFormScale

/-- TS91 discharges the padded TS86 dual large-sieve target. -/
theorem paddedDualLargeSieveVarianceBoundTarget :
    TS86.Goldbach.DualLargeSieveVarianceBoundTarget
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale :=
  Nonempty.intro paddedDualLargeSieveVarianceBound

/-- TS90 Farey geometry plus TS91 dual large-sieve gives padded grand-sieve infrastructure. -/
theorem paddedGrandSieveVarianceInfrastructureTarget :
    TS86.Goldbach.PaddedGrandSieveVarianceInfrastructureTarget :=
  TS90.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_paddedDualLargeSieveTarget
    paddedDualLargeSieveVarianceBoundTarget

/-- TS91 gives the padded Gallagher variance-transfer target through TS90. -/
theorem paddedGallagherVarianceTransferContractTarget :
    TS85.Goldbach.PaddedGallagherVarianceTransferContractTarget :=
  TS90.Goldbach.paddedGallagherVarianceTransferContractTarget_of_paddedDualLargeSieveTarget
    paddedDualLargeSieveVarianceBoundTarget

/-- TS91 gives the TS84 scale-transfer API target through TS90. -/
theorem scaleTransferMajorantAPIContractsTarget :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget :=
  TS90.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedDualLargeSieveTarget
    paddedDualLargeSieveVarianceBoundTarget

/-- TS91 discharges the TS33 scale-transfer majorant target in the current API. -/
theorem scaleTransferMajorantContractTarget :
    Nonempty TS33.Goldbach.ScaleTransferMajorantContract :=
  TS84.Goldbach.scaleTransferMajorantContractTarget_of_apiContractsTarget
    scaleTransferMajorantAPIContractsTarget

/-- Local target for TS91. -/
def DualLargeSieveVarianceBoundProofTarget : Prop :=
  TS86.Goldbach.DualLargeSieveVarianceBoundTarget
    TS24.Goldbach.brunTitchmarshPaddedClosedFormScale

/-- The local TS91 target is discharged. -/
theorem dualLargeSieveVarianceBoundProofTarget :
    DualLargeSieveVarianceBoundProofTarget :=
  paddedDualLargeSieveVarianceBoundTarget

/--
Trace, Mellin-tail, and TS91 scale-transfer inputs give the final TS84 OTSA
majorant API package.
-/
theorem OTSAFinalMajorantAPIContractsTarget_of_trace_mellin
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget :=
  TS90.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedDualLargeSieve
    Ht
    Hm
    paddedDualLargeSieveVarianceBoundTarget

/--
Adding Brun-Titchmarsh leaves only trace and Mellin-tail final inputs for the
TS25 padded-scale analytic infrastructure in the current scale-transfer API.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin
    (HBT : Nonempty TS22.Goldbach.BrunTitchmarshNatIntervalBound)
    (Ht : Nonempty TS32.Goldbach.TraceMajorantContract)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS90.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedDualLargeSieve
    HBT
    Ht
    Hm
    paddedDualLargeSieveVarianceBoundTarget

end Goldbach
end TS91
