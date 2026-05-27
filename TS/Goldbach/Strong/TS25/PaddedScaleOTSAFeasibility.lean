import Mathlib.Tactic
import TS.Goldbach.Strong.TS23.OTSAScalePropagation
import TS.Goldbach.Strong.TS24.ClosedFormScaleBridge

namespace TS25
namespace Goldbach

/--
Full local infrastructure for the padded Brun-Titchmarsh scale.

This is not an unconditional proof object. The Brun-Titchmarsh interval theorem,
the scale-to-OTSA transfer, and the scaled OTSA admissibility certificate remain
explicit local obligations.
-/
structure PaddedScaleAnalyticInfrastructure where
  BT : TS22.Goldbach.BrunTitchmarshNatIntervalBound
  scaleControl :
    TS23.Goldbach.ScaleToOTSAControl
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale
  constants : TS23.Goldbach.ScaledOTSAConstants
  Cscale_matches : constants.Cscale = scaleControl.Cscale
  admissible : TS23.Goldbach.ScaledOTSAAdmissible constants

/--
The TS24 padded closed-form scale gives the scaled E1 estimate, assuming the
local interval Brun-Titchmarsh theorem.
-/
theorem Problem_E1Scale_from_padded_infrastructure
    (H : PaddedScaleAnalyticInfrastructure) :
    TS22.Goldbach.Problem_E1Scale
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale
      1 :=
  TS24.Goldbach.Problem_E1Scale_from_natIntervalBound_paddedClosedForm H.BT

/-- Expose the scaled OTSA admissibility certificate for the padded scale. -/
theorem OTSA_viability_from_padded_scale
    (H : PaddedScaleAnalyticInfrastructure) :
    TS23.Goldbach.ScaledOTSAAdmissible H.constants := by
  exact H.admissible

/--
Padded-scale OTSA residual discharge.

Once the padded scale is controlled and a local OTSA coupling estimate is
available for the scaled TS23 controls, the TS19 residual target follows from
the single admissibility certificate packaged in `H`.
-/
theorem OTSA_residual_from_padded_scale
    (H : PaddedScaleAnalyticInfrastructure)
    (R : TS19.OTSA.OTSAResidualFunctional)
    (Hcoup :
      TS19.OTSA.OTSACouplingHypothesis
        R
        (TS23.Goldbach.scaledKernelSpectralControl H.constants)
        (TS23.Goldbach.scaledTraceContributionControl H.constants)
        (TS23.Goldbach.scaledMellinTailDecay H.constants)) :
    TS19.OTSA.OTSAResidualBound R :=
  TS23.Goldbach.OTSA_residual_from_scaled_constants
    (Problem_E1Scale_from_padded_infrastructure H)
    H.scaleControl
    H.constants
    H.Cscale_matches
    R
    Hcoup
    H.admissible

end Goldbach
end TS25
