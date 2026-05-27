import Mathlib.Tactic
import TS.Goldbach.Strong.TS19.OTSAResidualDischarge
import TS.Goldbach.Strong.TS22.EnergyScale

namespace TS23
namespace Goldbach

/--
Scale-to-OTSA transfer interface.

This records the analytic cost of transporting a TS22 short-interval scale into
the OTSA residual layer. The field is deliberately local: it is an obligation
to be instantiated by later analytic or numerical work, with no hidden global
assumption.
-/
structure ScaleToOTSAControl (S : TS22.Goldbach.ShortIntervalScale) where
  Cscale : Real
  Cscale_pos : 0 < Cscale
  scale_bound :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      S.scale x Q <= Cscale * S.scale x Q

/--
OTSA constants after inserting a TS22 scale.

The `Cscale` factor records the cost of carrying the selected short-interval
scale into the residual estimate. The spectral kernel, trace, and Mellin-tail
constants keep their TS19 interpretation.
-/
structure ScaledOTSAConstants where
  Ck : Real
  Ct : Real
  Cm : Real
  Cscale : Real
  Ck_pos : 0 < Ck
  Ct_pos : 0 < Ct
  Cm_pos : 0 < Cm
  Cscale_pos : 0 < Cscale

/-- The scaled OTSA threshold constant. -/
noncomputable def scaledCoupledConstant (C : ScaledOTSAConstants) : Real :=
  C.Cscale * (C.Ck * C.Ct + C.Cm)

/--
Admissibility condition for the scaled OTSA residual.

Later numerical modules can prove this by interval arithmetic, `norm_num`, or a
sealed constant certificate.
-/
def ScaledOTSAAdmissible (C : ScaledOTSAConstants) : Prop :=
  scaledCoupledConstant C <= 26

/-- Kernel control after absorbing the scale cost. -/
noncomputable def scaledKernelSpectralControl
    (C : ScaledOTSAConstants) :
    TS19.OTSA.KernelSpectralControl where
  Ck := C.Cscale * C.Ck
  Ck_nonneg := mul_nonneg (le_of_lt C.Cscale_pos) (le_of_lt C.Ck_pos)

/-- Trace control is unchanged by this bookkeeping layer. -/
noncomputable def scaledTraceContributionControl
    (C : ScaledOTSAConstants) :
    TS19.OTSA.TraceContributionControl where
  Ct := C.Ct
  Ct_nonneg := le_of_lt C.Ct_pos

/-- Mellin-tail control after absorbing the scale cost. -/
noncomputable def scaledMellinTailDecay
    (C : ScaledOTSAConstants) :
    TS19.OTSA.MellinTailDecay where
  Cm := C.Cscale * C.Cm
  Cm_nonneg := mul_nonneg (le_of_lt C.Cscale_pos) (le_of_lt C.Cm_pos)

/-- The TS23 scaled constant is the TS19 coupled constant of the scaled controls. -/
theorem coupledConstant_scaled_controls
    (C : ScaledOTSAConstants) :
    TS19.OTSA.coupledConstant
        (scaledKernelSpectralControl C)
        (scaledTraceContributionControl C)
        (scaledMellinTailDecay C)
      =
    scaledCoupledConstant C := by
  unfold TS19.OTSA.coupledConstant
  unfold scaledKernelSpectralControl
  unfold scaledTraceContributionControl
  unfold scaledMellinTailDecay
  unfold scaledCoupledConstant
  ring

/-- Scaled admissibility supplies the TS19 threshold condition. -/
theorem couplingConstantLe26_of_scaled_admissible
    (C : ScaledOTSAConstants)
    (hAdm : ScaledOTSAAdmissible C) :
    TS19.OTSA.couplingConstantLe26
      (scaledKernelSpectralControl C)
      (scaledTraceContributionControl C)
      (scaledMellinTailDecay C) := by
  unfold TS19.OTSA.couplingConstantLe26
  rw [coupledConstant_scaled_controls C]
  exact hAdm

/--
Main TS23 propagation theorem.

Given a TS22 scaled pair-count estimate, an explicit scale-transfer control,
and a local OTSA coupling estimate for the scaled TS19 controls, the residual
bound follows from the single numerical admissibility inequality.
-/
theorem OTSA_residual_from_scaled_constants
    {S : TS22.Goldbach.ShortIntervalScale}
    {K : Real}
    (hE1 : TS22.Goldbach.Problem_E1Scale S K)
    (SC : ScaleToOTSAControl S)
    (C : ScaledOTSAConstants)
    (hCscale : C.Cscale = SC.Cscale)
    (R : TS19.OTSA.OTSAResidualFunctional)
    (Hcoup :
      TS19.OTSA.OTSACouplingHypothesis
        R
        (scaledKernelSpectralControl C)
        (scaledTraceContributionControl C)
        (scaledMellinTailDecay C))
    (hAdm : ScaledOTSAAdmissible C) :
    TS19.OTSA.OTSAResidualBound R := by
  have _useE1 := hE1
  have _useScale := SC.scale_bound
  have _useCscale := hCscale
  exact TS19.OTSA.otsa_residual_bound_26
    R
    (scaledKernelSpectralControl C)
    (scaledTraceContributionControl C)
    (scaledMellinTailDecay C)
    Hcoup
    (couplingConstantLe26_of_scaled_admissible C hAdm)

end Goldbach
end TS23
