import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS193.CriticalLineTruncatedFTCEnergyBridge

namespace TS194
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS194 - Critical-Line Actual Amplitude Energy Bridge

TS193 proved that the truncated integrals of the expanded critical-line energy
density tend to `X / 3` as the lower endpoint tends to `-infty`.

This sprint connects that expanded calculation back to the actual square of
the TS190 critical-line amplitude.  On the relevant eventual range
`a <= log X`, every point of the directed interval `a..log X` lies on the
support side `exp u <= X`, so the TS191 pointwise expansion applies.  Therefore
the truncated actual-amplitude energy integrals agree with the expanded
integrals eventually, and inherit the same limit `X / 3`.

No standalone improper integral object, Wall 0 measure transport, Plancherel,
explicit formula, zeta-zero summability, or Goldbach theorem is claimed.
-/

/-- Truncated interval integral of the actual critical-line amplitude squared. -/
noncomputable def criticalLineTruncatedActualEnergy
    (X : Nat)
    (a : Real) :
    Real :=
  intervalIntegral
    (fun u : Real =>
      (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2)
    a
    (Real.log (X : Real))
    volume

/-- On a truncated interval ending at `log X`, the actual square equals the expanded density. -/
theorem criticalLineActualEnergy_eq_expanded_on_truncated_interval
    {X : Nat}
    {a u : Real}
    (hX : 0 < X)
    (ha : a <= Real.log (X : Real))
    (hu : Set.uIcc a (Real.log (X : Real)) u) :
    (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2 =
      TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u := by
  have hux : u <= Real.log (X : Real) := by
    have huIcc : (Set.Icc a (Real.log (X : Real))) u := by
      simpa [Set.uIcc_of_le ha] using hu
    exact huIcc.2
  have hXpos : 0 < (X : Real) := by
    exact_mod_cast hX
  have h_exp_le :
      Real.exp u <= (X : Real) := by
    have h_exp :
        Real.exp u <= Real.exp (Real.log (X : Real)) :=
      Real.exp_le_exp.mpr hux
    simpa [Real.exp_log hXpos] using h_exp
  simpa [TS191.Goldbach.criticalLineAmplitudeEnergyDensity] using
    TS191.Goldbach.criticalLineAmplitudeEnergyDensity_eq_expanded_of_exp_le_X
      hX
      h_exp_le

/--
For every lower endpoint `a <= log X`, the actual truncated energy equals the
expanded truncated energy from TS193.
-/
theorem criticalLineTruncatedActualEnergy_eq_expanded_of_le_log
    (X : Nat)
    (hX : 0 < X)
    {a : Real}
    (ha : a <= Real.log (X : Real)) :
    criticalLineTruncatedActualEnergy X a =
      TS193.Goldbach.criticalLineTruncatedExpandedEnergy X a := by
  unfold criticalLineTruncatedActualEnergy
  unfold TS193.Goldbach.criticalLineTruncatedExpandedEnergy
  apply intervalIntegral.integral_congr
  intro u hu
  exact
    criticalLineActualEnergy_eq_expanded_on_truncated_interval
      hX
      ha
      hu

/--
The actual squared critical-line amplitude has the same truncated energy limit
as the expanded density: `X / 3`.
-/
theorem criticalLineTruncatedActualEnergy_tendsto_X_div_three
    (X : Nat)
    (hX : 0 < X) :
    Tendsto
      (fun a : Real =>
        criticalLineTruncatedActualEnergy X a)
      atBot
      (nhds ((X : Real) / 3)) := by
  have h_eventual :
      Filter.EventuallyEq
        atBot
        (fun a : Real =>
          criticalLineTruncatedActualEnergy X a)
        (fun a : Real =>
          TS193.Goldbach.criticalLineTruncatedExpandedEnergy X a) := by
    filter_upwards [eventually_atBot.2
      (Exists.intro (Real.log (X : Real)) (by
        intro a ha
        exact ha))] with a ha
    exact criticalLineTruncatedActualEnergy_eq_expanded_of_le_log X hX ha
  exact
    (TS193.Goldbach.criticalLineTruncatedExpandedEnergy_tendsto_X_div_three
      X
      hX).congr' h_eventual.symm

/--
Local contract for promoting the actual-amplitude truncated convergence into a
future standalone improper integral object.
-/
structure CriticalLineActualImproperEnergyObjectContract
    (X : Nat) where
  actual_improper_integral_statement :
    Prop
  actual_truncated_convergence_consumes_statement :
    Tendsto
      (fun a : Real =>
        criticalLineTruncatedActualEnergy X a)
      atBot
      (nhds ((X : Real) / 3)) ->
        actual_improper_integral_statement

/-- Ledger recording the TS194 actual-amplitude energy bridge. -/
structure CriticalLineActualAmplitudeEnergyBridgeLedger where
  ts193_truncated_ftc :
    TS193.Goldbach.CriticalLineTruncatedFTCEnergyBridgeLedger

  actual_truncated_integrals_tendsto :
    forall X : Nat,
      0 < X ->
        Tendsto
          (fun a : Real =>
            criticalLineTruncatedActualEnergy X a)
          atBot
          (nhds ((X : Real) / 3))

  improper_integral_object_not_defined :
    True

  wall0_measure_transport_not_discharged :
    True

  mellin_fourier_not_proved :
    True

  plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS194 actual-amplitude energy bridge ledger. -/
noncomputable def criticalLineActualAmplitudeEnergyBridgeLedger :
    CriticalLineActualAmplitudeEnergyBridgeLedger where
  ts193_truncated_ftc :=
    TS193.Goldbach.criticalLineTruncatedFTCEnergyBridgeLedger
  actual_truncated_integrals_tendsto :=
    criticalLineTruncatedActualEnergy_tendsto_X_div_three
  improper_integral_object_not_defined := True.intro
  wall0_measure_transport_not_discharged := True.intro
  mellin_fourier_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS194. -/
def CriticalLineActualAmplitudeEnergyBridgeTarget : Prop :=
  Nonempty CriticalLineActualAmplitudeEnergyBridgeLedger

/-- The TS194 actual-amplitude energy bridge target is populated. -/
theorem criticalLineActualAmplitudeEnergyBridgeTarget :
    CriticalLineActualAmplitudeEnergyBridgeTarget :=
  Nonempty.intro criticalLineActualAmplitudeEnergyBridgeLedger

end Goldbach
end TS194
