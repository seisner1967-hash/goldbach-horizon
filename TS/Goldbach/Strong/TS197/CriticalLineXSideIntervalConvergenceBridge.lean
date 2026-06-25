import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS196.CriticalLineCompactChangeOfVariablesProbe

namespace TS197
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS197 - Critical-Line X-Side Interval Convergence Bridge

TS196 proved the compact change of variables between the critical-line
logarithmic squared amplitude and the original-coordinate triangle-spline
square density under `x = exp u`.

This sprint transfers the TS194 truncated-energy limit across that compact
change of variables.  The x-side truncated energy is defined as the compact
set integral over `Icc b X`.  Substituting `b = exp a` and using the TS196
compact change of variables gives eventual equality with the TS194 logarithmic
truncated energy as `a -> -infty`; therefore the x-side compact energies also
converge to `X / 3`.

No standalone improper Lebesgue object on `(0, X]`, full Wall 0 transport
`dx / x = du`, Plancherel, explicit formula, zeta-zero summability, or Goldbach
theorem is claimed.
-/

/-- Truncated compact set integral of the x-side square-energy density. -/
noncomputable def criticalLineTruncatedXSideEnergy
    (X : Nat)
    (b : Real) :
    Real :=
  MeasureTheory.integral
    (volume.restrict (Set.Icc b (X : Real)))
    (fun x : Real => TS196.Goldbach.criticalLineXSideEnergyDensity X x)

/--
On `a <= log X`, the compact set integral of the actual squared amplitude is
the TS194 directed interval integral.
-/
theorem compactActualEnergy_setIntegral_eq_truncatedActual
    (X : Nat)
    {a : Real}
    (ha : a <= Real.log (X : Real)) :
    MeasureTheory.integral
        (volume.restrict (Set.Icc a (Real.log (X : Real))))
        (fun u : Real =>
          (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2) =
      TS194.Goldbach.criticalLineTruncatedActualEnergy X a := by
  let f : Real -> Real := fun u =>
    (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2
  have hIccIoc :
      MeasureTheory.integral
        (volume.restrict (Set.Icc a (Real.log (X : Real))))
        f =
      MeasureTheory.integral
        (volume.restrict (Set.Ioc a (Real.log (X : Real))))
        f := by
    exact
      (integral_Icc_eq_integral_Ioc :
        MeasureTheory.integral
          (volume.restrict (Set.Icc a (Real.log (X : Real))))
          f =
        MeasureTheory.integral
          (volume.restrict (Set.Ioc a (Real.log (X : Real))))
          f)
  unfold TS194.Goldbach.criticalLineTruncatedActualEnergy
  rw [intervalIntegral.integral_of_le ha]
  change
    MeasureTheory.integral
      (volume.restrict (Set.Icc a (Real.log (X : Real))))
      f =
    MeasureTheory.integral
      (volume.restrict (Set.Ioc a (Real.log (X : Real))))
      f
  exact hIccIoc

/--
On the eventual range `a <= log X`, the x-side truncated compact energy at
`exp a` equals the TS194 logarithmic truncated energy at `a`.
-/
theorem criticalLineTruncatedXSideEnergy_comp_exp_eq
    (X : Nat)
    (a : Real)
    (hX : 0 < X)
    (ha : a <= Real.log (X : Real)) :
    criticalLineTruncatedXSideEnergy X (Real.exp a) =
      TS194.Goldbach.criticalLineTruncatedActualEnergy X a := by
  unfold criticalLineTruncatedXSideEnergy
  rw [<- TS196.Goldbach.compactActualEnergy_setIntegral_eq_xSide X hX ha]
  exact compactActualEnergy_setIntegral_eq_truncatedActual X ha

/--
The x-side compact energies with lower endpoint `exp a` converge to `X / 3`
as `a -> -infty`.
-/
theorem criticalLineTruncatedXSideEnergy_comp_exp_tendsto
    (X : Nat)
    (hX : 0 < X) :
    Tendsto
      (fun a : Real => criticalLineTruncatedXSideEnergy X (Real.exp a))
      atBot
      (nhds ((X : Real) / 3)) := by
  have h_eventual :
      Filter.EventuallyEq
        atBot
        (fun a : Real => criticalLineTruncatedXSideEnergy X (Real.exp a))
        (fun a : Real => TS194.Goldbach.criticalLineTruncatedActualEnergy X a) := by
    filter_upwards [eventually_atBot.2
      (Exists.intro (Real.log (X : Real)) (by
        intro a ha
        exact ha))] with a ha
    exact criticalLineTruncatedXSideEnergy_comp_exp_eq X a hX ha
  exact
    (TS194.Goldbach.criticalLineTruncatedActualEnergy_tendsto_X_div_three
      X
      hX).congr' h_eventual.symm

/--
Local contract for promoting the x-side compact-energy convergence into a
future named improper object over `(0, X]`.
-/
structure CriticalLineXSideImproperEnergyObjectContract
    (X : Nat) where
  x_side_improper_integral_statement :
    Prop
  x_side_truncated_convergence_consumes_statement :
    Tendsto
      (fun a : Real => criticalLineTruncatedXSideEnergy X (Real.exp a))
      atBot
      (nhds ((X : Real) / 3)) ->
        x_side_improper_integral_statement

/-- Ledger recording the TS197 x-side convergence bridge. -/
structure CriticalLineXSideIntervalConvergenceBridgeLedger where
  ts196_compact_cov_ledger :
    TS196.Goldbach.CriticalLineCompactChangeOfVariablesLedger

  x_side_truncated_energy_defined :
    True

  x_side_comp_exp_eq_u_side :
    forall X : Nat,
      forall a : Real,
        0 < X ->
          a <= Real.log (X : Real) ->
            criticalLineTruncatedXSideEnergy X (Real.exp a) =
              TS194.Goldbach.criticalLineTruncatedActualEnergy X a

  x_side_comp_exp_tendsto :
    forall X : Nat,
      0 < X ->
        Tendsto
          (fun a : Real => criticalLineTruncatedXSideEnergy X (Real.exp a))
          atBot
          (nhds ((X : Real) / 3))

  x_side_improper_object_not_defined :
    True

  wall0_full_measure_transport_not_proved :
    True

  haar_transport_not_proved :
    True

  mellin_fourier_equivalence_not_proved :
    True

  plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS197 x-side convergence bridge ledger. -/
noncomputable def criticalLineXSideIntervalConvergenceBridgeLedger :
    CriticalLineXSideIntervalConvergenceBridgeLedger where
  ts196_compact_cov_ledger :=
    TS196.Goldbach.criticalLineCompactChangeOfVariablesLedger
  x_side_truncated_energy_defined := True.intro
  x_side_comp_exp_eq_u_side :=
    criticalLineTruncatedXSideEnergy_comp_exp_eq
  x_side_comp_exp_tendsto :=
    criticalLineTruncatedXSideEnergy_comp_exp_tendsto
  x_side_improper_object_not_defined := True.intro
  wall0_full_measure_transport_not_proved := True.intro
  haar_transport_not_proved := True.intro
  mellin_fourier_equivalence_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS197. -/
def CriticalLineXSideIntervalConvergenceBridgeTarget : Prop :=
  Nonempty CriticalLineXSideIntervalConvergenceBridgeLedger

/-- The TS197 x-side convergence bridge target is populated. -/
theorem criticalLineXSideIntervalConvergenceBridgeTarget :
    CriticalLineXSideIntervalConvergenceBridgeTarget :=
  Nonempty.intro criticalLineXSideIntervalConvergenceBridgeLedger

end Goldbach
end TS197
