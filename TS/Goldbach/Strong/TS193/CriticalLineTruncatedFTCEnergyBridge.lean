import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exp
import TS.Goldbach.Strong.TS192.CriticalLinePrimitiveLowerTailLimit

namespace TS193
namespace Goldbach

open Filter
open MeasureTheory

/-!
# TS193 - Critical-Line Truncated FTC Energy Bridge

TS191 proved the algebraic primitive value at the upper endpoint `log X`.
TS192 proved that the same primitive tends to `0` as `u -> -infty`.

This sprint proves the finite-interval Fundamental Theorem of Calculus bridge:
the expanded critical-line energy density integrates over `a..log X` to the
difference of the TS191 primitive values.  It then combines that truncated FTC
identity with the TS191/TS192 boundary values to prove that the truncated
integrals tend to `X / 3` as the lower endpoint `a -> -infty`.

The result is a genuine convergence theorem for truncated interval integrals.
It is still not a standalone Lean object for the full improper Lebesgue
integral, and it does not discharge Wall 0 measure transport.
-/

/-- The TS191 primitive differentiates to the expanded critical-line density. -/
theorem criticalLineEnergyPrimitive_hasDerivAt
    (X : Nat)
    (u : Real) :
    HasDerivAt
      (fun v : Real =>
        TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X v)
      (TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
      u := by
  unfold TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
  unfold TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity
  have h_exp : HasDerivAt (fun v : Real => Real.exp v) (Real.exp u) u :=
    Real.hasDerivAt_exp u
  have h_exp_two :
      HasDerivAt
        (fun v : Real => Real.exp (2 * v))
        (2 * Real.exp (2 * u))
        u := by
    have h_linear : HasDerivAt (fun v : Real => (2 : Real) * v) 2 u := by
      simpa using (hasDerivAt_id u).const_mul (2 : Real)
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (2 * u)).comp u h_linear
  have h_exp_three :
      HasDerivAt
        (fun v : Real => Real.exp (3 * v))
        (3 * Real.exp (3 * u))
        u := by
    have h_linear : HasDerivAt (fun v : Real => (3 : Real) * v) 3 u := by
      simpa using (hasDerivAt_id u).const_mul (3 : Real)
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (3 * u)).comp u h_linear
  have h_second :
      HasDerivAt
        (fun v : Real => (1 / (X : Real)) * Real.exp (2 * v))
        ((1 / (X : Real)) * (2 * Real.exp (2 * u)))
        u :=
    h_exp_two.const_mul (1 / (X : Real))
  have h_third :
      HasDerivAt
        (fun v : Real =>
          (1 / (3 * ((X : Real) ^ 2))) * Real.exp (3 * v))
        ((1 / (3 * ((X : Real) ^ 2))) * (3 * Real.exp (3 * u)))
        u :=
    h_exp_three.const_mul (1 / (3 * ((X : Real) ^ 2)))
  convert h_exp.sub h_second |>.add h_third using 1
  ring_nf

/-- The expanded density is interval-integrable on every truncated interval. -/
theorem criticalLineExpandedDensity_intervalIntegrable
    (X : Nat)
    (a b : Real) :
    IntervalIntegrable
      (fun u : Real =>
        TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
      volume
      a
      b := by
  apply Continuous.intervalIntegrable
  unfold TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity
  continuity

/-- Truncated interval integral of the expanded critical-line energy density. -/
noncomputable def criticalLineTruncatedExpandedEnergy
    (X : Nat)
    (a : Real) :
    Real :=
  intervalIntegral
    (fun u : Real =>
      TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
    a
    (Real.log (X : Real))
    volume

/--
Finite-interval FTC bridge for the expanded critical-line energy density.

This is the concrete truncated version of the future improper integral.
-/
theorem criticalLineTruncatedExpandedEnergy_eq_primitive_sub
    (X : Nat)
    (a : Real) :
    criticalLineTruncatedExpandedEnergy X a =
    TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
        X (Real.log (X : Real))
      -
    TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X a := by
  let F : Real -> Real := fun u =>
    TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X u
  have hderiv :
      forall u : Real,
        (Set.uIcc a (Real.log (X : Real))) u ->
          HasDerivAt
            F
            (TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
            u := by
    intro u _hu
    dsimp [F]
    exact criticalLineEnergyPrimitive_hasDerivAt X u
  have hint :
      IntervalIntegrable
        (fun u : Real =>
          TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
        volume
        a
        (Real.log (X : Real)) :=
    criticalLineExpandedDensity_intervalIntegrable X a (Real.log (X : Real))
  unfold criticalLineTruncatedExpandedEnergy
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := a)
      (b := Real.log (X : Real))
      (f := F)
      (f' := fun u : Real =>
        TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
      hderiv
      hint

/--
The truncated expanded-energy integrals converge to `X / 3` as the lower
endpoint tends to `-infty`.
-/
theorem criticalLineTruncatedExpandedEnergy_tendsto_X_div_three
    (X : Nat)
    (hX : 0 < X) :
    Tendsto
      (fun a : Real =>
        criticalLineTruncatedExpandedEnergy X a)
      atBot
      (nhds ((X : Real) / 3)) := by
  have hftc :
      (fun a : Real =>
        criticalLineTruncatedExpandedEnergy X a)
        =
      (fun a : Real =>
        TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
            X (Real.log (X : Real))
          -
        TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X a) := by
    funext a
    exact criticalLineTruncatedExpandedEnergy_eq_primitive_sub X a
  have hconst :
      TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
          X (Real.log (X : Real)) =
        (X : Real) / 3 :=
    TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive_at_log_eq_X_div_three
      hX
  have htail :
      Tendsto
        (fun a : Real =>
          TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X a)
        atBot
        (nhds 0) :=
    TS192.Goldbach.criticalLineAmplitudeEnergyPrimitive_tendsto_atBot_zero X
  have hlim :
      Tendsto
        (fun a : Real =>
          TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
              X (Real.log (X : Real))
            -
          TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X a)
        atBot
        (nhds
          (TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
              X (Real.log (X : Real))
            -
          0)) :=
    tendsto_const_nhds.sub htail
  rw [hftc]
  simpa [hconst] using hlim

/--
Local contract for promoting the truncated-integral convergence into a named
improper-integral object.  TS193 proves the convergence theorem, but still does
not define or discharge the final improper Lebesgue integral object.
-/
structure CriticalLineImproperIntegralObjectContract
    (X : Nat) where
  improper_integral_statement :
    Prop
  truncated_convergence_consumes_statement :
    Tendsto
      (fun a : Real =>
        criticalLineTruncatedExpandedEnergy X a)
      atBot
      (nhds ((X : Real) / 3)) ->
        improper_integral_statement

/-- Ledger recording the TS193 truncated FTC bridge. -/
structure CriticalLineTruncatedFTCEnergyBridgeLedger where
  ts192_lower_tail_ledger :
    TS192.Goldbach.CriticalLinePrimitiveLowerTailLimitLedger

  primitive_derivative :
    forall X : Nat,
      forall u : Real,
        HasDerivAt
          (fun v : Real =>
            TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X v)
          (TS191.Goldbach.criticalLineAmplitudeEnergyExpandedDensity X u)
          u

  truncated_ftc :
    forall X : Nat,
      forall a : Real,
        criticalLineTruncatedExpandedEnergy X a =
        TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
            X (Real.log (X : Real))
          -
        TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X a

  truncated_integrals_tendsto :
    forall X : Nat,
      0 < X ->
        Tendsto
          (fun a : Real =>
            criticalLineTruncatedExpandedEnergy X a)
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

/-- Concrete TS193 truncated FTC energy bridge ledger. -/
noncomputable def criticalLineTruncatedFTCEnergyBridgeLedger :
    CriticalLineTruncatedFTCEnergyBridgeLedger where
  ts192_lower_tail_ledger :=
    TS192.Goldbach.criticalLinePrimitiveLowerTailLimitLedger
  primitive_derivative :=
    criticalLineEnergyPrimitive_hasDerivAt
  truncated_ftc :=
    criticalLineTruncatedExpandedEnergy_eq_primitive_sub
  truncated_integrals_tendsto :=
    criticalLineTruncatedExpandedEnergy_tendsto_X_div_three
  improper_integral_object_not_defined := True.intro
  wall0_measure_transport_not_discharged := True.intro
  mellin_fourier_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS193. -/
def CriticalLineTruncatedFTCEnergyBridgeTarget : Prop :=
  Nonempty CriticalLineTruncatedFTCEnergyBridgeLedger

/-- The TS193 truncated FTC energy bridge target is populated. -/
theorem criticalLineTruncatedFTCEnergyBridgeTarget :
    CriticalLineTruncatedFTCEnergyBridgeTarget :=
  Nonempty.intro criticalLineTruncatedFTCEnergyBridgeLedger

end Goldbach
end TS193
