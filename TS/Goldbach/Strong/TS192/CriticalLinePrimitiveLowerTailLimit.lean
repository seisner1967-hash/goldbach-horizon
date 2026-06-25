import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import TS.Goldbach.Strong.TS191.CriticalLineAmplitudeEnergyPrimitive

namespace TS192
namespace Goldbach

open Filter

/-!
# TS192 - Critical-Line Primitive Lower-Tail Limit

TS191 proved the algebraic core of the critical-line energy calculation:
the squared amplitude expands into elementary exponentials, and the natural
primitive evaluates to `X / 3` at the upper endpoint `log X`.

This sprint proves the missing lower-boundary value for that primitive:
as `u -> -infty`, the primitive tends to `0`.  This discharges the lower-tail
part of the future improper-energy computation without claiming the full
Lebesgue improper integral or the Wall 0 measure transport.
-/

/-- `exp (2*u)` tends to zero as `u -> -infty`. -/
theorem tendsto_exp_two_mul_atBot_zero :
    Tendsto (fun u : Real => Real.exp (2 * u)) atBot (nhds 0) := by
  have harg :
      Tendsto (fun u : Real => (2 : Real) * u) atBot atBot :=
    Tendsto.const_mul_atBot (by norm_num : (0 : Real) < 2) tendsto_id
  exact Real.tendsto_exp_atBot.comp harg

/-- `exp (3*u)` tends to zero as `u -> -infty`. -/
theorem tendsto_exp_three_mul_atBot_zero :
    Tendsto (fun u : Real => Real.exp (3 * u)) atBot (nhds 0) := by
  have harg :
      Tendsto (fun u : Real => (3 : Real) * u) atBot atBot :=
    Tendsto.const_mul_atBot (by norm_num : (0 : Real) < 3) tendsto_id
  exact Real.tendsto_exp_atBot.comp harg

/--
The TS191 energy primitive tends to zero at the lower tail.

This is the nontrivial boundary value needed before the primitive calculation
can be promoted to a genuine improper integral over `(-infty, log X]`.
-/
theorem criticalLineAmplitudeEnergyPrimitive_tendsto_atBot_zero
    (X : Nat) :
    Tendsto
      (fun u : Real =>
        TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X u)
      atBot
      (nhds 0) := by
  have h1 :
      Tendsto (fun u : Real => Real.exp u) atBot (nhds 0) :=
    Real.tendsto_exp_atBot
  have h2 :
      Tendsto (fun u : Real => Real.exp (2 * u)) atBot (nhds 0) :=
    tendsto_exp_two_mul_atBot_zero
  have h3 :
      Tendsto (fun u : Real => Real.exp (3 * u)) atBot (nhds 0) :=
    tendsto_exp_three_mul_atBot_zero
  have hlim :
      Tendsto
        (fun u : Real =>
          Real.exp u
            - (1 / (X : Real)) * Real.exp (2 * u)
            + (1 / (3 * ((X : Real) ^ 2))) * Real.exp (3 * u))
        atBot
        (nhds
          (0
            - (1 / (X : Real)) * 0
            + (1 / (3 * ((X : Real) ^ 2))) * 0)) :=
    (h1.sub (h2.const_mul (1 / (X : Real)))).add
      (h3.const_mul (1 / (3 * ((X : Real) ^ 2))))
  simpa [TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive] using hlim

/--
The completed boundary-value statement for the TS191 primitive.

This packages the lower-tail limit from TS192 with the upper-endpoint value
from TS191.  It is still not an improper-integral theorem.
-/
def CriticalLinePrimitiveBoundaryStatement
    (X : Nat) :
    Prop :=
  Tendsto
    (fun u : Real =>
      TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X u)
    atBot
    (nhds 0)
    /\
  (0 < X ->
    TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive
        X (Real.log (X : Real)) =
      (X : Real) / 3)

/-- The primitive has both boundary values required by the paper calculation. -/
theorem criticalLinePrimitiveBoundaryStatement
    (X : Nat) :
    CriticalLinePrimitiveBoundaryStatement X := by
  constructor
  case left =>
    exact criticalLineAmplitudeEnergyPrimitive_tendsto_atBot_zero X
  case right =>
    intro hX
    exact
      TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive_at_log_eq_X_div_three
        hX

/--
Local contract for the remaining improper-integral and FTC step.

The integral proposition is deliberately supplied as a field, so TS192 does
not hide the actual Lebesgue/improper-integral statement behind `True`.
-/
structure CriticalLineImproperEnergyFTCContract
    (X : Nat) where
  improper_integral_statement :
    Prop
  density_integrable_on_lower_interval :
    Prop
  improper_ftc_bridge :
    CriticalLinePrimitiveBoundaryStatement X ->
      improper_integral_statement

/-- Ledger recording the TS192 lower-tail limit bridge. -/
structure CriticalLinePrimitiveLowerTailLimitLedger where
  ts191_primitive_ledger :
    TS191.Goldbach.CriticalLineAmplitudeEnergyPrimitiveLedger

  lower_tail_limit :
    forall X : Nat,
      Tendsto
        (fun u : Real =>
          TS191.Goldbach.criticalLineAmplitudeEnergyPrimitive X u)
        atBot
        (nhds 0)

  boundary_statement :
    forall X : Nat,
      CriticalLinePrimitiveBoundaryStatement X

  improper_ftc_contract_registered :
    True

  full_improper_integral_not_proved :
    True

  wall0_measure_transport_not_discharged :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS192 lower-tail limit ledger. -/
noncomputable def criticalLinePrimitiveLowerTailLimitLedger :
    CriticalLinePrimitiveLowerTailLimitLedger where
  ts191_primitive_ledger :=
    TS191.Goldbach.criticalLineAmplitudeEnergyPrimitiveLedger
  lower_tail_limit :=
    criticalLineAmplitudeEnergyPrimitive_tendsto_atBot_zero
  boundary_statement :=
    criticalLinePrimitiveBoundaryStatement
  improper_ftc_contract_registered := True.intro
  full_improper_integral_not_proved := True.intro
  wall0_measure_transport_not_discharged := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS192. -/
def CriticalLinePrimitiveLowerTailLimitTarget : Prop :=
  Nonempty CriticalLinePrimitiveLowerTailLimitLedger

/-- The TS192 lower-tail limit target is populated. -/
theorem criticalLinePrimitiveLowerTailLimitTarget :
    CriticalLinePrimitiveLowerTailLimitTarget :=
  Nonempty.intro criticalLinePrimitiveLowerTailLimitLedger

end Goldbach
end TS192
