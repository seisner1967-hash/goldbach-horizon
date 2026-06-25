import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TS.Goldbach.Strong.TS190.TriangleSplineCriticalAmplitude

namespace TS191
namespace Goldbach

/-!
# TS191 - Critical-Line Amplitude Energy Primitive

TS190 produced the critical-line logarithmic amplitude

`(1 - exp u / X) * exp (u / 2)`

on the support side `exp u <= X`.  This sprint isolates the exact algebraic
energy calculation behind the paper identity

`int_{-infty}^{log X} A(u)^2 du = X / 3`.

It proves the pointwise square expansion on the support and proves that the
natural primitive evaluates to `X / 3` at the upper endpoint `log X`.  The
remaining improper-integral step from `-infty` is recorded as a local contract;
the Wall 0 measure transport and Mellin/Fourier equivalence remain unproved.
-/

/-- Squared critical-line amplitude. -/
noncomputable def criticalLineAmplitudeEnergyDensity
    (X : Nat)
    (u : Real) :
    Real :=
  (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2

/-- Expanded exponential density on the support side. -/
noncomputable def criticalLineAmplitudeEnergyExpandedDensity
    (X : Nat)
    (u : Real) :
    Real :=
  Real.exp u
    - (2 / (X : Real)) * Real.exp (2 * u)
    + (1 / ((X : Real) ^ 2)) * Real.exp (3 * u)

/-- Primitive for the expanded critical-line energy density. -/
noncomputable def criticalLineAmplitudeEnergyPrimitive
    (X : Nat)
    (u : Real) :
    Real :=
  Real.exp u
    - (1 / (X : Real)) * Real.exp (2 * u)
    + (1 / (3 * ((X : Real) ^ 2))) * Real.exp (3 * u)

/-- The squared critical-line amplitude expands into elementary exponentials. -/
theorem criticalLineAmplitudeEnergyDensity_eq_expanded_of_exp_le_X
    {X : Nat}
    {u : Real}
    (hX : 0 < X)
    (huX : Real.exp u <= (X : Real)) :
    criticalLineAmplitudeEnergyDensity X u =
      criticalLineAmplitudeEnergyExpandedDensity X u := by
  have hXr : Not ((X : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hX)
  have h_exp_two :
      Real.exp (2 * u) = (Real.exp u) ^ 2 := by
    rw [show (2 : Real) * u = u + u by ring]
    rw [Real.exp_add]
    ring
  have h_exp_three :
      Real.exp (3 * u) = (Real.exp u) ^ 3 := by
    rw [show (3 : Real) * u = (u + u) + u by ring]
    rw [Real.exp_add, Real.exp_add]
    ring
  have h_half_sq :
      (Real.exp (u / 2)) ^ 2 = Real.exp u := by
    rw [sq, <- Real.exp_add]
    congr 1
    ring
  unfold criticalLineAmplitudeEnergyDensity
  rw [TS190.Goldbach.triangleSplineCriticalAmplitude_eq_affine_of_exp_le_X hX huX]
  unfold criticalLineAmplitudeEnergyExpandedDensity
  rw [h_exp_two, h_exp_three]
  rw [show ((1 - Real.exp u / (X : Real)) * Real.exp (u / 2)) ^ 2 =
      (1 - Real.exp u / (X : Real)) ^ 2 * (Real.exp (u / 2)) ^ 2 by ring]
  rw [h_half_sq]
  field_simp [hXr]
  ring

/--
At the logarithmic endpoint, the primitive has the exact value `X / 3`.

This is the algebraic heart of the critical-line energy calculation.
-/
theorem criticalLineAmplitudeEnergyPrimitive_at_log_eq_X_div_three
    {X : Nat}
    (hX : 0 < X) :
    criticalLineAmplitudeEnergyPrimitive X (Real.log (X : Real)) =
      (X : Real) / 3 := by
  have hXpos : 0 < (X : Real) := by
    exact_mod_cast hX
  have hXne : Not ((X : Real) = 0) := ne_of_gt hXpos
  have h_exp_one :
      Real.exp (Real.log (X : Real)) = (X : Real) := by
    exact Real.exp_log hXpos
  have h_exp_two :
      Real.exp (2 * Real.log (X : Real)) = (X : Real) ^ 2 := by
    rw [show (2 : Real) * Real.log (X : Real) =
        Real.log (X : Real) + Real.log (X : Real) by ring]
    rw [Real.exp_add, h_exp_one]
    ring
  have h_exp_three :
      Real.exp (3 * Real.log (X : Real)) = (X : Real) ^ 3 := by
    rw [show (3 : Real) * Real.log (X : Real) =
        (Real.log (X : Real) + Real.log (X : Real)) +
          Real.log (X : Real) by ring]
    rw [Real.exp_add, Real.exp_add, h_exp_one]
    ring
  unfold criticalLineAmplitudeEnergyPrimitive
  rw [h_exp_one, h_exp_two, h_exp_three]
  field_simp [hXne]
  ring

/--
Local contract for the remaining improper-integral step.

TS191 proves the density expansion and endpoint primitive value.  To promote
those facts into an integral over `(-infty, log X]`, a future sprint must
provide the lower-tail vanishing and the exact improper-integral bridge.
-/
structure CriticalLineAmplitudeImproperEnergyContract
    (X : Nat) where
  lower_tail_primitive_vanishes :
    Prop
  improper_integral_equals_primitive_endpoint :
    Prop
  energy_equals_X_div_three :
    Prop

/-- Ledger recording the TS191 critical-line energy primitive calculation. -/
structure CriticalLineAmplitudeEnergyPrimitiveLedger where
  ts190_critical_amplitude :
    TS190.Goldbach.TriangleSplineCriticalAmplitudeLedger

  density_expansion :
    forall {X : Nat},
      forall {u : Real},
        0 < X ->
          Real.exp u <= (X : Real) ->
            criticalLineAmplitudeEnergyDensity X u =
              criticalLineAmplitudeEnergyExpandedDensity X u

  primitive_endpoint :
    forall {X : Nat},
      0 < X ->
        criticalLineAmplitudeEnergyPrimitive X (Real.log (X : Real)) =
          (X : Real) / 3

  improper_energy_contract_registered :
    True

  improper_energy_not_proved :
    True

  wall0_measure_transport_not_discharged :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS191 critical-line energy primitive ledger. -/
noncomputable def criticalLineAmplitudeEnergyPrimitiveLedger :
    CriticalLineAmplitudeEnergyPrimitiveLedger where
  ts190_critical_amplitude :=
    TS190.Goldbach.triangleSplineCriticalAmplitudeLedger
  density_expansion := by
    intro X u hX huX
    exact criticalLineAmplitudeEnergyDensity_eq_expanded_of_exp_le_X hX huX
  primitive_endpoint := by
    intro X hX
    exact criticalLineAmplitudeEnergyPrimitive_at_log_eq_X_div_three hX
  improper_energy_contract_registered := True.intro
  improper_energy_not_proved := True.intro
  wall0_measure_transport_not_discharged := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS191. -/
def CriticalLineAmplitudeEnergyPrimitiveTarget : Prop :=
  Nonempty CriticalLineAmplitudeEnergyPrimitiveLedger

/-- The TS191 critical-line energy primitive target is populated. -/
theorem criticalLineAmplitudeEnergyPrimitiveTarget :
    CriticalLineAmplitudeEnergyPrimitiveTarget :=
  Nonempty.intro criticalLineAmplitudeEnergyPrimitiveLedger

end Goldbach
end TS191
