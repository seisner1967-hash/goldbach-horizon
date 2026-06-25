import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.Jacobian
import TS.Goldbach.Strong.TS195.CriticalLineActualImproperEnergyObject

namespace TS196
namespace Goldbach

open MeasureTheory

/-!
# TS196 - Critical-Line Compact Change-of-Variables Probe

TS189 named Wall 0: the Mellin/Fourier logarithmic-coordinate gap.  TS190-TS195
then computed the critical-line energy in logarithmic coordinates and packaged
the limit value `X / 3`.

This sprint attacks the compact, finite-endpoint part of Wall 0.  It does not
prove the full improper transport `dx / x = du`, and it does not identify the
Mellin and Fourier transforms.  Instead it proves the local compact change of
variables for the concrete energy density:

`u -> x = exp u`.

On compact intervals ending at `log X`, the square of the critical-line
amplitude is exactly the Jacobian-weighted pullback of the original
triangle-spline square density.  Mathlib's one-dimensional Jacobian theorem
then gives the corresponding compact set-integral identity.

No Plancherel, explicit formula, zeta-zero summability, circle-method
correlation, or Goldbach theorem is claimed.
-/

/-- Original-coordinate square density corresponding to the triangle spline at scale `X`. -/
noncomputable def criticalLineXSideEnergyDensity
    (X : Nat)
    (x : Real) :
    Real :=
  (TS42.MellinJackson.triangleSpline (x / (X : Real))) ^ 2

/-- Jacobian-weighted logarithmic pullback of the original-coordinate square density. -/
noncomputable def criticalLineCompactLogEnergyDensity
    (X : Nat)
    (u : Real) :
    Real :=
  Real.exp u * criticalLineXSideEnergyDensity X (Real.exp u)

/--
Pointwise algebraic identity: the actual critical-line amplitude squared is the
Jacobian-weighted logarithmic pullback of the original-coordinate square
density.
-/
theorem criticalLineActualSquare_eq_compactLogDensity
    (X : Nat)
    (u : Real) :
    (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2 =
      criticalLineCompactLogEnergyDensity X u := by
  unfold TS190.Goldbach.triangleSplineCriticalAmplitude
  unfold TS189.Goldbach.triangleSplineMellinFourierAmplitude
  unfold TS189.Goldbach.triangleSplineLogPullback
  unfold criticalLineCompactLogEnergyDensity
  unfold criticalLineXSideEnergyDensity
  set y : Real :=
    TS42.MellinJackson.triangleSpline (Real.exp u / (X : Real))
  have hexp :
      Real.exp ((1 / 2 : Real) * u) ^ 2 = Real.exp u := by
    rw [sq, <- Real.exp_add]
    congr
    ring
  calc
    (y * Real.exp ((1 / 2 : Real) * u)) ^ 2 =
        y ^ 2 * Real.exp ((1 / 2 : Real) * u) ^ 2 := by
      ring
    _ = y ^ 2 * Real.exp u := by
      rw [hexp]
    _ = Real.exp u * y ^ 2 := by
      ring

/-- The exponential map sends the compact logarithmic interval to the original interval. -/
theorem exp_image_Icc_log
    {X : Nat}
    {a : Real}
    (hX : 0 < X)
    (_ha : a <= Real.log (X : Real)) :
    Real.exp '' Set.Icc a (Real.log (X : Real)) =
      Set.Icc (Real.exp a) (X : Real) := by
  ext x
  constructor
  next =>
    intro hximg
    apply Exists.elim hximg
    intro u hu_and
    have hu : (Set.Icc a (Real.log (X : Real))) u := hu_and.1
    have hx_eq : Real.exp u = x := hu_and.2
    rw [<- hx_eq]
    exact And.intro
      (Real.exp_le_exp.mpr hu.1)
      (by
        have h_exp :
            Real.exp u <= Real.exp (Real.log (X : Real)) :=
          Real.exp_le_exp.mpr hu.2
        have hXpos : 0 < (X : Real) := by
          exact_mod_cast hX
        simpa [Real.exp_log hXpos] using h_exp)
  next =>
    intro hx
    have hXpos : 0 < (X : Real) := by
      exact_mod_cast hX
    have hxpos : 0 < x :=
      lt_of_lt_of_le (Real.exp_pos a) hx.1
    refine Exists.intro (Real.log x) ?_
    exact And.intro
      (And.intro
        (by
          have h_exp :
              Real.exp a <= Real.exp (Real.log x) := by
            simpa [Real.exp_log hxpos] using hx.1
          exact Real.exp_le_exp.mp h_exp)
        (by
          have h_exp :
              Real.exp (Real.log x) <= Real.exp (Real.log (X : Real)) := by
            simpa [Real.exp_log hxpos, Real.exp_log hXpos] using hx.2
          exact Real.exp_le_exp.mp h_exp))
      (Real.exp_log hxpos)

/-- The exponential map has derivative `exp u` on the compact interval. -/
theorem exp_hasDerivWithinAt_Icc
    (a b u : Real)
    (_hu : (Set.Icc a b) u) :
    HasDerivWithinAt Real.exp (Real.exp u) (Set.Icc a b) u := by
  exact (Real.hasDerivAt_exp u).hasDerivWithinAt

/-- The exponential map is injective on every compact interval. -/
theorem exp_injOn_Icc
    (a b : Real) :
    Set.InjOn Real.exp (Set.Icc a b) := by
  exact Real.exp_injective.injOn

/--
Compact Wall 0 change of variables for the original-coordinate square density.

This is a set-integral statement over compact intervals.  It is deliberately
not the full improper statement and not the Mellin/Fourier transform
equivalence.
-/
theorem compactChangeOfVariables_xSide_eq_logSide
    (X : Nat)
    (hX : 0 < X)
    {a : Real}
    (ha : a <= Real.log (X : Real)) :
    MeasureTheory.integral
        (volume.restrict (Set.Icc (Real.exp a) (X : Real)))
        (fun x : Real => criticalLineXSideEnergyDensity X x) =
      MeasureTheory.integral
        (volume.restrict (Set.Icc a (Real.log (X : Real))))
        (fun u : Real => criticalLineCompactLogEnergyDensity X u) := by
  have hcov :=
    integral_image_eq_integral_abs_deriv_smul
      (s := Set.Icc a (Real.log (X : Real)))
      (f := Real.exp)
      (f' := Real.exp)
      measurableSet_Icc
      (by
        intro u hu
        exact exp_hasDerivWithinAt_Icc a (Real.log (X : Real)) u hu)
      (exp_injOn_Icc a (Real.log (X : Real)))
      (criticalLineXSideEnergyDensity X)
  rw [exp_image_Icc_log hX ha] at hcov
  simpa [criticalLineCompactLogEnergyDensity, abs_of_pos (Real.exp_pos _)] using hcov

/--
The compact logarithmic set integral of the actual squared amplitude equals the
compact original-coordinate square-energy integral.
-/
theorem compactActualEnergy_setIntegral_eq_xSide
    (X : Nat)
    (hX : 0 < X)
    {a : Real}
    (ha : a <= Real.log (X : Real)) :
    MeasureTheory.integral
        (volume.restrict (Set.Icc a (Real.log (X : Real))))
        (fun u : Real =>
          (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2) =
      MeasureTheory.integral
        (volume.restrict (Set.Icc (Real.exp a) (X : Real)))
        (fun x : Real => criticalLineXSideEnergyDensity X x) := by
  calc
    MeasureTheory.integral
        (volume.restrict (Set.Icc a (Real.log (X : Real))))
        (fun u : Real =>
          (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2) =
        MeasureTheory.integral
          (volume.restrict (Set.Icc a (Real.log (X : Real))))
          (fun u : Real => criticalLineCompactLogEnergyDensity X u) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u _hu
      exact criticalLineActualSquare_eq_compactLogDensity X u
    _ = MeasureTheory.integral
          (volume.restrict (Set.Icc (Real.exp a) (X : Real)))
          (fun x : Real => criticalLineXSideEnergyDensity X x) := by
      exact (compactChangeOfVariables_xSide_eq_logSide X hX ha).symm

/-- Outcome marker for the TS196 compact change-of-variables probe. -/
inductive CompactChangeOfVariablesProbeOutcome where
  | compactSetIntegralChangeOfVariablesProved
  | intervalIntegralImproperBridgeStillOpen
  deriving DecidableEq, Repr

/-- Ledger recording the compact Wall 0 progress made in TS196. -/
structure CriticalLineCompactChangeOfVariablesLedger where
  ts195_energy_object :
    TS195.Goldbach.CriticalLineActualImproperEnergyObjectLedger

  pointwise_square_pullback :
    forall X : Nat,
      forall u : Real,
        (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2 =
          criticalLineCompactLogEnergyDensity X u

  compact_cov_proved :
    forall (X : Nat),
      0 < X ->
        forall {a : Real},
          a <= Real.log (X : Real) ->
            MeasureTheory.integral
              (volume.restrict (Set.Icc a (Real.log (X : Real))))
              (fun u : Real =>
                (TS190.Goldbach.triangleSplineCriticalAmplitude X u) ^ 2) =
              MeasureTheory.integral
                (volume.restrict (Set.Icc (Real.exp a) (X : Real)))
                (fun x : Real => criticalLineXSideEnergyDensity X x)

  compact_cov_outcome :
    CompactChangeOfVariablesProbeOutcome

  intervalIntegral_improper_bridge_not_proved :
    True

  wall0_general_measure_transport_not_proved :
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

/-- Concrete TS196 compact change-of-variables ledger. -/
noncomputable def criticalLineCompactChangeOfVariablesLedger :
    CriticalLineCompactChangeOfVariablesLedger where
  ts195_energy_object :=
    TS195.Goldbach.criticalLineActualImproperEnergyObjectLedger
  pointwise_square_pullback :=
    criticalLineActualSquare_eq_compactLogDensity
  compact_cov_proved := by
    intro X hX a ha
    exact compactActualEnergy_setIntegral_eq_xSide X hX ha
  compact_cov_outcome :=
    CompactChangeOfVariablesProbeOutcome.compactSetIntegralChangeOfVariablesProved
  intervalIntegral_improper_bridge_not_proved := True.intro
  wall0_general_measure_transport_not_proved := True.intro
  haar_transport_not_proved := True.intro
  mellin_fourier_equivalence_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS196. -/
def CriticalLineCompactChangeOfVariablesTarget : Prop :=
  Nonempty CriticalLineCompactChangeOfVariablesLedger

/-- The TS196 compact change-of-variables target is populated. -/
theorem criticalLineCompactChangeOfVariablesTarget :
    CriticalLineCompactChangeOfVariablesTarget :=
  Nonempty.intro criticalLineCompactChangeOfVariablesLedger

end Goldbach
end TS196
