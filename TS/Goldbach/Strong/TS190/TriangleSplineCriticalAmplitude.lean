import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exponential
import TS.Goldbach.Strong.TS189.LogarithmicPullbackMellinFourierInterface

namespace TS190
namespace Goldbach

/-!
# TS190 - Triangle Spline Critical-Line Amplitude

TS189 defined the logarithmic pullback and the Mellin/Fourier amplitude
`F(exp u / X) * exp (c * u)` for an arbitrary real shift `c`.  This sprint
specializes that algebraic amplitude to the critical-line value `c = 1 / 2`.

The resulting profile

`triangleSpline (exp u / X) * exp (u / 2)`

is the real spatial shape that would be seen by a future explicit-formula
argument on the critical line.  TS190 proves its nonnegativity, its zero branch
after the logarithmic scale boundary, and its affine branch before the
boundary.

No measure transport, Riemann hypothesis, explicit formula, Plancherel, or
Goldbach theorem is claimed.
-/

/--
Triangle-spline Mellin/Fourier amplitude specialized to the critical-line
shift `c = 1 / 2`.
-/
noncomputable def triangleSplineCriticalAmplitude
    (X : Nat)
    (u : Real) :
    Real :=
  TS189.Goldbach.triangleSplineMellinFourierAmplitude
    (X : Real) (1 / 2 : Real) u

/-- The critical-line amplitude is nonnegative. -/
theorem triangleSplineCriticalAmplitude_nonneg
    (X : Nat)
    (u : Real) :
    0 <= triangleSplineCriticalAmplitude X u := by
  unfold triangleSplineCriticalAmplitude
  exact TS189.Goldbach.triangleSplineMellinFourierAmplitude_nonneg
    (X : Real) (1 / 2 : Real) u

/--
Past the logarithmic scale boundary, equivalently `(X : Real) <= exp u`, the
critical-line amplitude vanishes.
-/
theorem triangleSplineCriticalAmplitude_eq_zero_of_X_le_exp
    {X : Nat}
    {u : Real}
    (hX : 0 < X)
    (hXu : (X : Real) <= Real.exp u) :
    triangleSplineCriticalAmplitude X u = 0 := by
  unfold triangleSplineCriticalAmplitude
  exact TS189.Goldbach.triangleSplineMellinFourierAmplitude_eq_zero_of_X_le_exp
    (X := (X : Real))
    (c := (1 / 2 : Real))
    (u := u)
    (by exact_mod_cast hX)
    hXu

/--
On the support side `exp u <= X`, the critical-line amplitude is the affine
spline branch multiplied by the critical exponential weight.
-/
theorem triangleSplineCriticalAmplitude_eq_affine_of_exp_le_X
    {X : Nat}
    {u : Real}
    (hX : 0 < X)
    (huX : Real.exp u <= (X : Real)) :
    triangleSplineCriticalAmplitude X u =
      (1 - Real.exp u / (X : Real)) * Real.exp (u / 2) := by
  unfold triangleSplineCriticalAmplitude
  rw [TS189.Goldbach.triangleSplineMellinFourierAmplitude_eq_affine_of_exp_le_X
    (X := (X : Real))
    (c := (1 / 2 : Real))
    (u := u)
    (by exact_mod_cast hX)
    huX]
  rw [show ((1 / 2 : Real) * u) = u / 2 by ring]

/-- Ledger recording the TS190 critical-line amplitude specialization. -/
structure TriangleSplineCriticalAmplitudeLedger where
  ts189_interface :
    TS189.Goldbach.LogarithmicPullbackMellinFourierInterfaceLedger

  critical_amplitude_defined :
    True

  critical_amplitude_nonneg :
    forall X : Nat,
      forall u : Real,
        0 <= triangleSplineCriticalAmplitude X u

  critical_amplitude_zero_branch :
    forall {X : Nat},
      forall {u : Real},
        0 < X ->
          (X : Real) <= Real.exp u ->
            triangleSplineCriticalAmplitude X u = 0

  critical_amplitude_affine_branch :
    forall {X : Nat},
      forall {u : Real},
        0 < X ->
          Real.exp u <= (X : Real) ->
            triangleSplineCriticalAmplitude X u =
              (1 - Real.exp u / (X : Real)) * Real.exp (u / 2)

  critical_line_specialization_not_rh :
    True

  wall0_measure_transport_not_discharged :
    True

  explicit_formula_not_proved :
    True

  plancherel_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS190 critical-line amplitude ledger. -/
noncomputable def triangleSplineCriticalAmplitudeLedger :
    TriangleSplineCriticalAmplitudeLedger where
  ts189_interface :=
    TS189.Goldbach.logarithmicPullbackMellinFourierInterfaceLedger
  critical_amplitude_defined := True.intro
  critical_amplitude_nonneg := triangleSplineCriticalAmplitude_nonneg
  critical_amplitude_zero_branch := by
    intro X u hX hXu
    exact triangleSplineCriticalAmplitude_eq_zero_of_X_le_exp hX hXu
  critical_amplitude_affine_branch := by
    intro X u hX huX
    exact triangleSplineCriticalAmplitude_eq_affine_of_exp_le_X hX huX
  critical_line_specialization_not_rh := True.intro
  wall0_measure_transport_not_discharged := True.intro
  explicit_formula_not_proved := True.intro
  plancherel_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS190. -/
def TriangleSplineCriticalAmplitudeTarget : Prop :=
  Nonempty TriangleSplineCriticalAmplitudeLedger

/-- The TS190 critical-line amplitude target is populated. -/
theorem triangleSplineCriticalAmplitudeTarget :
    TriangleSplineCriticalAmplitudeTarget :=
  Nonempty.intro triangleSplineCriticalAmplitudeLedger

end Goldbach
end TS190
