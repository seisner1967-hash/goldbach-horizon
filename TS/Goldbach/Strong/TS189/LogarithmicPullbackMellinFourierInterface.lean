import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TS.Goldbach.Strong.TS162.TriangleSplineTraceKernelInstantiation
import TS.Goldbach.Strong.TS187.AnalyticFrontierTransformCompatibilityLedger

namespace TS189
namespace Goldbach

/-!
# TS189 - Logarithmic Pullback Mellin Fourier Interface

TS187 isolated Wall 0: the Mellin/Fourier compatibility gap.  Classical
explicit formulae live naturally in Mellin and Dirichlet-series coordinates,
while the triangle-spline kernel has been identified through the real Fourier
transform.

This sprint proves only the algebraic part of the logarithmic substitution.
It defines the coordinate maps `logCoord` and `expCoord`, proves their basic
round trips, defines the triangle-spline logarithmic pullback
`triangleSpline (exp u / X)`, proves its support, affine branch, and
nonnegativity facts, and defines the critical Mellin/Fourier amplitude by
multiplication by `exp (c * u)`.

The measure transport `dx / x = du`, the Mellin-as-Fourier integral
equivalence, and analytic inversion remain explicit local contracts.
-/

/-- Logarithmic coordinate map from the positive line to the real line. -/
noncomputable def logCoord
    (x : Real) :
    Real :=
  Real.log x

/-- Exponential coordinate map from the real line to the positive line. -/
noncomputable def expCoord
    (u : Real) :
    Real :=
  Real.exp u

/-- The logarithmic coordinate map is a left inverse to the exponential map. -/
theorem logCoord_expCoord
    (u : Real) :
    logCoord (expCoord u) = u := by
  simp [logCoord, expCoord]

/-- The exponential coordinate map is a right inverse on positive reals. -/
theorem expCoord_logCoord
    {x : Real}
    (hx : 0 < x) :
    expCoord (logCoord x) = x := by
  simpa [logCoord, expCoord] using Real.exp_log hx

/--
The algebraic real logarithmic pullback of a test function `F` at shift `c`.
It is the amplitude `F(exp u) * exp (c * u)` before the Fourier oscillation.
-/
noncomputable def realLogarithmicPullback
    (F : Real -> Real)
    (c : Real)
    (u : Real) :
    Real :=
  F (Real.exp u) * Real.exp (c * u)

/-- The real logarithmic pullback preserves pointwise nonnegativity. -/
theorem realLogarithmicPullback_nonneg
    (F : Real -> Real)
    (c u : Real)
    (hF : 0 <= F (Real.exp u)) :
    0 <= realLogarithmicPullback F c u := by
  unfold realLogarithmicPullback
  exact mul_nonneg hF (le_of_lt (Real.exp_pos (c * u)))

/-- Triangle-spline logarithmic pullback at scale `X`. -/
noncomputable def triangleSplineLogPullback
    (X : Real)
    (u : Real) :
    Real :=
  TS42.MellinJackson.triangleSpline (Real.exp u / X)

/-- The triangle-spline logarithmic pullback is nonnegative. -/
theorem triangleSplineLogPullback_nonneg
    (X u : Real) :
    0 <= triangleSplineLogPullback X u := by
  unfold triangleSplineLogPullback
  exact TS162.Goldbach.triangleSpline_nonneg _

/-- The logarithmic pullback vanishes once `exp u` reaches the scale `X`. -/
theorem triangleSplineLogPullback_eq_zero_of_X_le_exp
    {X u : Real}
    (hX : 0 < X)
    (hXu : X <= Real.exp u) :
    triangleSplineLogPullback X u = 0 := by
  unfold triangleSplineLogPullback
  have hratio :
      1 <= Real.exp u / X := by
    rw [one_le_div hX]
    exact hXu
  have habs :
      1 <= |Real.exp u / X| :=
    le_trans hratio (le_abs_self _)
  exact TS162.Goldbach.triangleSpline_eq_zero_of_one_le_abs habs

/-- On the support side `exp u <= X`, the logarithmic pullback is affine. -/
theorem triangleSplineLogPullback_eq_one_sub_of_exp_le_X
    {X u : Real}
    (hX : 0 < X)
    (huX : Real.exp u <= X) :
    triangleSplineLogPullback X u =
      1 - Real.exp u / X := by
  unfold triangleSplineLogPullback
  apply TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
  case hx0 =>
    exact div_nonneg (le_of_lt (Real.exp_pos u)) (le_of_lt hX)
  case hx1 =>
    rw [div_le_one hX]
    exact huX

/--
Critical Mellin/Fourier amplitude obtained by multiplying the logarithmic
pullback by the real exponential shift `exp (c * u)`.
-/
noncomputable def triangleSplineMellinFourierAmplitude
    (X c u : Real) :
    Real :=
  triangleSplineLogPullback X u * Real.exp (c * u)

/-- The critical Mellin/Fourier amplitude is nonnegative. -/
theorem triangleSplineMellinFourierAmplitude_nonneg
    (X c u : Real) :
    0 <= triangleSplineMellinFourierAmplitude X c u := by
  unfold triangleSplineMellinFourierAmplitude
  exact mul_nonneg
    (triangleSplineLogPullback_nonneg X u)
    (le_of_lt (Real.exp_pos (c * u)))

/-- The critical amplitude vanishes once `exp u` reaches the scale `X`. -/
theorem triangleSplineMellinFourierAmplitude_eq_zero_of_X_le_exp
    {X c u : Real}
    (hX : 0 < X)
    (hXu : X <= Real.exp u) :
    triangleSplineMellinFourierAmplitude X c u = 0 := by
  unfold triangleSplineMellinFourierAmplitude
  rw [triangleSplineLogPullback_eq_zero_of_X_le_exp hX hXu]
  simp

/-- On the support side, the critical amplitude has the expected affine form. -/
theorem triangleSplineMellinFourierAmplitude_eq_affine_of_exp_le_X
    {X c u : Real}
    (hX : 0 < X)
    (huX : Real.exp u <= X) :
    triangleSplineMellinFourierAmplitude X c u =
      (1 - Real.exp u / X) * Real.exp (c * u) := by
  unfold triangleSplineMellinFourierAmplitude
  rw [triangleSplineLogPullback_eq_one_sub_of_exp_le_X hX huX]

/--
Local contract for the measure-theoretic part of Wall 0.

This names the obligations that remain after the algebraic pullback has been
proved: measure transport, Mellin-as-Fourier equivalence, explicit-formula
compatibility, and convergence/inversion.
-/
structure LogPullbackMeasureTransportContract where
  wall0_contract :
    TS187.Goldbach.MellinFourierDiffeomorphismContract
  measure_transport_dx_over_x_eq_du :
    Prop
  mellin_as_fourier_equivalence :
    Prop
  explicit_formula_compatibility :
    Prop
  convergence_and_inversion :
    Prop

/-- Evidence package required to discharge the TS189 measure contract. -/
structure LogPullbackMeasureTransportEvidence
    (contract : LogPullbackMeasureTransportContract) where
  wall0_evidence :
    TS187.Goldbach.MellinFourierDiffeomorphismEvidence
      contract.wall0_contract
  measure_transport :
    contract.measure_transport_dx_over_x_eq_du
  mellin_as_fourier :
    contract.mellin_as_fourier_equivalence
  explicit_formula :
    contract.explicit_formula_compatibility
  convergence_and_inversion :
    contract.convergence_and_inversion

/-- Ledger recording the TS189 logarithmic-pullback interface. -/
structure LogarithmicPullbackMellinFourierInterfaceLedger where
  ts187_frontier :
    TS187.Goldbach.AnalyticFrontierTransformCompatibilityLedger

  log_exp_roundtrip :
    forall u : Real,
      logCoord (expCoord u) = u

  exp_log_roundtrip :
    forall {x : Real},
      0 < x ->
        expCoord (logCoord x) = x

  pullback_nonnegative :
    forall X u : Real,
      0 <= triangleSplineLogPullback X u

  pullback_support_zero :
    forall {X u : Real},
      0 < X ->
        X <= Real.exp u ->
          triangleSplineLogPullback X u = 0

  pullback_affine_on_support :
    forall {X u : Real},
      0 < X ->
        Real.exp u <= X ->
          triangleSplineLogPullback X u =
            1 - Real.exp u / X

  amplitude_nonnegative :
    forall X c u : Real,
      0 <= triangleSplineMellinFourierAmplitude X c u

  measure_transport_contract_registered :
    True

  measure_transport_evidence_not_supplied :
    True

  wall0_not_discharged :
    True

  explicit_formula_not_proved :
    True

  plancherel_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS189 logarithmic-pullback interface ledger. -/
noncomputable def logarithmicPullbackMellinFourierInterfaceLedger :
    LogarithmicPullbackMellinFourierInterfaceLedger where
  ts187_frontier :=
    TS187.Goldbach.analyticFrontierTransformCompatibilityLedger
  log_exp_roundtrip := logCoord_expCoord
  exp_log_roundtrip := by
    intro x hx
    exact expCoord_logCoord hx
  pullback_nonnegative := triangleSplineLogPullback_nonneg
  pullback_support_zero := by
    intro X u hX hXu
    exact triangleSplineLogPullback_eq_zero_of_X_le_exp hX hXu
  pullback_affine_on_support := by
    intro X u hX huX
    exact triangleSplineLogPullback_eq_one_sub_of_exp_le_X hX huX
  amplitude_nonnegative := triangleSplineMellinFourierAmplitude_nonneg
  measure_transport_contract_registered := True.intro
  measure_transport_evidence_not_supplied := True.intro
  wall0_not_discharged := True.intro
  explicit_formula_not_proved := True.intro
  plancherel_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS189. -/
def LogarithmicPullbackMellinFourierInterfaceTarget : Prop :=
  Nonempty LogarithmicPullbackMellinFourierInterfaceLedger

/-- The TS189 logarithmic-pullback interface target is populated. -/
theorem logarithmicPullbackMellinFourierInterfaceTarget :
    LogarithmicPullbackMellinFourierInterfaceTarget :=
  Nonempty.intro logarithmicPullbackMellinFourierInterfaceLedger

end Goldbach
end TS189
