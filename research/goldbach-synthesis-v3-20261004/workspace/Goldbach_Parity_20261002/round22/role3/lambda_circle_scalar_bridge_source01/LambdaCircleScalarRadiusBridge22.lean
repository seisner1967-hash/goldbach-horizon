import LambdaCircleTruncationEnvelope22
import ScalarRadiusRealConnectors22

/-! SOURCE ONLY / PENDING_DEPENDENCIES_NOT_ELABORATED.
Both direct imports are prospective and require their own independent actual
compiler verdicts. This file identifies their literal closed real radii and
instantiates the true coefficient truncation theorem at the fixed point.
No numerical coefficient, Dirichlet quadrature, arithmetic sign or D_N bound
is computed or supplied as a premise. All prime powers remain in the actual
projectionAdditiveCoefficient of the imported circle theorem.
-/

noncomputable section

open GoldbachContinuous22 GoldbachComplexGammaMellin22
open GoldbachLambdaCircle22 GoldbachScalarRadius22

namespace GoldbachLambdaScalarBridge22

/-- The two amplitudes unfold to the same real expression. -/
theorem projectionAmplitude_eq_radiusAmplitude (a : ℝ) :
    projectionAmplitude a = radiusAmplitude a := by
  rfl

/-- The floor and the scalar decay use exactly the same arctangent. -/
theorem circleDecayFloor_eq_radiusDecay (a : ℝ) :
    circleDecayFloor a = radiusDecay a := by
  rfl

/-- Equality of the closed phase radii, with no numerical tolerance. -/
theorem lambdaCircleEpsilon_eq_radiusEpsilon (a H : ℝ) :
    lambdaCircleEpsilon a H = radiusEpsilon a H := by
  rfl

/-- Equality of the complete coefficient error radii. -/
theorem lambdaCircleCoefficientError_eq_radiusError (a H : ℝ) (N : ℕ) :
    lambdaCircleCoefficientError a H N = radiusError a H N := by
  rfl

/-- The imported integral estimate now uses the literal scalar radius. -/
theorem lambdaCircleCenteredCoefficient_error_le_radius {a H : ℝ}
    (ha : 0 < a) (hH : 0 ≤ H) (N : ℕ) :
    ‖lambdaCircleCenteredCoefficient a N - lambdaCircleTruncatedCoefficient a H N‖ ≤
      radiusError a H N := by
  rw [← lambdaCircleCoefficientError_eq_radiusError a H N]
  exact lambdaCircleCenteredCoefficient_error_le ha hH N

/-- The same bound retains the true von Mangoldt coefficient and all PP. -/
theorem lambdaCircleAdditiveCoefficient_error_le_radius {a H : ℝ}
    (ha : 0 < a) (hH : 0 ≤ H) (N : ℕ) :
    ‖(projectionAdditiveCoefficient N : ℂ) - lambdaCircleTruncatedCoefficient a H N‖ ≤
      radiusError a H N := by
  rw [← lambdaCircleCoefficientError_eq_radiusError a H N]
  exact lambdaCircleAdditiveCoefficient_error_le ha hH N

/-- Fixed-point truncation control of the centered integral; no evaluation. -/
theorem lambdaCircleCenteredCoefficient_point_error_lt_tau :
    ‖lambdaCircleCenteredCoefficient (1 / 100000000) 100000000 -
      lambdaCircleTruncatedCoefficient (1 / 100000000) 100000000000 100000000‖ <
        (1 : ℝ) / 1000000 := by
  have hb := lambdaCircleCenteredCoefficient_error_le_radius
    (a := pointA) (H := pointHeight) pointA_pos pointHeight_nonneg 100000000
  have h := hb.trans_lt error_point_lt_tau
  simpa only [pointA, pointHeight, pointTau] using h

/-- Fixed-point control of C_N versus the exact truncated Mellin integral. -/
theorem lambdaCircleAdditiveCoefficient_point_error_lt_tau :
    ‖(projectionAdditiveCoefficient 100000000 : ℂ) -
      lambdaCircleTruncatedCoefficient (1 / 100000000) 100000000000 100000000‖ <
        (1 : ℝ) / 1000000 := by
  have hb := lambdaCircleAdditiveCoefficient_error_le_radius
    (a := pointA) (H := pointHeight) pointA_pos pointHeight_nonneg 100000000
  have h := hb.trans_lt error_point_lt_tau
  simpa only [pointA, pointHeight, pointTau] using h

end GoldbachLambdaScalarBridge22

#print axioms GoldbachLambdaScalarBridge22.projectionAmplitude_eq_radiusAmplitude
#print axioms GoldbachLambdaScalarBridge22.circleDecayFloor_eq_radiusDecay
#print axioms GoldbachLambdaScalarBridge22.lambdaCircleEpsilon_eq_radiusEpsilon
#print axioms GoldbachLambdaScalarBridge22.lambdaCircleCoefficientError_eq_radiusError
#print axioms GoldbachLambdaScalarBridge22.lambdaCircleCenteredCoefficient_error_le_radius
#print axioms GoldbachLambdaScalarBridge22.lambdaCircleAdditiveCoefficient_error_le_radius
#print axioms GoldbachLambdaScalarBridge22.lambdaCircleCenteredCoefficient_point_error_lt_tau
#print axioms GoldbachLambdaScalarBridge22.lambdaCircleAdditiveCoefficient_point_error_lt_tau
