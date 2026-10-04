import ThermalProjectionIdentity22
import ComplexGammaMellinLambdaTail22
import ComplexGammaCircleGeometry22
import Mathlib.MeasureTheory.Integral.Periodic

/-! SOURCE ONLY / PENDING_DEPENDENCIES.
Identity13 and Envelope11 are actual independent compiler successes.
Lambda30 (repaired SOURCE02), weighted Lambda tails16 and circle geometry25
are prospective imports: this source has not been elaborated. The actual
Lambda series, including all prime powers, is retained. Periodicity is proved
only for that series and its integer character, never for principal powers or
the truncated Mellin kernel. No arithmetic sign or D_N claim is made.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open GoldbachContinuous22 GoldbachComplexGammaMellin22

namespace GoldbachLambdaCircle22

def lambdaCircleTrace (a theta : ℝ) : ℂ :=
  lambdaMellinThermal (circleMellinPoint a theta)

def lambdaCircleTruncatedTrace (a H theta : ℝ) : ℂ :=
  lambdaMellinTruncated (circleMellinPoint a theta) H

def lambdaCircleCenteredCoefficient (a : ℝ) (N : ℕ) : ℂ :=
  ((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ theta : ℝ in (-Real.pi)..Real.pi,
      lambdaCircleTrace a theta ^ 2 * projectionCharacter N theta

def lambdaCircleTruncatedCoefficient (a H : ℝ) (N : ℕ) : ℂ :=
  ((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ theta : ℝ in (-Real.pi)..Real.pi,
      lambdaCircleTruncatedTrace a H theta ^ 2 * projectionCharacter N theta

def lambdaCircleEpsilon (a H : ℝ) : ℝ :=
  24 * Real.exp (-circleDecayFloor a * H) /
    (Real.pi * a ^ 2 * circleDecayFloor a)

def lambdaCircleCoefficientError (a H : ℝ) (N : ℕ) : ℝ :=
  Real.exp (a * (N : ℝ)) *
    (2 * projectionAmplitude a * lambdaCircleEpsilon a H + lambdaCircleEpsilon a H ^ 2)

/-- The thermal series is exactly the already validated heat trace. -/
theorem lambdaCircleTerm_eq_heatTerm (a theta : ℝ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (-((n : ℂ) * circleMellinPoint a theta)) =
        projectionHeatTerm a theta n := by
  have he : -((n : ℂ) * circleMellinPoint a theta) =
      (n : ℂ) * ((-a : ℝ) : ℂ) + ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
    unfold circleMellinPoint
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul, ← Complex.ofReal_exp]
  unfold projectionHeatTerm projectionHeatRatio
  ring

theorem lambdaCircleTrace_eq_heatTrace (a theta : ℝ) :
    lambdaCircleTrace a theta = projectionHeatTrace a theta := by
  unfold lambdaCircleTrace lambdaMellinThermal projectionHeatTrace
  exact tsum_congr (lambdaCircleTerm_eq_heatTerm a theta)

/-- Integer characters are genuinely periodic; this says nothing about cpow. -/
theorem signedCircleCharacter_periodic (k : ℤ) :
    Function.Periodic (signedCircleCharacter k) (2 * Real.pi) := by
  intro theta
  have hp : Complex.exp (((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have he : ((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I k
  unfold signedCircleCharacter
  rw [Complex.ofReal_add, mul_add, Complex.exp_add, hp, mul_one]

theorem projectionHeatTerm_eq_signedCharacter (a theta : ℝ) (n : ℕ) :
    projectionHeatTerm a theta n =
      ((ArithmeticFunction.vonMangoldt n : ℂ) * (projectionHeatRatio a : ℂ) ^ n) *
        signedCircleCharacter (n : ℤ) theta := by
  unfold projectionHeatTerm signedCircleCharacter
  congr 1
  congr 1
  push_cast
  ring

theorem lambdaCircleTrace_periodic (a : ℝ) :
    Function.Periodic (lambdaCircleTrace a) (2 * Real.pi) := by
  intro theta
  simp only [lambdaCircleTrace_eq_heatTrace, projectionHeatTrace]
  apply tsum_congr
  intro n
  simp only [projectionHeatTerm_eq_signedCharacter]
  rw [signedCircleCharacter_periodic (n : ℤ) theta]

theorem projectionCharacter_eq_signedCharacter (N : ℕ) (theta : ℝ) :
    projectionCharacter N theta = signedCircleCharacter (-(N : ℤ)) theta := by
  unfold projectionCharacter signedCircleCharacter
  congr 1
  push_cast
  ring

theorem projectionCharacter_periodic (N : ℕ) :
    Function.Periodic (projectionCharacter N) (2 * Real.pi) := by
  intro theta
  simp only [projectionCharacter_eq_signedCharacter]
  exact signedCircleCharacter_periodic (-(N : ℤ)) theta

theorem star_heatTrace_neg (a theta : ℝ) :
    star (projectionHeatTrace a (-theta)) = projectionHeatTrace a theta := by
  unfold projectionHeatTrace
  rw [tsum_star]
  exact tsum_congr (star_projectionHeatTerm_neg a theta)

theorem lambdaCircleTrace_sq_eq_correlation (a theta : ℝ) :
    lambdaCircleTrace a theta ^ 2 = projectionCorrelation a theta := by
  rw [lambdaCircleTrace_eq_heatTrace]
  unfold projectionCorrelation
  rw [star_heatTrace_neg, pow_two]

theorem lambdaCircleIntegrand_periodic (a : ℝ) (N : ℕ) :
    Function.Periodic
      (fun theta : ℝ => lambdaCircleTrace a theta ^ 2 * projectionCharacter N theta)
      (2 * Real.pi) := by
  intro theta
  rw [lambdaCircleTrace_periodic a theta, projectionCharacter_periodic N theta]

/-- The complete trace moves between the two circle representatives exactly. -/
theorem lambdaCircleCenteredCoefficient_eq_projection (a : ℝ) (N : ℕ) :
    lambdaCircleCenteredCoefficient a N = thermalContinuousProjection a N := by
  have hp := (lambdaCircleIntegrand_periodic a N).intervalIntegral_add_eq (-Real.pi) 0
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [he, zero_add] at hp
  unfold lambdaCircleCenteredCoefficient thermalContinuousProjection
  rw [hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta htheta
  rw [lambdaCircleTrace_sq_eq_correlation]

theorem lambdaCircleCenteredCoefficient_eq_additiveCoefficient {a : ℝ} (ha : 0 < a)
    (N : ℕ) :
    lambdaCircleCenteredCoefficient a N = (projectionAdditiveCoefficient N : ℂ) := by
  rw [lambdaCircleCenteredCoefficient_eq_projection,
    thermalContinuousProjection_eq_coefficient ha]

theorem lambdaCircleTrace_norm_le {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    ‖lambdaCircleTrace a theta‖ ≤ projectionAmplitude a := by
  rw [lambdaCircleTrace_eq_heatTrace]
  exact norm_projectionHeatTrace_le ha theta

theorem lambdaCircleTrace_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (lambdaCircleTrace a) := by
  have he : lambdaCircleTrace a = projectionHeatTrace a :=
    funext (lambdaCircleTrace_eq_heatTrace a)
  rw [he]
  exact projectionHeatTrace_continuous ha

theorem lambdaCircleEpsilon_pos {a : ℝ} (ha : 0 < a) (H : ℝ) :
    0 < lambdaCircleEpsilon a H := by
  unfold lambdaCircleEpsilon
  exact div_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (mul_pos (mul_pos Real.pi_pos (sq_pos_of_pos ha)) (circleDecayFloor_pos ha))

/-- The comparison of both decay parameters pays the uniform phase radius. -/
theorem lambdaMellinTailRadius_circle_le {a theta H : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (htheta : |theta| ≤ Real.pi) :
    lambdaMellinTailRadius (circleMellinPoint a theta) H ≤ lambdaCircleEpsilon a H := by
  let w := circleMellinPoint a theta
  let d := circleDecayFloor a
  have hd : 0 < d := circleDecayFloor_pos ha
  have hdD : d ≤ decayGap w := decayGap_circle_ge_floor ha htheta
  have hD : 0 < decayGap w := lt_of_lt_of_le hd hdD
  have hC := kernelCoefficient_circle_le_four ha theta
  have hexp : Real.exp (-decayGap w * H) ≤ Real.exp (-d * H) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hdD hH
    linarith
  have hnum : 6 * kernelCoefficient w * Real.exp (-decayGap w * H) ≤
      6 * (4 / a ^ 2) * Real.exp (-d * H) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hC (by norm_num)
    · exact hexp
    · exact (Real.exp_pos _).le
    · positivity
  have hden : Real.pi * d ≤ Real.pi * decayGap w :=
    mul_le_mul_of_nonneg_left hdD Real.pi_pos.le
  rw [lambdaMellinTailRadius_eq_closed]
  change 6 * kernelCoefficient w * Real.exp (-decayGap w * H) /
      (Real.pi * decayGap w) ≤ lambdaCircleEpsilon a H
  calc
    _ ≤ (6 * (4 / a ^ 2) * Real.exp (-d * H)) / (Real.pi * d) :=
      div_le_div₀ (by positivity) hnum (mul_pos Real.pi_pos hd) hden
    _ = lambdaCircleEpsilon a H := by
      unfold lambdaCircleEpsilon
      dsimp only [d]
      field_simp [ha.ne', (circleDecayFloor_pos ha).ne', Real.pi_ne_zero]
      <;> ring

theorem lambdaCircleTrace_sub_truncated_norm_le {a H theta : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (htheta : |theta| ≤ Real.pi) :
    ‖lambdaCircleTrace a theta - lambdaCircleTruncatedTrace a H theta‖ ≤
      lambdaCircleEpsilon a H := by
  have hw : 0 < (circleMellinPoint a theta).re := by
    simpa only [circleMellinPoint_re] using ha
  exact (lambdaMellinThermal_truncation_error_le hw hH).trans
    (lambdaMellinTailRadius_circle_le ha hH htheta)

/-- Local domination supplies actual fixed-cutoff parameter continuity. -/
theorem lambdaMellinTruncated_continuousAt {w : ℂ} (hw : 0 < w.re) (H : ℝ) :
    ContinuousAt (fun z : ℂ => lambdaMellinTruncated z H) w := by
  obtain ⟨epsilon, hepsilon, hb⟩ := lambdaMellinProduct_local_uniform_bound hw
  let F : ℂ → ℝ → ℂ := fun z t => lambdaMellinDirichlet t * complexGammaKernel z t
  let B : ℝ → ℝ := fun t =>
    6 * ((‖w‖ / 2) ^ (-2 : ℝ) * (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
      Real.exp (-localDecayGap w * |t|)
  have hm : ∀ᶠ z in 𝓝 w, AEStronglyMeasurable (F z) (volume.restrict (Icc (-H) H)) := by
    filter_upwards [Metric.ball_mem_nhds w hepsilon] with z hz
    exact ((lambdaMellinProduct_integrable (hb z hz).1).integrableOn).aestronglyMeasurable
  have hbound : ∀ᶠ z in 𝓝 w, ∀ᵐ t ∂volume.restrict (Icc (-H) H), ‖F z t‖ ≤ B t := by
    filter_upwards [Metric.ball_mem_nhds w hepsilon] with z hz
    exact Filter.Eventually.of_forall ((hb z hz).2)
  have hBi : Integrable B (volume.restrict (Icc (-H) H)) :=
    (lambdaMellinProduct_local_envelope_integrable hw).integrableOn
  have hcont : ∀ᵐ t ∂volume.restrict (Icc (-H) H),
      ContinuousAt (fun z : ℂ => F z t) w := by
    apply Filter.Eventually.of_forall
    intro t
    have hpow : ContinuousAt (fun z : ℂ => z ^ (-verticalS t)) w :=
      Complex.continuousAt_cpow_const (rightHalfPlane_mem_slitPlane hw)
    change ContinuousAt (fun z : ℂ => lambdaMellinDirichlet t *
      (Complex.Gamma (verticalS t) * z ^ (-verticalS t))) w
    exact (continuousAt_const.mul (continuousAt_const.mul hpow))
  have hi : ContinuousAt (fun z : ℂ => ∫ t : ℝ in Icc (-H) H, F z t) w :=
    continuousAt_of_dominated hm hbound hBi hcont
  unfold lambdaMellinTruncated
  exact continuousAt_const.mul hi

theorem lambdaCircleTruncatedTrace_continuous {a : ℝ} (ha : 0 < a) (H : ℝ) :
    Continuous (lambdaCircleTruncatedTrace a H) := by
  apply continuous_iff_continuousAt.mpr
  intro theta
  have hw : 0 < (circleMellinPoint a theta).re := by
    simpa only [circleMellinPoint_re] using ha
  have hp : Continuous (fun x : ℝ => circleMellinPoint a x) := by
    unfold circleMellinPoint
    fun_prop
  have hc := ContinuousAt.comp
    (f := fun x : ℝ => circleMellinPoint a x)
    (g := fun z : ℂ => lambdaMellinTruncated z H) (x := theta)
    (lambdaMellinTruncated_continuousAt hw H) hp.continuousAt
  simpa only [Function.comp_apply, lambdaCircleTruncatedTrace] using hc

theorem lambdaCircleTruncatedTrace_norm_le {a H theta : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (htheta : |theta| ≤ Real.pi) :
    ‖lambdaCircleTruncatedTrace a H theta‖ ≤ projectionAmplitude a + lambdaCircleEpsilon a H := by
  have he : lambdaCircleTruncatedTrace a H theta = lambdaCircleTrace a theta -
      (lambdaCircleTrace a theta - lambdaCircleTruncatedTrace a H theta) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (add_le_add (lambdaCircleTrace_norm_le ha theta)
      (lambdaCircleTrace_sub_truncated_norm_le ha hH htheta))

theorem lambdaCircleSquaredTrace_error_le {a H theta : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (htheta : |theta| ≤ Real.pi) :
    ‖lambdaCircleTrace a theta ^ 2 - lambdaCircleTruncatedTrace a H theta ^ 2‖ ≤
      2 * projectionAmplitude a * lambdaCircleEpsilon a H + lambdaCircleEpsilon a H ^ 2 := by
  have he : lambdaCircleTrace a theta ^ 2 - lambdaCircleTruncatedTrace a H theta ^ 2 =
      (lambdaCircleTrace a theta - lambdaCircleTruncatedTrace a H theta) *
        (lambdaCircleTrace a theta + lambdaCircleTruncatedTrace a H theta) := by ring
  rw [he, norm_mul]
  have hadd : ‖lambdaCircleTrace a theta + lambdaCircleTruncatedTrace a H theta‖ ≤
      projectionAmplitude a + (projectionAmplitude a + lambdaCircleEpsilon a H) :=
    (norm_add_le _ _).trans (add_le_add (lambdaCircleTrace_norm_le ha theta)
      (lambdaCircleTruncatedTrace_norm_le ha hH htheta))
  calc
    _ ≤ lambdaCircleEpsilon a H *
        (projectionAmplitude a + (projectionAmplitude a + lambdaCircleEpsilon a H)) :=
      mul_le_mul (lambdaCircleTrace_sub_truncated_norm_le ha hH htheta) hadd
        (norm_nonneg _) (lambdaCircleEpsilon_pos ha H).le
    _ = _ := by ring

theorem lambdaCircleIntegrand_intervalIntegrable {a : ℝ} (ha : 0 < a) (N : ℕ) :
    IntervalIntegrable
      (fun theta : ℝ => lambdaCircleTrace a theta ^ 2 * projectionCharacter N theta)
      volume (-Real.pi) Real.pi := by
  have hc : Continuous (projectionCharacter N) := by
    unfold projectionCharacter
    fun_prop
  exact (((lambdaCircleTrace_continuous ha).pow 2).mul hc).intervalIntegrable _ _

theorem lambdaCircleTruncatedIntegrand_intervalIntegrable {a : ℝ} (ha : 0 < a)
    (H : ℝ) (N : ℕ) :
    IntervalIntegrable
      (fun theta : ℝ => lambdaCircleTruncatedTrace a H theta ^ 2 * projectionCharacter N theta)
      volume (-Real.pi) Real.pi := by
  have hc : Continuous (projectionCharacter N) := by
    unfold projectionCharacter
    fun_prop
  exact (((lambdaCircleTruncatedTrace_continuous ha H).pow 2).mul hc).intervalIntegrable _ _

/-- The output error follows from genuine squared traces and both integrable projections. -/
theorem lambdaCircleCenteredCoefficient_error_le {a H : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (N : ℕ) :
    ‖lambdaCircleCenteredCoefficient a N - lambdaCircleTruncatedCoefficient a H N‖ ≤
      lambdaCircleCoefficientError a H N := by
  let E := 2 * projectionAmplitude a * lambdaCircleEpsilon a H + lambdaCircleEpsilon a H ^ 2
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi) (C := E)
    (f := fun theta : ℝ =>
      (lambdaCircleTrace a theta ^ 2 - lambdaCircleTruncatedTrace a H theta ^ 2) *
        projectionCharacter N theta) (by
      intro theta htheta
      rw [uIoc_of_le hpi] at htheta
      have ht : |theta| ≤ Real.pi := abs_le.mpr ⟨htheta.1.le, htheta.2⟩
      rw [norm_mul, norm_projectionCharacter, mul_one]
      exact lambdaCircleSquaredTrace_error_le ha hH ht)
  have hi := lambdaCircleIntegrand_intervalIntegrable ha N
  have hf := lambdaCircleTruncatedIntegrand_intervalIntegrable ha H N
  have hc : 0 < Real.exp (a * (N : ℝ)) / (2 * Real.pi) :=
    div_pos (Real.exp_pos _) (mul_pos (by norm_num) Real.pi_pos)
  unfold lambdaCircleCenteredCoefficient lambdaCircleTruncatedCoefficient
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hf]
  simp_rw [← sub_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ (Real.exp (a * (N : ℝ)) / (2 * Real.pi)) * (E * |Real.pi - -Real.pi|) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = lambdaCircleCoefficientError a H N := by
      rw [abs_of_pos (by linarith [Real.pi_pos] : 0 < Real.pi - -Real.pi)]
      unfold lambdaCircleCoefficientError
      dsimp only [E]
      field_simp [Real.pi_ne_zero]
      <;> ring

theorem lambdaCircleAdditiveCoefficient_error_le {a H : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (N : ℕ) :
    ‖(projectionAdditiveCoefficient N : ℂ) - lambdaCircleTruncatedCoefficient a H N‖ ≤
      lambdaCircleCoefficientError a H N := by
  rw [← lambdaCircleCenteredCoefficient_eq_additiveCoefficient ha N]
  exact lambdaCircleCenteredCoefficient_error_le ha hH N

theorem lambdaCircleEpsilon_continuousAt {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => lambdaCircleEpsilon q.1 q.2) p := by
  have hd : 0 < circleDecayFloor p.1 := circleDecayFloor_pos hp
  have hc : ContinuousAt (fun q : ℝ × ℝ => circleDecayFloor q.1) p :=
    (circleDecayFloor_continuous.comp continuous_fst).continuousAt
  unfold lambdaCircleEpsilon
  fun_prop (disch := positivity)

theorem lambdaCircleCoefficientError_nonneg {a : ℝ} (ha : 0 < a) (H : ℝ) (N : ℕ) :
    0 ≤ lambdaCircleCoefficientError a H N := by
  unfold lambdaCircleCoefficientError
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (projectionAmplitude_nonneg ha))
      (lambdaCircleEpsilon_pos ha H).le) (sq_nonneg _))

theorem lambdaCircleCoefficientError_continuousAt {p : ℝ × ℝ} (hp : 0 < p.1) (N : ℕ) :
    ContinuousAt (fun q : ℝ × ℝ => lambdaCircleCoefficientError q.1 q.2 N) p := by
  have he := lambdaCircleEpsilon_continuousAt hp
  have hd : projectionHeatRatio p.1 < 1 := projectionHeatRatio_lt_one hp
  have hd' : 0 < 1 - Real.exp (-p.1) := by
    simpa only [projectionHeatRatio] using sub_pos.mpr hd
  have ha : ContinuousAt (fun q : ℝ × ℝ => projectionAmplitude q.1) p := by
    unfold projectionAmplitude projectionHeatRatio
    fun_prop (disch := positivity)
  unfold lambdaCircleCoefficientError
  fun_prop

end GoldbachLambdaCircle22

#print axioms GoldbachLambdaCircle22.lambdaCircleTrace
#print axioms GoldbachLambdaCircle22.lambdaCircleTruncatedTrace
#print axioms GoldbachLambdaCircle22.lambdaCircleCenteredCoefficient
#print axioms GoldbachLambdaCircle22.lambdaCircleTruncatedCoefficient
#print axioms GoldbachLambdaCircle22.lambdaCircleEpsilon
#print axioms GoldbachLambdaCircle22.lambdaCircleCoefficientError
#print axioms GoldbachLambdaCircle22.lambdaCircleTerm_eq_heatTerm
#print axioms GoldbachLambdaCircle22.lambdaCircleTrace_eq_heatTrace
#print axioms GoldbachLambdaCircle22.signedCircleCharacter_periodic
#print axioms GoldbachLambdaCircle22.projectionHeatTerm_eq_signedCharacter
#print axioms GoldbachLambdaCircle22.lambdaCircleTrace_periodic
#print axioms GoldbachLambdaCircle22.projectionCharacter_eq_signedCharacter
#print axioms GoldbachLambdaCircle22.projectionCharacter_periodic
#print axioms GoldbachLambdaCircle22.star_heatTrace_neg
#print axioms GoldbachLambdaCircle22.lambdaCircleTrace_sq_eq_correlation
#print axioms GoldbachLambdaCircle22.lambdaCircleIntegrand_periodic
#print axioms GoldbachLambdaCircle22.lambdaCircleCenteredCoefficient_eq_projection
#print axioms GoldbachLambdaCircle22.lambdaCircleCenteredCoefficient_eq_additiveCoefficient
#print axioms GoldbachLambdaCircle22.lambdaCircleTrace_norm_le
#print axioms GoldbachLambdaCircle22.lambdaCircleTrace_continuous
#print axioms GoldbachLambdaCircle22.lambdaCircleEpsilon_pos
#print axioms GoldbachLambdaCircle22.lambdaMellinTailRadius_circle_le
#print axioms GoldbachLambdaCircle22.lambdaCircleTrace_sub_truncated_norm_le
#print axioms GoldbachLambdaCircle22.lambdaMellinTruncated_continuousAt
#print axioms GoldbachLambdaCircle22.lambdaCircleTruncatedTrace_continuous
#print axioms GoldbachLambdaCircle22.lambdaCircleTruncatedTrace_norm_le
#print axioms GoldbachLambdaCircle22.lambdaCircleSquaredTrace_error_le
#print axioms GoldbachLambdaCircle22.lambdaCircleIntegrand_intervalIntegrable
#print axioms GoldbachLambdaCircle22.lambdaCircleTruncatedIntegrand_intervalIntegrable
#print axioms GoldbachLambdaCircle22.lambdaCircleCenteredCoefficient_error_le
#print axioms GoldbachLambdaCircle22.lambdaCircleAdditiveCoefficient_error_le
#print axioms GoldbachLambdaCircle22.lambdaCircleEpsilon_continuousAt
#print axioms GoldbachLambdaCircle22.lambdaCircleCoefficientError_nonneg
#print axioms GoldbachLambdaCircle22.lambdaCircleCoefficientError_continuousAt
