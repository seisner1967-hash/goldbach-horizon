import ThermalProjectionEnvelope22
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Star.BigOperators

/-! SOURCE ONLY. This module uses the actual von Mangoldt trace and retains
all prime powers. Its only analytic premise is a>0. Circle orthogonality and
finite character sums are proved first. The infinite integral is recovered
from the concrete uniform geometric envelope, rather than from a supplied
Fourier identity. Revision03 retains the four repairs of revision02 and
normalizes the period casts after the actual batch12 log. Its imported
Envelope02 is independently PASS and remains readonly; this identity revision
is SOURCE and has not been compiled.
This identity does not supply a uniform zeta evaluator, prime-power removal,
frontier positivity, a D_N estimate or a Goldbach conclusion. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace GoldbachContinuous22

/-- The genuine character of the circle with signed integer frequency. -/
def signedCircleCharacter (k : ℤ) (theta : ℝ) : ℂ :=
  Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))

/-- The additive coefficient retains every von Mangoldt prime-power weight. -/
def projectionAdditiveCoefficient (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal N,
    ArithmeticFunction.vonMangoldt p.1 * ArithmeticFunction.vonMangoldt p.2

theorem signedCircleCharacter_continuous (k : ℤ) : Continuous (signedCircleCharacter k) := by
  unfold signedCircleCharacter
  fun_prop

/-- Exact orthogonality with interval length 2*pi, including frequency zero. -/
theorem integral_signedCircleCharacter (k : ℤ) :
    (∫ theta : ℝ in (0)..(2 * Real.pi), signedCircleCharacter k theta) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [signedCircleCharacter, intervalIntegral.integral_const]
  · have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero hkC Complex.I_ne_zero
    have hperiod : Complex.exp (((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have he : ((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [he]
      exact Complex.exp_int_mul_two_pi_mul_I k
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hperiod
    unfold signedCircleCharacter
    rw [_root_.integral_exp_mul_complex hc]
    simp [hperiod, hk]

/-- Conjugating the negative phase restores the positive character. -/
theorem star_projectionHeatTerm_neg (a theta : ℝ) (n : ℕ) :
    star (projectionHeatTerm a (-theta) n) = projectionHeatTerm a theta n := by
  have he : conj (Complex.exp ((((n : ℝ) * (-theta) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul,
      Complex.ofReal_neg]
    ring
  simp only [projectionHeatTerm, Complex.star_def, map_mul, map_pow,
    Complex.conj_ofReal, he]

/-- Multiplication of continuous characters adds their frequencies. -/
theorem projection_pair_character (a theta : ℝ) (N m n : ℕ) :
    projectionHeatTerm a theta m * star (projectionHeatTerm a (-theta) n) *
        projectionCharacter N theta =
      ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (projectionHeatRatio a : ℂ) ^ (m + n) *
        signedCircleCharacter ((m : ℤ) + (n : ℤ) - (N : ℤ)) theta := by
  rw [star_projectionHeatTerm_neg]
  have he :
      Complex.exp ((((m : ℝ) * theta : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-(N : ℝ) * theta : ℝ) : ℂ) * Complex.I) =
      signedCircleCharacter ((m : ℤ) + (n : ℤ) - (N : ℤ)) theta := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    unfold signedCircleCharacter
    congr 1
    push_cast
    ring
  calc
    _ = ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (projectionHeatRatio a : ℂ) ^ (m + n) *
        (Complex.exp ((((m : ℝ) * theta : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(N : ℝ) * theta : ℝ) : ℂ) * Complex.I)) := by
      unfold projectionHeatTerm projectionCharacter
      rw [pow_add]
      push_cast
      ring
    _ = _ := by rw [he]

theorem projection_pair_integral (a : ℝ) (N m n : ℕ) :
    (∫ theta : ℝ in (0)..(2 * Real.pi),
      projectionHeatTerm a theta m * star (projectionHeatTerm a (-theta) n) *
        projectionCharacter N theta) =
      if m + n = N then
        ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (projectionHeatRatio a : ℂ) ^ N * ((2 * Real.pi : ℝ) : ℂ)
      else 0 := by
  simp_rw [projection_pair_character]
  rw [intervalIntegral.integral_const_mul, integral_signedCircleCharacter]
  by_cases hmn : m + n = N
  · have hk : (m : ℤ) + (n : ℤ) - (N : ℤ) = 0 := by omega
    simp [hmn, hk]
  · have hk : (m : ℤ) + (n : ℤ) - (N : ℤ) ≠ 0 := by omega
    simp [hmn, hk]

/-- The normalizer cancels the heat factor exactly for every real a. -/
theorem projection_normalizer_cancel (a : ℝ) (N : ℕ) :
    ((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
      (projectionHeatRatio a : ℂ) ^ N * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
  have hpow : projectionHeatRatio a ^ N = Real.exp (-(a * (N : ℝ))) := by
    unfold projectionHeatRatio
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hreal : (Real.exp (a * (N : ℝ)) / (2 * Real.pi)) *
      projectionHeatRatio a ^ N * (2 * Real.pi) = 1 := by
    rw [hpow, Real.exp_neg]
    field_simp [Real.pi_ne_zero, Real.exp_ne_zero] <;> ring
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one] using
    congrArg Complex.ofReal hreal

theorem normalized_projection_pair_integral (a : ℝ) (N m n : ℕ) :
    ((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ theta : ℝ in (0)..(2 * Real.pi),
        projectionHeatTerm a theta m * star (projectionHeatTerm a (-theta) n) *
          projectionCharacter N theta) =
      if m + n = N then
        ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
      else 0 := by
  rw [projection_pair_integral]
  by_cases hmn : m + n = N
  · rw [if_pos hmn, if_pos hmn]
    calc
      _ = ((ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
            (projectionHeatRatio a : ℂ) ^ N * ((2 * Real.pi : ℝ) : ℂ)) := by ring
      _ = _ := by rw [projection_normalizer_cancel, mul_one]
  · simp [hmn]

/-- Expansion on a finite rectangle of actual circle characters. -/
theorem projectionPartialCorrelation_expansion (a theta : ℝ) (N M : ℕ) :
    projectionPartialCorrelation a theta M * projectionCharacter N theta =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        projectionHeatTerm a theta p.1 * star (projectionHeatTerm a (-theta) p.2) *
          projectionCharacter N theta := by
  simp only [projectionPartialCorrelation, projectionHeatPartial, star_sum,
    Finset.sum_product, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A sufficiently large finite rectangle contains the whole additive antidiagonal. -/
theorem projection_rectangle_filter_eq_antidiagonal (N M : ℕ) (hNM : N ≤ M) :
    (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = N) = Finset.antidiagonal N := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · exact fun hp => hp.2
  · intro hp
    have hp1 : p.1 ≤ N := by omega
    have hp2 : p.2 ≤ N := by omega
    exact ⟨⟨by omega, by omega⟩, hp⟩

/-- All finite interchanges have continuous, hence interval-integrable, summands. -/
theorem thermalPartialProjection_eq_finite_coefficient (a : ℝ) (N M : ℕ) :
    thermalPartialProjection a N M =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        if p.1 + p.2 = N then
          ((ArithmeticFunction.vonMangoldt p.1 * ArithmeticFunction.vonMangoldt p.2 : ℝ) : ℂ)
        else 0 := by
  have hi (p : ℕ × ℕ) : IntervalIntegrable (fun theta : ℝ =>
      projectionHeatTerm a theta p.1 * star (projectionHeatTerm a (-theta) p.2) *
        projectionCharacter N theta) volume (0 : ℝ) (2 * Real.pi) := by
    have hc : Continuous (fun theta : ℝ =>
        projectionHeatTerm a theta p.1 * star (projectionHeatTerm a (-theta) p.2) *
          projectionCharacter N theta) := by
      unfold projectionHeatTerm projectionCharacter
      fun_prop
    exact hc.intervalIntegrable _ _
  unfold thermalPartialProjection
  simp_rw [projectionPartialCorrelation_expansion]
  rw [intervalIntegral.integral_finset_sum (fun p hp => hi p), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact normalized_projection_pair_integral a N p.1 p.2

/-- The exact finite projection is already stable once M>=N. -/
theorem thermalPartialProjection_eq_coefficient (a : ℝ) (N M : ℕ) (hNM : N ≤ M) :
    thermalPartialProjection a N M = (projectionAdditiveCoefficient N : ℂ) := by
  rw [thermalPartialProjection_eq_finite_coefficient, ← Finset.sum_filter,
    projection_rectangle_filter_eq_antidiagonal N M hNM]
  unfold projectionAdditiveCoefficient
  push_cast <;> rfl

/-- Conventional single-index form, with no removal of prime powers. -/
theorem projectionAdditiveCoefficient_eq_sum (N : ℕ) :
    projectionAdditiveCoefficient N =
      ∑ m ∈ Finset.range (N + 1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N - m) := by
  unfold projectionAdditiveCoefficient
  rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map] <;> rfl

/-- The already derived geometric tail tends to zero; no epsilon oracle is assumed. -/
theorem projectionTailEnvelope_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun M : ℕ => projectionTailEnvelope a M) atTop (𝓝 0) := by
  have hr := (projectionHeatRatio_pos a).le
  have hr1 := projectionHeatRatio_lt_one ha
  have h1 : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) * projectionHeatRatio a ^ (M + 1))
      atTop (𝓝 0) :=
    (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M : ℕ => projectionHeatRatio a ^ (M + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_projectionHeatRatio_lt_one ha)).comp
      (tendsto_add_atTop_nat 1)
  have h := (h1.div_const (1 - projectionHeatRatio a)).add
    (h2.mul_const (projectionAmplitude a))
  have heq : (fun M : ℕ => projectionTailEnvelope a M) =
      (fun M : ℕ => (((M + 1 : ℕ) : ℝ) * projectionHeatRatio a ^ (M + 1)) /
        (1 - projectionHeatRatio a) +
        projectionHeatRatio a ^ (M + 1) * projectionAmplitude a) := by
    funext M
    unfold projectionTailEnvelope
    ring
  simpa only [← heq, zero_div, zero_mul, zero_add] using h

/-- Genuine uniform convergence in theta of the actual finite heat traces. -/
theorem projectionHeatPartial_converges_uniformly {a : ℝ} (ha : 0 < a) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ theta : ℝ,
      ‖projectionHeatTrace a theta - projectionHeatPartial a theta M‖ < epsilon := by
  intro epsilon he
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp
    ((projectionTailEnvelope_tendsto_zero ha).eventually (gt_mem_nhds he))
  exact ⟨M0, fun M hM theta =>
    (norm_projectionHeatTrace_sub_partial_le ha theta M).trans_lt (hM0 M hM)⟩

theorem projectionErrorEnvelope_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Tendsto (fun M : ℕ => projectionErrorEnvelope a N M) atTop (𝓝 0) := by
  have h := (projectionTailEnvelope_tendsto_zero ha).const_mul
    (2 * Real.exp (a * (N : ℝ)) * projectionAmplitude a)
  simpa only [projectionErrorEnvelope, mul_zero] using h

/-- The infinite correlation integral is the limit of the finite integrals.
The bound paying this interchange was constructed from the actual true trace. -/
theorem thermalProjection_difference_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Tendsto (fun M : ℕ => thermalContinuousProjection a N - thermalPartialProjection a N M)
      atTop (𝓝 0) :=
  squeeze_zero_norm (fun M => thermalContinuousProjection_error_le ha N M)
    (projectionErrorEnvelope_tendsto_zero ha N)

/-- Exact coefficient extraction for the actual infinite continuous correlation. -/
theorem thermalContinuousProjection_eq_coefficient {a : ℝ} (ha : 0 < a) (N : ℕ) :
    thermalContinuousProjection a N = (projectionAdditiveCoefficient N : ℂ) := by
  have h := thermalProjection_difference_tendsto_zero ha N
  have he : (fun M : ℕ => thermalContinuousProjection a N - thermalPartialProjection a N M)
      =ᶠ[atTop] (fun _ : ℕ => thermalContinuousProjection a N - (projectionAdditiveCoefficient N : ℂ)) := by
    exact eventually_atTop.mpr ⟨N, fun M hM => by
      change thermalContinuousProjection a N - thermalPartialProjection a N M =
        thermalContinuousProjection a N - (projectionAdditiveCoefficient N : ℂ)
      rw [thermalPartialProjection_eq_coefficient a N M hM]⟩
  have hc := h.congr' he
  exact sub_eq_zero.mp (tendsto_const_nhds_iff.mp hc)

/-- Circle correlation identity with the conventional true Lambda coefficient. -/
theorem thermalContinuousProjection_eq_vonMangoldt_sum {a : ℝ} (ha : 0 < a) (N : ℕ) :
    thermalContinuousProjection a N =
      ((∑ m ∈ Finset.range (N + 1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N - m) : ℝ) : ℂ) := by
  rw [thermalContinuousProjection_eq_coefficient ha, projectionAdditiveCoefficient_eq_sum]

end GoldbachContinuous22

#print axioms GoldbachContinuous22.signedCircleCharacter
#print axioms GoldbachContinuous22.projectionAdditiveCoefficient
#print axioms GoldbachContinuous22.signedCircleCharacter_continuous
#print axioms GoldbachContinuous22.integral_signedCircleCharacter
#print axioms GoldbachContinuous22.star_projectionHeatTerm_neg
#print axioms GoldbachContinuous22.projection_pair_character
#print axioms GoldbachContinuous22.projection_pair_integral
#print axioms GoldbachContinuous22.projection_normalizer_cancel
#print axioms GoldbachContinuous22.normalized_projection_pair_integral
#print axioms GoldbachContinuous22.projectionPartialCorrelation_expansion
#print axioms GoldbachContinuous22.projection_rectangle_filter_eq_antidiagonal
#print axioms GoldbachContinuous22.thermalPartialProjection_eq_finite_coefficient
#print axioms GoldbachContinuous22.thermalPartialProjection_eq_coefficient
#print axioms GoldbachContinuous22.projectionAdditiveCoefficient_eq_sum
#print axioms GoldbachContinuous22.projectionTailEnvelope_tendsto_zero
#print axioms GoldbachContinuous22.projectionHeatPartial_converges_uniformly
#print axioms GoldbachContinuous22.projectionErrorEnvelope_tendsto_zero
#print axioms GoldbachContinuous22.thermalProjection_difference_tendsto_zero
#print axioms GoldbachContinuous22.thermalContinuousProjection_eq_coefficient
#print axioms GoldbachContinuous22.thermalContinuousProjection_eq_vonMangoldt_sum



