import Mathlib.Tactic
import TS.Goldbach.Strong.TS315.DiscreteSpectralCorrelationIdentity

namespace TS316
namespace Goldbach

noncomputable section

/-!
# Quantitative diagonal zero-correlation bound

This module closes the diagonal contract left by TS315.  Its coefficient
magnitude is the norm of the exact TS292 spectral term at scale one, so all
zero multiplicities and Mellin denominators remain unchanged.

Absolute summability from TS292 implies square summability by restricting the
product of two nonnegative summable families to the diagonal.  No separate
multiplicity bound, zero simplicity assumption, TS290 recounting, or RH input
is needed.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

/-- Magnitude of the exact multiplicity-denominator coefficient. -/
noncomputable def zeroCoefficientMagnitude
    (rho : ConcreteNontrivialZero) : Real :=
  norm (TS292.Goldbach.infiniteZeroSpectralTerm 1 rho)

/-- Scale one removes the complex-power factor exactly. -/
theorem zeroCoefficientMagnitude_eq_factor_abs
    (rho : ConcreteNontrivialZero) :
    zeroCoefficientMagnitude rho =
      Complex.abs
        (TS268.Goldbach.concreteMultiplicityDenominatorFactor rho.1) := by
  unfold zeroCoefficientMagnitude TS292.Goldbach.infiniteZeroSpectralTerm
  change
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm 1 rho.1) = _
  rw [TS268.Goldbach.concreteFiniteHeightZeroTerm_abs_eq_scale_mul_factor]
  simp

theorem zeroCoefficientMagnitude_nonnegative
    (rho : ConcreteNontrivialZero) :
    0 <= zeroCoefficientMagnitude rho :=
  norm_nonneg _

/-- TS292 absolute convergence is exactly linear coefficient summability. -/
theorem zeroCoefficientMagnitude_summable :
    Summable zeroCoefficientMagnitude := by
  simpa only [zeroCoefficientMagnitude] using
    TS292.Goldbach.infiniteZeroSpectralTerm_norm_summable 1

/-- A nonnegative summable real family is square summable. -/
theorem summable_sq_of_summable_nonnegative
    {alpha : Type*}
    (a : alpha -> Real)
    (ha : Summable a)
    (ha0 : forall i, 0 <= a i) :
    Summable (fun i => a i ^ 2) := by
  have hProd : Summable
      (fun p : Prod alpha alpha => a p.1 * a p.2) :=
    ha.mul_of_nonneg ha ha0 ha0
  have hDiag : Summable
      (Function.comp
        (fun p : Prod alpha alpha => a p.1 * a p.2)
        (fun i : alpha => (i, i))) :=
    hProd.comp_injective
      (fun i j hij => by simpa using congrArg Prod.fst hij)
  simpa only [Function.comp_apply, pow_two] using hDiag

theorem zeroCoefficientMagnitude_sq_summable :
    Summable (fun rho : ConcreteNontrivialZero =>
      zeroCoefficientMagnitude rho ^ 2) :=
  summable_sq_of_summable_nonnegative
    zeroCoefficientMagnitude
    zeroCoefficientMagnitude_summable
    zeroCoefficientMagnitude_nonnegative

/-- Global finite quadratic mass of the exact TS292 coefficients. -/
noncomputable def globalQuadraticSpectralMass : Real :=
  tsum (fun rho : ConcreteNontrivialZero =>
    zeroCoefficientMagnitude rho ^ 2)

/-- Global linear coefficient mass already known finite from TS292. -/
noncomputable def globalLinearSpectralMass : Real :=
  tsum zeroCoefficientMagnitude

theorem globalQuadraticSpectralMass_nonnegative :
    0 <= globalQuadraticSpectralMass := by
  unfold globalQuadraticSpectralMass
  exact tsum_nonneg (fun rho => sq_nonneg (zeroCoefficientMagnitude rho))

theorem globalLinearSpectralMass_nonnegative :
    0 <= globalLinearSpectralMass := by
  unfold globalLinearSpectralMass
  exact tsum_nonneg zeroCoefficientMagnitude_nonnegative

/-- The quadratic mass is bounded by the square of the TS292 linear mass. -/
theorem globalQuadraticSpectralMass_le_linear_sq :
    globalQuadraticSpectralMass <= globalLinearSpectralMass ^ 2 := by
  let a : ConcreteNontrivialZero -> Real := zeroCoefficientMagnitude
  have ha : Summable a := zeroCoefficientMagnitude_summable
  have ha0 : forall rho, 0 <= a rho := zeroCoefficientMagnitude_nonnegative
  let S : Real := tsum a
  have hPointwise : forall rho, a rho ^ 2 <= S * a rho := by
    intro rho
    have hLe : a rho <= S := by
      exact le_tsum ha rho (fun sigma hNe => ha0 sigma)
    nlinarith [ha0 rho]
  have hMajorant : Summable (fun rho => S * a rho) := ha.mul_left S
  unfold globalQuadraticSpectralMass globalLinearSpectralMass
  change tsum (fun rho : ConcreteNontrivialZero => a rho ^ 2) <=
    tsum a ^ 2
  calc
    tsum (fun rho : ConcreteNontrivialZero => a rho ^ 2) <=
        tsum (fun rho : ConcreteNontrivialZero => S * a rho) :=
      tsum_le_tsum hPointwise zeroCoefficientMagnitude_sq_summable hMajorant
    _ = S * tsum a := ha.tsum_mul_left S
    _ = tsum a ^ 2 := by ring

/-! ## Uniform normalized-term bound -/

/-- The unnormalized term at scale `x >= 1` is at most `x` times its coefficient. -/
theorem infiniteZeroSpectralTerm_norm_le_scale_mul_coefficient
    (x : Nat)
    (hx : 1 <= x)
    (rho : ConcreteNontrivialZero) :
    norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho) <=
      (x : Real) * zeroCoefficientMagnitude rho := by
  unfold TS292.Goldbach.infiniteZeroSpectralTerm
  change
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm x rho.1) <= _
  rw [TS268.Goldbach.concreteFiniteHeightZeroTerm_abs_eq_scale_mul_factor]
  rw [zeroCoefficientMagnitude_eq_factor_abs]
  exact mul_le_mul_of_nonneg_right
    (TS268.Goldbach.naturalScaleComplexPower_abs_le
      x rho.1 hx rho.property)
    (Complex.abs.nonneg _)

/-- Canonical normalization cancels the arithmetic scale pointwise. -/
theorem normalizedTruncatedZeroTerm_norm_le_two_mul_coefficient
    (x : Nat)
    (hx : 1 <= x)
    (rho : ConcreteNontrivialZero) :
    norm (TS315.Goldbach.normalizedTruncatedZeroTerm x rho) <=
      2 * zeroCoefficientMagnitude rho := by
  have hx0 : Not ((x : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hx))
  have hScale :=
    infiniteZeroSpectralTerm_norm_le_scale_mul_coefficient x hx rho
  unfold TS315.Goldbach.normalizedTruncatedZeroTerm
  rw [norm_mul]
  have hNormalization :
      norm
          ((TS313.Goldbach.canonicalTraceNormalizationFactor x : Real) :
            Complex) =
        2 / (x : Real) := by
    unfold TS313.Goldbach.canonicalTraceNormalizationFactor
    rw [Complex.norm_real]
    exact abs_of_nonneg (by positivity)
  rw [hNormalization]
  calc
    2 / (x : Real) *
        norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho) <=
      2 / (x : Real) *
        ((x : Real) * zeroCoefficientMagnitude rho) := by
      exact mul_le_mul_of_nonneg_left hScale (by positivity)
    _ = 2 * zeroCoefficientMagnitude rho := by
      field_simp
      ring

/-! ## Diagonal kernel and global bound -/

/-- The diagonal kernel is the finite sum of squared normalized norms. -/
theorem diagonalZeroPairCorrelationKernel_eq_sum_norm_sq
    (X : Nat)
    (rho : ConcreteNontrivialZero) :
    TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho rho =
      Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
        ((norm (TS315.Goldbach.normalizedTruncatedZeroTerm x rho) ^ 2 :
          Real) : Complex)) := by
  unfold TS315.Goldbach.normalizedZeroPairCorrelationKernel
  apply Finset.sum_congr rfl
  intro x hx
  simpa only [Complex.ofReal_pow] using
    Complex.mul_conj'
      (TS315.Goldbach.normalizedTruncatedZeroTerm x rho)

/-- Every diagonal kernel is controlled by its exact scale-one coefficient. -/
theorem diagonalZeroPairCorrelationKernel_norm_le
    (X : Nat)
    (hX : 0 < X)
    (rho : ConcreteNontrivialZero) :
    norm (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho rho) <=
      4 * (X : Real) * zeroCoefficientMagnitude rho ^ 2 := by
  unfold TS315.Goldbach.normalizedZeroPairCorrelationKernel
  calc
    norm
        (Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
          TS315.Goldbach.normalizedTruncatedZeroTerm x rho *
            (starRingEnd Complex)
              (TS315.Goldbach.normalizedTruncatedZeroTerm x rho))) <=
      Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
        norm
          (TS315.Goldbach.normalizedTruncatedZeroTerm x rho *
            (starRingEnd Complex)
              (TS315.Goldbach.normalizedTruncatedZeroTerm x rho))) :=
      norm_sum_le _ _
    _ <= Finset.sum (TS314.Goldbach.dyadicWindow X) (fun _ =>
        4 * zeroCoefficientMagnitude rho ^ 2) := by
      apply Finset.sum_le_sum
      intro x hxWindow
      have hxOne :=
        TS314.Goldbach.one_le_of_mem_dyadicWindow hX hxWindow
      have hTerm :=
        normalizedTruncatedZeroTerm_norm_le_two_mul_coefficient
          x hxOne rho
      have hTermNonnegative :
          0 <= norm (TS315.Goldbach.normalizedTruncatedZeroTerm x rho) :=
        norm_nonneg _
      have hCoefficientNonnegative : 0 <= zeroCoefficientMagnitude rho :=
        zeroCoefficientMagnitude_nonnegative rho
      calc
        norm
            (TS315.Goldbach.normalizedTruncatedZeroTerm x rho *
              (starRingEnd Complex)
                (TS315.Goldbach.normalizedTruncatedZeroTerm x rho)) =
          norm (TS315.Goldbach.normalizedTruncatedZeroTerm x rho) ^ 2 := by
            rw [Complex.mul_conj']
            simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg _)]
        _ <= (2 * zeroCoefficientMagnitude rho) ^ 2 := by
          nlinarith
        _ = 4 * zeroCoefficientMagnitude rho ^ 2 := by ring
    _ = 4 * (X : Real) * zeroCoefficientMagnitude rho ^ 2 := by
      rw [Finset.sum_const, TS314.Goldbach.dyadicWindow_card]
      simp only [nsmul_eq_mul]
      ring

/-- Division by the dyadic cardinal cancels the spatial factor. -/
theorem diagonalZeroPairCorrelationKernel_div_norm_le
    (X : Nat)
    (hX : 0 < X)
    (rho : ConcreteNontrivialZero) :
    norm
        (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho rho /
          (X : Complex)) <=
      4 * zeroCoefficientMagnitude rho ^ 2 := by
  have hXReal : (0 : Real) < (X : Real) := by exact_mod_cast hX
  have hXNe : Not ((X : Real) = 0) := ne_of_gt hXReal
  have hKernel := diagonalZeroPairCorrelationKernel_norm_le X hX rho
  rw [norm_div, Complex.norm_natCast]
  calc
    norm (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho rho) /
        (X : Real) <=
      (4 * (X : Real) * zeroCoefficientMagnitude rho ^ 2) / (X : Real) :=
      div_le_div_of_nonneg_right hKernel hXReal.le
    _ = 4 * zeroCoefficientMagnitude rho ^ 2 := by
      field_simp
      ring

/-- The TS315 diagonal contract is closed uniformly in height and scale. -/
theorem diagonalZeroCorrelationBound
    (X T : Nat)
    (hX : 0 < X) :
    TS315.Goldbach.DiagonalZeroCorrelationBoundStatement
      X T (4 * globalQuadraticSpectralMass) := by
  unfold TS315.Goldbach.DiagonalZeroCorrelationBoundStatement
  calc
    norm (TS315.Goldbach.diagonalNormalizedZeroPairCorrelation X T) <=
        Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
          norm
            (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho rho /
              (X : Complex))) :=
      TS315.Goldbach.diagonalNormalizedZeroPairCorrelation_norm_le X T
    _ <= Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        4 * zeroCoefficientMagnitude rho ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact diagonalZeroPairCorrelationKernel_div_norm_le X hX rho
    _ = 4 * Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        zeroCoefficientMagnitude rho ^ 2) := by
      rw [Finset.mul_sum]
    _ <= 4 * globalQuadraticSpectralMass := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      unfold globalQuadraticSpectralMass
      exact sum_le_tsum (TS315.Goldbach.truncatedZeroSet T)
        (fun rho hRho => sq_nonneg (zeroCoefficientMagnitude rho))
        zeroCoefficientMagnitude_sq_summable

/-- A coarser closed form uses only the TS292 linear coefficient mass. -/
theorem diagonalZeroCorrelationBound_by_linearMass
    (X T : Nat)
    (hX : 0 < X) :
    TS315.Goldbach.DiagonalZeroCorrelationBoundStatement
      X T (4 * globalLinearSpectralMass ^ 2) := by
  unfold TS315.Goldbach.DiagonalZeroCorrelationBoundStatement
  exact (diagonalZeroCorrelationBound X T hX).trans
    (mul_le_mul_of_nonneg_left
      globalQuadraticSpectralMass_le_linear_sq (by norm_num))

/-! ## Audit ledger -/

structure TS316Ledger where
  exact_scale_one_coefficient_identified : True
  linear_coefficient_summability_reused : True
  quadratic_coefficient_summability_proved : True
  quadratic_mass_le_linear_mass_squared : True
  normalized_term_bound_proved : True
  diagonal_kernel_bound_proved : True
  diagonal_contract_closed_uniformly : True
  separate_multiplicity_bound_not_needed : True
  ts290_recounting_not_needed : True
  rational_mass_upper_bound_not_proved : True
  diagonal_half_budget_smallness_not_proved : True
  kusmin_landau_deferred_to_ts317 : True
  rh_not_assumed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts316Ledger : TS316Ledger where
  exact_scale_one_coefficient_identified := True.intro
  linear_coefficient_summability_reused := True.intro
  quadratic_coefficient_summability_proved := True.intro
  quadratic_mass_le_linear_mass_squared := True.intro
  normalized_term_bound_proved := True.intro
  diagonal_kernel_bound_proved := True.intro
  diagonal_contract_closed_uniformly := True.intro
  separate_multiplicity_bound_not_needed := True.intro
  ts290_recounting_not_needed := True.intro
  rational_mass_upper_bound_not_proved := True.intro
  diagonal_half_budget_smallness_not_proved := True.intro
  kusmin_landau_deferred_to_ts317 := True.intro
  rh_not_assumed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS316
