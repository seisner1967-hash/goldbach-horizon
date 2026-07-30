import Mathlib.Tactic
import TS.Goldbach.Strong.TS316.QuantitativeDiagonalZeroCorrelationBound

namespace TS317
namespace Goldbach

noncomputable section

/-!
# Weighted off-diagonal correlation reduction

This module exposes the exact oscillatory power in the TS315 ordered-pair
kernel and closes a coarse absolute off-diagonal bound from TS292 summability.
It then separates the genuinely oscillatory input into two finite contracts:
a weighted Kusmin-Landau kernel estimate and a close-pair envelope bound.

The zero truncation remains the finite `truncatedZeroSet T`, the real amplitude
is retained in the exponent `rho + conj sigma - 2`, and equal ordinates are
handled by the close-pair branch.  No division by an unproved nonzero ordinate
gap, global zero-pair `tsum`, RH, or zero-simplicity assumption is introduced.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

/-! ## Exact weighted oscillatory kernel -/

/-- Exact multiplicity and Mellin-denominator coefficient. -/
noncomputable def exactZeroCoefficient
    (rho : ConcreteNontrivialZero) : Complex :=
  TS268.Goldbach.concreteMultiplicityDenominatorFactor rho.1

/-- Exact exponent after the two canonical `2 / x` normalizations. -/
noncomputable def offDiagonalComplexExponent
    (rho sigma : ConcreteNontrivialZero) : Complex :=
  rho.1 + (starRingEnd Complex) sigma.1 - 2

/-- Exact ordered coefficient product, including both multiplicities. -/
noncomputable def offDiagonalCoefficientProduct
    (rho sigma : ConcreteNontrivialZero) : Complex :=
  exactZeroCoefficient rho *
    (starRingEnd Complex) (exactZeroCoefficient sigma)

/-- The TS315 term is the canonical normalization times the exact TS268 factor. -/
theorem normalizedTruncatedZeroTerm_eq_factorized
    (x : Nat)
    (rho : ConcreteNontrivialZero) :
    TS315.Goldbach.normalizedTruncatedZeroTerm x rho =
      ((TS313.Goldbach.canonicalTraceNormalizationFactor x : Real) :
          Complex) *
        ((x : Complex) ^ rho.1 * exactZeroCoefficient rho) := by
  unfold TS315.Goldbach.normalizedTruncatedZeroTerm
    TS292.Goldbach.infiniteZeroSpectralTerm
    exactZeroCoefficient
  rw [TS268.Goldbach.concreteFiniteHeightZeroTerm_eq_scale_mul_factor]

/-- Conjugation of a positive natural-base complex power conjugates its exponent. -/
theorem conj_natCast_cpow_eq_cpow_conj
    (x : Nat)
    (sigma : ConcreteNontrivialZero) :
    (starRingEnd Complex) ((x : Complex) ^ sigma.1) =
      (x : Complex) ^ ((starRingEnd Complex) sigma.1) := by
  have hArg : Not ((x : Complex).arg = Real.pi) := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  symm
  simpa only [map_natCast] using
    Complex.cpow_conj (x : Complex) sigma.1 hArg

/-- The two complex powers combine with the conjugated second exponent. -/
theorem natCast_cpow_mul_conj_eq_cpow_add_conj
    (x : Nat)
    (hx : 0 < x)
    (rho sigma : ConcreteNontrivialZero) :
    (x : Complex) ^ rho.1 *
        (starRingEnd Complex) ((x : Complex) ^ sigma.1) =
      (x : Complex) ^
        (rho.1 + (starRingEnd Complex) sigma.1) := by
  have hxC : Not ((x : Complex) = 0) := by
    exact_mod_cast Nat.ne_of_gt hx
  rw [conj_natCast_cpow_eq_cpow_conj x sigma,
    (Complex.cpow_add _ _ hxC).symm]

/-- Exact pointwise weighted power identity; the exponent is `-2`, not `-4`. -/
theorem normalizedPairTerm_eq_weightedCpow
    (x : Nat)
    (hx : 0 < x)
    (rho sigma : ConcreteNontrivialZero) :
    TS315.Goldbach.normalizedTruncatedZeroTerm x rho *
        (starRingEnd Complex)
          (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma) =
      4 * offDiagonalCoefficientProduct rho sigma *
        (x : Complex) ^ offDiagonalComplexExponent rho sigma := by
  have hxC : Not ((x : Complex) = 0) := by
    exact_mod_cast Nat.ne_of_gt hx
  rw [normalizedTruncatedZeroTerm_eq_factorized,
    normalizedTruncatedZeroTerm_eq_factorized]
  simp only [map_mul, Complex.conj_ofReal]
  unfold TS313.Goldbach.canonicalTraceNormalizationFactor
  push_cast
  unfold offDiagonalCoefficientProduct offDiagonalComplexExponent
  rw [Complex.cpow_sub _ _ hxC, Complex.cpow_two,
    Complex.cpow_add _ _ hxC,
    (conj_natCast_cpow_eq_cpow_conj x sigma).symm]
  field_simp
  ring

/-- Exact finite weighted-power representation of one TS315 pair kernel. -/
theorem normalizedZeroPairCorrelationKernel_eq_weightedCpow_sum
    (X : Nat)
    (hX : 0 < X)
    (rho sigma : ConcreteNontrivialZero) :
    TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma =
      Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
        4 * offDiagonalCoefficientProduct rho sigma *
          (x : Complex) ^ offDiagonalComplexExponent rho sigma) := by
  unfold TS315.Goldbach.normalizedZeroPairCorrelationKernel
  apply Finset.sum_congr rfl
  intro x hxWindow
  have hxOne := TS314.Goldbach.one_le_of_mem_dyadicWindow hX hxWindow
  exact normalizedPairTerm_eq_weightedCpow x
    (Nat.zero_lt_of_lt hxOne) rho sigma

/-! ## Coarse unconditional off-diagonal control -/

/-- One pair kernel, after dyadic averaging, has the absolute coefficient bound. -/
theorem normalizedZeroPairCorrelationKernel_div_norm_le
    (X : Nat)
    (hX : 0 < X)
    (rho sigma : ConcreteNontrivialZero) :
    norm
        (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma /
          (X : Complex)) <=
      4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
        TS316.Goldbach.zeroCoefficientMagnitude sigma := by
  have hXReal : (0 : Real) < (X : Real) := by exact_mod_cast hX
  have hKernel :
      norm (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) <=
        4 * (X : Real) * TS316.Goldbach.zeroCoefficientMagnitude rho *
          TS316.Goldbach.zeroCoefficientMagnitude sigma := by
    unfold TS315.Goldbach.normalizedZeroPairCorrelationKernel
    calc
      norm
          (Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
            TS315.Goldbach.normalizedTruncatedZeroTerm x rho *
              (starRingEnd Complex)
                (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma))) <=
        Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
          norm
            (TS315.Goldbach.normalizedTruncatedZeroTerm x rho *
              (starRingEnd Complex)
                (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma))) :=
        norm_sum_le _ _
      _ <= Finset.sum (TS314.Goldbach.dyadicWindow X) (fun _ =>
          4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
            TS316.Goldbach.zeroCoefficientMagnitude sigma) := by
        apply Finset.sum_le_sum
        intro x hxWindow
        have hxOne := TS314.Goldbach.one_le_of_mem_dyadicWindow hX hxWindow
        have hRho :=
          TS316.Goldbach.normalizedTruncatedZeroTerm_norm_le_two_mul_coefficient
            x hxOne rho
        have hSigma :=
          TS316.Goldbach.normalizedTruncatedZeroTerm_norm_le_two_mul_coefficient
            x hxOne sigma
        rw [norm_mul]
        have hConjNorm :
            norm
                ((starRingEnd Complex)
                  (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma)) =
              norm (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma) := by
          simpa only [Complex.norm_eq_abs] using
            Complex.abs_conj
              (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma)
        rw [hConjNorm]
        nlinarith [norm_nonneg
            (TS315.Goldbach.normalizedTruncatedZeroTerm x rho),
          norm_nonneg (TS315.Goldbach.normalizedTruncatedZeroTerm x sigma),
          TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho,
          TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma]
      _ = 4 * (X : Real) * TS316.Goldbach.zeroCoefficientMagnitude rho *
          TS316.Goldbach.zeroCoefficientMagnitude sigma := by
        rw [Finset.sum_const, TS314.Goldbach.dyadicWindow_card]
        simp only [nsmul_eq_mul]
        ring
  rw [norm_div, Complex.norm_natCast]
  calc
    norm (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) /
        (X : Real) <=
      (4 * (X : Real) * TS316.Goldbach.zeroCoefficientMagnitude rho *
          TS316.Goldbach.zeroCoefficientMagnitude sigma) / (X : Real) :=
      div_le_div_of_nonneg_right hKernel hXReal.le
    _ = 4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
        TS316.Goldbach.zeroCoefficientMagnitude sigma := by
      field_simp
      ring

/-- Finite absolute coefficient mass over the exact ordered off-diagonal pairs. -/
noncomputable def finiteOffDiagonalCoefficientMass
    (T : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
    Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
      TS316.Goldbach.zeroCoefficientMagnitude rho *
        TS316.Goldbach.zeroCoefficientMagnitude sigma))

theorem finiteOffDiagonalCoefficientMass_nonnegative
    (T : Nat) :
    0 <= finiteOffDiagonalCoefficientMass T := by
  unfold finiteOffDiagonalCoefficientMass
  apply Finset.sum_nonneg
  intro rho hRho
  apply Finset.sum_nonneg
  intro sigma hSigma
  exact mul_nonneg
    (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)
    (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma)

/-- The finite off-diagonal mass is bounded by the global TS292 linear mass squared. -/
theorem finiteOffDiagonalCoefficientMass_le_globalLinear_sq
    (T : Nat) :
    finiteOffDiagonalCoefficientMass T <=
      TS316.Goldbach.globalLinearSpectralMass ^ 2 := by
  let Z := TS315.Goldbach.truncatedZeroSet T
  let a := TS316.Goldbach.zeroCoefficientMagnitude
  have ha0 : forall rho, 0 <= a rho :=
    TS316.Goldbach.zeroCoefficientMagnitude_nonnegative
  have hFiniteNonnegative : 0 <= Finset.sum Z a :=
    Finset.sum_nonneg (fun rho hRho => ha0 rho)
  have hFiniteLeGlobal :
      Finset.sum Z a <= TS316.Goldbach.globalLinearSpectralMass := by
    unfold TS316.Goldbach.globalLinearSpectralMass
    exact sum_le_tsum Z (fun rho hRho => ha0 rho)
      TS316.Goldbach.zeroCoefficientMagnitude_summable
  unfold finiteOffDiagonalCoefficientMass
  change Finset.sum Z (fun rho =>
      Finset.sum (Z.erase rho) (fun sigma => a rho * a sigma)) <= _
  calc
    Finset.sum Z (fun rho =>
        Finset.sum (Z.erase rho) (fun sigma => a rho * a sigma)) <=
      Finset.sum Z (fun rho =>
        Finset.sum Z (fun sigma => a rho * a sigma)) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun sigma hSigma hNotMem => mul_nonneg (ha0 rho) (ha0 sigma))
    _ = (Finset.sum Z a) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
    _ <= TS316.Goldbach.globalLinearSpectralMass ^ 2 := by
      nlinarith [TS316.Goldbach.globalLinearSpectralMass_nonnegative]

/-- The exact off-diagonal correlation is bounded by its finite coefficient mass. -/
theorem offDiagonalNormalizedZeroPairCorrelation_norm_le_mass
    (X T : Nat)
    (hX : 0 < X) :
    norm (TS315.Goldbach.offDiagonalNormalizedZeroPairCorrelation X T) <=
      4 * finiteOffDiagonalCoefficientMass T := by
  unfold TS315.Goldbach.offDiagonalNormalizedZeroPairCorrelation
  rw [Finset.sum_div]
  calc
    norm
        (Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
          Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
              (fun sigma =>
                TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) /
            (X : Complex))) <=
      Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        norm
          (Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
              (fun sigma =>
                TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) /
            (X : Complex))) :=
      norm_sum_le _ _
    _ <= Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
          norm
            (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma /
              (X : Complex)))) := by
      apply Finset.sum_le_sum
      intro rho hRho
      rw [Finset.sum_div]
      exact norm_sum_le _ _
    _ <= Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
          4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
            TS316.Goldbach.zeroCoefficientMagnitude sigma)) := by
      apply Finset.sum_le_sum
      intro rho hRho
      apply Finset.sum_le_sum
      intro sigma hSigma
      exact normalizedZeroPairCorrelationKernel_div_norm_le X hX rho sigma
    _ = 4 * finiteOffDiagonalCoefficientMass T := by
      unfold finiteOffDiagonalCoefficientMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hRho
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma hSigma
      ring

/-- A coarse unconditional TS315 off-diagonal contract under its stored compatibility. -/
theorem weightedZeroOrdinatePairCorrelationWindowBound_coarse
    (X T : Nat)
    (hX : 0 < X)
    (hCompat : 4 * T <= X) :
    TS315.Goldbach.WeightedZeroOrdinatePairCorrelationWindowBoundStatement
      X T (4 * TS316.Goldbach.globalLinearSpectralMass ^ 2) := by
  refine And.intro hCompat (And.intro (by positivity) ?_)
  exact (offDiagonalNormalizedZeroPairCorrelation_norm_le_mass X T hX).trans
    ((mul_le_mul_of_nonneg_left
      (finiteOffDiagonalCoefficientMass_le_globalLinear_sq T) (by norm_num)))

/-- The full finite moment has a coarse unconditional real bound as well. -/
theorem finiteQuadraticSpectralMomentBound_coarse
    (X T : Nat)
    (hX : 0 < X)
    (hCompat : 4 * T <= X) :
    TS314.Goldbach.FiniteQuadraticSpectralMomentBoundStatement X T
      (3 * TS316.Goldbach.globalLinearSpectralMass) := by
  apply TS315.Goldbach.finiteQuadraticSpectralMoment_le_of_pair_bounds
    X T
    (4 * TS316.Goldbach.globalLinearSpectralMass ^ 2)
    (4 * TS316.Goldbach.globalLinearSpectralMass ^ 2)
    (3 * TS316.Goldbach.globalLinearSpectralMass)
  case hDiagonal =>
    exact TS316.Goldbach.diagonalZeroCorrelationBound_by_linearMass X T hX
  case hOffDiagonal =>
    exact weightedZeroOrdinatePairCorrelationWindowBound_coarse X T hX hCompat
  case hTotal =>
    nlinarith [TS316.Goldbach.globalLinearSpectralMass_nonnegative]

/-! ## Phase-aware finite reduction -/

/-- Absolute gap between the two zero ordinates. -/
noncomputable def zeroOrdinateGap
    (rho sigma : ConcreteNontrivialZero) : Real :=
  abs (rho.1.im - sigma.1.im)

/-- Safe close-pair weight: one for gaps at most one, reciprocal thereafter. -/
noncomputable def ordinateGapDecayWeight
    (rho sigma : ConcreteNontrivialZero) : Real :=
  1 / max 1 (zeroOrdinateGap rho sigma)

theorem ordinateGapDecayWeight_nonnegative
    (rho sigma : ConcreteNontrivialZero) :
    0 <= ordinateGapDecayWeight rho sigma := by
  unfold ordinateGapDecayWeight
  positivity

theorem ordinateGapDecayWeight_le_one
    (rho sigma : ConcreteNontrivialZero) :
    ordinateGapDecayWeight rho sigma <= 1 := by
  unfold ordinateGapDecayWeight
  simpa using one_div_le_one_div_of_le
    (by norm_num : (0 : Real) < 1)
    (le_max_left 1 (zeroOrdinateGap rho sigma))

/-- Finite project-weighted close-pair envelope at truncation height `T`. -/
noncomputable def weightedClosePairEnvelope
    (T : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
    Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
      TS316.Goldbach.zeroCoefficientMagnitude rho *
        TS316.Goldbach.zeroCoefficientMagnitude sigma *
          ordinateGapDecayWeight rho sigma))

theorem weightedClosePairEnvelope_nonnegative
    (T : Nat) :
    0 <= weightedClosePairEnvelope T := by
  unfold weightedClosePairEnvelope
  apply Finset.sum_nonneg
  intro rho hRho
  apply Finset.sum_nonneg
  intro sigma hSigma
  exact mul_nonneg
    (mul_nonneg
      (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)
      (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma))
    (ordinateGapDecayWeight_nonnegative rho sigma)

/-- The gap weight only decreases the finite absolute coefficient mass. -/
theorem weightedClosePairEnvelope_le_finiteOffDiagonalCoefficientMass
    (T : Nat) :
    weightedClosePairEnvelope T <= finiteOffDiagonalCoefficientMass T := by
  unfold weightedClosePairEnvelope finiteOffDiagonalCoefficientMass
  apply Finset.sum_le_sum
  intro rho hRho
  apply Finset.sum_le_sum
  intro sigma hSigma
  exact mul_le_of_le_one_right
    (mul_nonneg
      (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)
      (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma))
    (ordinateGapDecayWeight_le_one rho sigma)

/-- The phase-aware pair envelope also has a coarse global TS292 bound. -/
theorem weightedClosePairEnvelope_le_globalLinear_sq
    (T : Nat) :
    weightedClosePairEnvelope T <=
      TS316.Goldbach.globalLinearSpectralMass ^ 2 :=
  (weightedClosePairEnvelope_le_finiteOffDiagonalCoefficientMass T).trans
    (finiteOffDiagonalCoefficientMass_le_globalLinear_sq T)

/--
The elementary weighted Kusmin-Landau output needed for every concrete pair.
It includes the close-pair branch, so equal ordinates never cause division by
zero.  TS317 names but does not inhabit this analytic statement.
-/
def WeightedKusminLandauKernelBoundStatement
    (X T : Nat)
    (oscillationConstant : Real) : Prop :=
  4 * T <= X /\
    0 <= oscillationConstant /\
      forall rho, Membership.mem (TS315.Goldbach.truncatedZeroSet T) rho ->
        forall sigma,
          Membership.mem
              ((TS315.Goldbach.truncatedZeroSet T).erase rho) sigma ->
            norm
                (TS315.Goldbach.normalizedZeroPairCorrelationKernel
                    X rho sigma /
                  (X : Complex)) <=
              oscillationConstant *
                TS316.Goldbach.zeroCoefficientMagnitude rho *
                TS316.Goldbach.zeroCoefficientMagnitude sigma *
                ordinateGapDecayWeight rho sigma

/-- A quantitative bound for the exact finite close-pair envelope. -/
def WeightedClosePairEnvelopeBoundStatement
    (T : Nat)
    (pairMajorant : Real) : Prop :=
  0 <= pairMajorant /\
    weightedClosePairEnvelope T <= pairMajorant

/-- A coarse pair-envelope certificate is already unconditional. -/
theorem weightedClosePairEnvelopeBound_coarse
    (T : Nat) :
    WeightedClosePairEnvelopeBoundStatement T
      (TS316.Goldbach.globalLinearSpectralMass ^ 2) :=
  And.intro (sq_nonneg TS316.Goldbach.globalLinearSpectralMass)
    (weightedClosePairEnvelope_le_globalLinear_sq T)

/-- The two analytic inputs imply the exact TS315 weighted pair contract. -/
theorem weightedZeroOrdinatePairCorrelationWindowBound_of_reduction
    (X T : Nat)
    (oscillationConstant pairMajorant : Real)
    (hKernel :
      WeightedKusminLandauKernelBoundStatement X T oscillationConstant)
    (hPairs : WeightedClosePairEnvelopeBoundStatement T pairMajorant) :
    TS315.Goldbach.WeightedZeroOrdinatePairCorrelationWindowBoundStatement
      X T (oscillationConstant * pairMajorant) := by
  refine And.intro hKernel.1 (And.intro (mul_nonneg hKernel.2.1 hPairs.1) ?_)
  unfold TS315.Goldbach.offDiagonalNormalizedZeroPairCorrelation
  rw [Finset.sum_div]
  calc
    norm
        (Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
          Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
              (fun sigma =>
                TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) /
            (X : Complex))) <=
      Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
          norm
            (TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma /
              (X : Complex)))) := by
      calc
        norm
            (Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
              Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
                  (fun sigma =>
                    TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) /
                (X : Complex))) <=
          Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
            norm
              (Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
                  (fun sigma =>
                    TS315.Goldbach.normalizedZeroPairCorrelationKernel X rho sigma) /
                (X : Complex))) := norm_sum_le _ _
        _ <= _ := by
          apply Finset.sum_le_sum
          intro rho hRho
          rw [Finset.sum_div]
          exact norm_sum_le _ _
    _ <= oscillationConstant * weightedClosePairEnvelope T := by
      unfold weightedClosePairEnvelope
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro rho hRho
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro sigma hSigma
      simpa only [mul_assoc] using hKernel.2.2 rho hRho sigma hSigma
    _ <= oscillationConstant * pairMajorant :=
      mul_le_mul_of_nonneg_left hPairs.2 hKernel.2.1

/-! ## Audit ledger -/

structure TS317Ledger where
  exact_normalized_factorization_proved : True
  exact_weighted_exponent_minus_two_proved : True
  finite_truncation_preserved : True
  equal_ordinate_division_avoided : True
  coarse_off_diagonal_bound_proved : True
  coarse_ts315_contract_inhabited : True
  coarse_finite_moment_bound_proved : True
  weighted_kusmin_landau_statement_named : True
  weighted_close_pair_envelope_named : True
  coarse_close_pair_envelope_bound_proved : True
  weighted_reduction_to_ts315_proved : True
  weighted_kusmin_landau_not_proved : True
  close_pair_smallness_not_proved : True
  half_budget_not_proved : True
  rh_not_assumed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts317Ledger : TS317Ledger where
  exact_normalized_factorization_proved := True.intro
  exact_weighted_exponent_minus_two_proved := True.intro
  finite_truncation_preserved := True.intro
  equal_ordinate_division_avoided := True.intro
  coarse_off_diagonal_bound_proved := True.intro
  coarse_ts315_contract_inhabited := True.intro
  coarse_finite_moment_bound_proved := True.intro
  weighted_kusmin_landau_statement_named := True.intro
  weighted_close_pair_envelope_named := True.intro
  coarse_close_pair_envelope_bound_proved := True.intro
  weighted_reduction_to_ts315_proved := True.intro
  weighted_kusmin_landau_not_proved := True.intro
  close_pair_smallness_not_proved := True.intro
  half_budget_not_proved := True.intro
  rh_not_assumed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS317
