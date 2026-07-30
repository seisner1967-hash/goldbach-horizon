import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import TS.Goldbach.Strong.TS317.WeightedOffDiagonalCorrelationReduction

namespace TS318
namespace Goldbach

noncomputable section

/-!
# Weighted Kusmin-Landau kernel reduction

This module separates the exact TS317 weighted complex power into a positive
decreasing real amplitude and a pure logarithmic phase.  A finite Abel
summation theorem transfers any uniform partial-sum estimate for the pure
phase to the weighted pair kernel without losing a factor in the variation.

The nonresonant discrete logarithmic-phase estimate is recorded as a named,
uninhabited contract.  Under that contract, TS318 inhabits the pointwise
TS317 weighted kernel statement with constant `4 * oscillationConstant`.
No global zero mass enters this pointwise constant.  The actual
Kusmin-Landau estimate, close-pair smallness, rational half-budget, RH, OTSA,
and Goldbach remain explicitly open.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

noncomputable def offDiagonalRealExponent
    (rho sigma : ConcreteNontrivialZero) : Real :=
  rho.1.re + sigma.1.re - 2

noncomputable def offDiagonalFrequency
    (rho sigma : ConcreteNontrivialZero) : Real :=
  rho.1.im - sigma.1.im

theorem offDiagonalComplexExponent_eq_real_add_frequency
    (rho sigma : ConcreteNontrivialZero) :
    TS317.Goldbach.offDiagonalComplexExponent rho sigma =
      (offDiagonalRealExponent rho sigma : Complex) +
        Complex.I * (offDiagonalFrequency rho sigma : Complex) := by
  apply Complex.ext
  next =>
    simp [TS317.Goldbach.offDiagonalComplexExponent,
      offDiagonalRealExponent, offDiagonalFrequency]
  next =>
    simp [TS317.Goldbach.offDiagonalComplexExponent,
      offDiagonalRealExponent, offDiagonalFrequency]
    ring

theorem offDiagonalRealExponent_nonpositive
    (rho sigma : ConcreteNontrivialZero) :
    offDiagonalRealExponent rho sigma <= 0 := by
  have hRho := TS264.Goldbach.concreteZero_in_critical_strip rho.property
  have hSigma := TS264.Goldbach.concreteZero_in_critical_strip sigma.property
  unfold TS185.Goldbach.criticalStripPredicate at hRho hSigma
  unfold offDiagonalRealExponent
  linarith

noncomputable def discreteLogPhase
    (x : Nat) (frequency : Real) : Complex :=
  (x : Complex) ^ (Complex.I * (frequency : Complex))

noncomputable def offDiagonalAmplitude
    (x : Nat) (rho sigma : ConcreteNontrivialZero) : Real :=
  (x : Real) ^ offDiagonalRealExponent rho sigma

theorem cpow_eq_amplitude_mul_phase
    (x : Nat) (hx : 0 < x)
    (rho sigma : ConcreteNontrivialZero) :
    (x : Complex) ^ TS317.Goldbach.offDiagonalComplexExponent rho sigma =
      (offDiagonalAmplitude x rho sigma : Complex) *
        discreteLogPhase x (offDiagonalFrequency rho sigma) := by
  rw [offDiagonalComplexExponent_eq_real_add_frequency]
  rw [Complex.cpow_add _ _ (by exact_mod_cast Nat.ne_of_gt hx)]
  unfold offDiagonalAmplitude discreteLogPhase
  rw [Complex.ofReal_cpow (Nat.cast_nonneg x)]
  norm_num

theorem offDiagonalAmplitude_nonnegative
    (x : Nat) (rho sigma : ConcreteNontrivialZero) :
    0 <= offDiagonalAmplitude x rho sigma := by
  unfold offDiagonalAmplitude
  positivity

theorem offDiagonalAmplitude_le_one
    (x : Nat) (hx : 1 <= x)
    (rho sigma : ConcreteNontrivialZero) :
    offDiagonalAmplitude x rho sigma <= 1 := by
  unfold offDiagonalAmplitude
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hx)
    (offDiagonalRealExponent_nonpositive rho sigma)

theorem offDiagonalAmplitude_antitone_of_pos
    {x y : Nat} (hx : 0 < x) (hxy : x <= y)
    (rho sigma : ConcreteNontrivialZero) :
    offDiagonalAmplitude y rho sigma <=
      offDiagonalAmplitude x rho sigma := by
  unfold offDiagonalAmplitude
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast hx)
    (by exact_mod_cast hxy)
    (offDiagonalRealExponent_nonpositive rho sigma)

noncomputable def truncatedLogPhase
    (X : Nat) (frequency : Real) (x : Nat) : Complex :=
  if X <= x then discreteLogPhase x frequency else 0

noncomputable def truncatedLogPhasePartialSum
    (X Y : Nat) (frequency : Real) : Complex :=
  Finset.sum (Finset.range Y) (truncatedLogPhase X frequency)

theorem truncatedLogPhasePartialSum_eq_Ico
    (X Y : Nat) (frequency : Real) :
    truncatedLogPhasePartialSum X Y frequency =
      Finset.sum (Finset.Ico X Y) (fun x => discreteLogPhase x frequency) := by
  unfold truncatedLogPhasePartialSum truncatedLogPhase
  have hFilter :
      Finset.sum (Finset.filter (fun x => X <= x) (Finset.range Y))
          (fun x => discreteLogPhase x frequency) =
        Finset.sum (Finset.range Y) (fun x =>
          if X <= x then discreteLogPhase x frequency else 0) :=
    Finset.sum_filter (fun x => X <= x) (fun x => discreteLogPhase x frequency)
  rw [hFilter.symm]
  refine Finset.sum_congr ?_ ?_
  next =>
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact and_comm
  next =>
    intro x hx
    rfl

theorem sum_Ico_sub_succ
    (f : Nat -> Real) {m n : Nat} (hmn : m <= n) :
    Finset.sum (Finset.Ico m n) (fun i => f i - f (i + 1)) =
      f m - f n := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      simp
  | succ n ih =>
      by_cases hm : m <= n
      case pos =>
        rw [Finset.sum_Ico_succ_top hm]
        rw [ih hm]
        ring
      case neg =>
        have hmEq : m = n + 1 := by omega
        subst m
        simp

theorem norm_weighted_sum_le_of_partial_sum_bound
    (f : Nat -> Real) (g : Nat -> Complex) {m n : Nat}
    (B : Real) (hmn : m < n)
    (hf0 : forall i, m <= i -> i < n -> 0 <= f i)
    (hfAnti : forall i, m <= i -> i + 1 < n -> f (i + 1) <= f i)
    (hPartial : forall k, m <= k -> k <= n ->
      norm (Finset.sum (Finset.range k) g) <= B)
    (hPartialStart : Finset.sum (Finset.range m) g = 0) :
    norm (Finset.sum (Finset.Ico m n) (fun i => (f i : Complex) * g i)) <=
      f m * B := by
  have hmLast : m <= n - 1 := Nat.le_sub_one_of_lt hmn
  have hLast0 : 0 <= f (n - 1) :=
    hf0 (n - 1) hmLast (Nat.sub_lt (by omega) (by omega))
  have hLast :
      norm ((f (n - 1) : Complex) * Finset.sum (Finset.range n) g) <=
        f (n - 1) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLast0]
    exact mul_le_mul_of_nonneg_left (hPartial n (by omega) le_rfl) hLast0
  have hVariationTerm : forall i, Membership.mem (Finset.Ico m (n - 1)) i ->
      norm (((f (i + 1) - f i : Real) : Complex) *
        Finset.sum (Finset.range (i + 1)) g) <=
        (f i - f (i + 1)) * B := by
    intro i hi
    have hiLower : m <= i := (Finset.mem_Ico.mp hi).1
    have hiUpper : i + 1 < n := by
      have := (Finset.mem_Ico.mp hi).2
      omega
    have hMono : f (i + 1) <= f i := hfAnti i hiLower hiUpper
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hMono)]
    rw [neg_sub]
    exact mul_le_mul_of_nonneg_left
      (hPartial (i + 1) (by omega) (by omega)) (sub_nonneg.mpr hMono)
  have hVariation :
      norm (Finset.sum (Finset.Ico m (n - 1)) (fun i =>
        (((f (i + 1) - f i : Real) : Complex) *
          Finset.sum (Finset.range (i + 1)) g))) <=
        (f m - f (n - 1)) * B := by
    calc
      norm (Finset.sum (Finset.Ico m (n - 1)) (fun i =>
          (((f (i + 1) - f i : Real) : Complex) *
            Finset.sum (Finset.range (i + 1)) g))) <=
          Finset.sum (Finset.Ico m (n - 1)) (fun i =>
            norm (((f (i + 1) - f i : Real) : Complex) *
              Finset.sum (Finset.range (i + 1)) g)) := norm_sum_le _ _
      _ <= Finset.sum (Finset.Ico m (n - 1)) (fun i =>
          (f i - f (i + 1)) * B) := by
        exact Finset.sum_le_sum hVariationTerm
      _ = (f m - f (n - 1)) * B := by
        have hMul := Finset.sum_mul (Finset.Ico m (n - 1))
          (fun i => f i - f (i + 1)) B
        rw [hMul.symm]
        rw [sum_Ico_sub_succ f hmLast]
  have hAbel := Finset.sum_Ico_by_parts f g hmn
  change
    Finset.sum (Finset.Ico m n) (fun i => (f i : Complex) * g i) =
      (f (n - 1) : Complex) * Finset.sum (Finset.range n) g -
        (f m : Complex) * Finset.sum (Finset.range m) g -
          Finset.sum (Finset.Ico m (n - 1)) (fun i =>
            ((f (i + 1) - f i : Real) : Complex) *
              Finset.sum (Finset.range (i + 1)) g) at hAbel
  rw [hAbel]
  rw [hPartialStart, mul_zero, sub_zero]
  calc
    norm ((f (n - 1) : Complex) * Finset.sum (Finset.range n) g -
        Finset.sum (Finset.Ico m (n - 1)) (fun i =>
          (((f (i + 1) - f i : Real) : Complex) *
            Finset.sum (Finset.range (i + 1)) g))) <=
      norm ((f (n - 1) : Complex) * Finset.sum (Finset.range n) g) +
        norm (Finset.sum (Finset.Ico m (n - 1)) (fun i =>
          (((f (i + 1) - f i : Real) : Complex) *
            Finset.sum (Finset.range (i + 1)) g))) :=
      by exact norm_sub_le _ _
    _ <= f (n - 1) * B + (f m - f (n - 1)) * B :=
      add_le_add hLast hVariation
    _ = f m * B := by ring

noncomputable def safeFrequencyDecayWeight
    (frequency : Real) : Real :=
  1 / max 1 (abs frequency)

theorem safeFrequencyDecayWeight_nonnegative
    (frequency : Real) :
    0 <= safeFrequencyDecayWeight frequency := by
  unfold safeFrequencyDecayWeight
  positivity

theorem safeFrequencyDecayWeight_eq_ordinateGapDecayWeight
    (rho sigma : ConcreteNontrivialZero) :
    safeFrequencyDecayWeight (offDiagonalFrequency rho sigma) =
      TS317.Goldbach.ordinateGapDecayWeight rho sigma := by
  rfl

theorem offDiagonalFrequency_abs_le_two_mul_height
    (T : Nat)
    (rho sigma : ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet T) rho)
    (hSigma : Membership.mem
      ((TS315.Goldbach.truncatedZeroSet T).erase rho) sigma) :
    abs (offDiagonalFrequency rho sigma) <= 2 * (T : Real) := by
  have hRhoHeight : abs rho.1.im <= (T : Real) := by
    exact (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff T rho).mp hRho
  have hSigmaSet : Membership.mem
      (TS315.Goldbach.truncatedZeroSet T) sigma :=
    (Finset.mem_erase.mp hSigma).2
  have hSigmaHeight : abs sigma.1.im <= (T : Real) := by
    exact (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff T sigma).mp
      hSigmaSet
  unfold offDiagonalFrequency
  calc
    abs (rho.1.im - sigma.1.im) <= abs rho.1.im + abs sigma.1.im :=
      abs_sub _ _
    _ <= (T : Real) + (T : Real) := add_le_add hRhoHeight hSigmaHeight
    _ = 2 * (T : Real) := by ring

theorem offDiagonalCoefficientProduct_norm_eq
    (rho sigma : ConcreteNontrivialZero) :
    norm (4 * TS317.Goldbach.offDiagonalCoefficientProduct rho sigma) =
      4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
        TS316.Goldbach.zeroCoefficientMagnitude sigma := by
  unfold TS317.Goldbach.offDiagonalCoefficientProduct
    TS317.Goldbach.exactZeroCoefficient
  rw [norm_mul, norm_mul]
  have hStar :
      norm ((starRingEnd Complex)
          (TS268.Goldbach.concreteMultiplicityDenominatorFactor sigma.1)) =
        norm (TS268.Goldbach.concreteMultiplicityDenominatorFactor sigma.1) := by
    exact norm_star _
  rw [hStar]
  norm_num
  rw [TS316.Goldbach.zeroCoefficientMagnitude_eq_factor_abs,
    TS316.Goldbach.zeroCoefficientMagnitude_eq_factor_abs]
  ring

def NonresonantDiscreteLogPhasePartialSumBoundStatement
    (X T : Nat) (oscillationConstant : Real) : Prop :=
  4 * T <= X /\
    0 <= oscillationConstant /\
      forall frequency : Real,
        abs frequency <= 2 * (T : Real) ->
          forall Y : Nat, X <= Y -> Y <= 2 * X ->
            norm (Finset.sum (Finset.Ico X Y) (fun x =>
              discreteLogPhase x frequency)) <=
                oscillationConstant * (X : Real) *
                  safeFrequencyDecayWeight frequency

theorem weightedCpowSum_norm_le_of_partial_sum_bound
    (X : Nat) (hX : 0 < X)
    (rho sigma : ConcreteNontrivialZero)
    (B : Real) (hB : 0 <= B)
    (hPartial : forall Y : Nat, X <= Y -> Y <= 2 * X ->
      norm (Finset.sum (Finset.Ico X Y) (fun x =>
        discreteLogPhase x (offDiagonalFrequency rho sigma))) <= B) :
    norm (Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
      (x : Complex) ^ TS317.Goldbach.offDiagonalComplexExponent rho sigma)) <=
        B := by
  let f : Nat -> Real := fun x => offDiagonalAmplitude x rho sigma
  let g : Nat -> Complex :=
    truncatedLogPhase X (offDiagonalFrequency rho sigma)
  have hf0 : forall i, X <= i -> i < 2 * X -> 0 <= f i := by
    intro i hiLower hiUpper
    exact offDiagonalAmplitude_nonnegative i rho sigma
  have hfAnti : forall i, X <= i -> i + 1 < 2 * X -> f (i + 1) <= f i := by
    intro i hiLower hiUpper
    exact offDiagonalAmplitude_antitone_of_pos
      (lt_of_lt_of_le hX hiLower) (Nat.le_succ i) rho sigma
  have hPartialRange : forall Y, X <= Y -> Y <= 2 * X ->
      norm (Finset.sum (Finset.range Y) g) <= B := by
    intro Y hXY hYUpper
    rw [show Finset.sum (Finset.range Y) g =
        Finset.sum (Finset.Ico X Y) (fun x =>
          discreteLogPhase x (offDiagonalFrequency rho sigma)) by
      exact truncatedLogPhasePartialSum_eq_Ico X Y
        (offDiagonalFrequency rho sigma)]
    exact hPartial Y hXY hYUpper
  have hPartialStart : Finset.sum (Finset.range X) g = 0 := by
    unfold g truncatedLogPhase
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [not_le_of_gt hi]
  have hWeighted :
      norm (Finset.sum (Finset.Ico X (2 * X))
        (fun x => (f x : Complex) * g x)) <=
        f X * B := by
    exact norm_weighted_sum_le_of_partial_sum_bound f g B
      (by omega) hf0 hfAnti hPartialRange hPartialStart
  have hAmplitude : f X <= 1 := by
    exact offDiagonalAmplitude_le_one X (Nat.one_le_iff_ne_zero.mpr hX.ne')
      rho sigma
  have hWeightedLe : f X * B <= B := by
    nlinarith
  rw [TS314.Goldbach.dyadicWindow]
  have hRewrite :
      Finset.sum (Finset.Ico X (2 * X)) (fun x =>
          (x : Complex) ^
            TS317.Goldbach.offDiagonalComplexExponent rho sigma) =
        Finset.sum (Finset.Ico X (2 * X))
          (fun x => (f x : Complex) * g x) := by
    apply Finset.sum_congr rfl
    intro x hxWindow
    have hxPos : 0 < x := lt_of_lt_of_le hX (Finset.mem_Ico.mp hxWindow).1
    rw [cpow_eq_amplitude_mul_phase x hxPos rho sigma]
    unfold f g truncatedLogPhase
    simp [Finset.mem_Ico.mp hxWindow |>.1]
  rw [hRewrite]
  exact hWeighted.trans hWeightedLe

theorem weightedKusminLandauKernelBound_of_partial_sum
    (X T : Nat) (hX : 0 < X)
    (oscillationConstant : Real)
    (hPhase : NonresonantDiscreteLogPhasePartialSumBoundStatement
      X T oscillationConstant) :
    TS317.Goldbach.WeightedKusminLandauKernelBoundStatement
      X T (4 * oscillationConstant) := by
  refine And.intro hPhase.1 (And.intro (mul_nonneg (by norm_num) hPhase.2.1) ?_)
  intro rho hRho sigma hSigma
  have hFrequency := offDiagonalFrequency_abs_le_two_mul_height
    T rho sigma hRho hSigma
  let B : Real := oscillationConstant * (X : Real) *
    safeFrequencyDecayWeight (offDiagonalFrequency rho sigma)
  have hB : 0 <= B := by
    exact mul_nonneg
      (mul_nonneg hPhase.2.1 (Nat.cast_nonneg X))
      (safeFrequencyDecayWeight_nonnegative _)
  have hPower :
      norm (Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
        (x : Complex) ^ TS317.Goldbach.offDiagonalComplexExponent rho sigma)) <=
        B := by
    apply weightedCpowSum_norm_le_of_partial_sum_bound X hX rho sigma B hB
    intro Y hXY hYUpper
    exact hPhase.2.2 (offDiagonalFrequency rho sigma) hFrequency
      Y hXY hYUpper
  have hXReal : (0 : Real) < (X : Real) := by exact_mod_cast hX
  rw [TS317.Goldbach.normalizedZeroPairCorrelationKernel_eq_weightedCpow_sum
    X hX rho sigma]
  have hMul := Finset.mul_sum (TS314.Goldbach.dyadicWindow X)
    (fun x => (x : Complex) ^
      TS317.Goldbach.offDiagonalComplexExponent rho sigma)
    (4 * TS317.Goldbach.offDiagonalCoefficientProduct rho sigma)
  rw [hMul.symm]
  rw [norm_div, norm_mul, Complex.norm_natCast]
  rw [offDiagonalCoefficientProduct_norm_eq]
  calc
    (4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
          TS316.Goldbach.zeroCoefficientMagnitude sigma *
        norm (Finset.sum (TS314.Goldbach.dyadicWindow X) (fun x =>
          (x : Complex) ^
            TS317.Goldbach.offDiagonalComplexExponent rho sigma))) /
        (X : Real) <=
      (4 * TS316.Goldbach.zeroCoefficientMagnitude rho *
          TS316.Goldbach.zeroCoefficientMagnitude sigma * B) /
        (X : Real) := by
      apply div_le_div_of_nonneg_right _ hXReal.le
      exact mul_le_mul_of_nonneg_left hPower
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho))
          (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma))
    _ = (4 * oscillationConstant) *
        TS316.Goldbach.zeroCoefficientMagnitude rho *
        TS316.Goldbach.zeroCoefficientMagnitude sigma *
        TS317.Goldbach.ordinateGapDecayWeight rho sigma := by
      unfold B
      rw [safeFrequencyDecayWeight_eq_ordinateGapDecayWeight]
      field_simp
      ring

/-! ## Audit ledger -/

structure TS318Ledger where
  exact_real_phase_decomposition_proved : True
  amplitude_nonnegative_and_decreasing_proved : True
  finite_abel_transfer_proved : True
  safe_frequency_weight_matches_ts317 : True
  finite_height_frequency_bound_proved : True
  coefficient_norm_preserved : True
  nonresonant_partial_sum_statement_named : True
  weighted_ts317_kernel_reduction_proved : True
  pure_kusmin_landau_bound_not_proved : True
  close_pair_smallness_not_proved : True
  rational_half_budget_not_proved : True
  rh_not_assumed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts318Ledger : TS318Ledger where
  exact_real_phase_decomposition_proved := True.intro
  amplitude_nonnegative_and_decreasing_proved := True.intro
  finite_abel_transfer_proved := True.intro
  safe_frequency_weight_matches_ts317 := True.intro
  finite_height_frequency_bound_proved := True.intro
  coefficient_norm_preserved := True.intro
  nonresonant_partial_sum_statement_named := True.intro
  weighted_ts317_kernel_reduction_proved := True.intro
  pure_kusmin_landau_bound_not_proved := True.intro
  close_pair_smallness_not_proved := True.intro
  rational_half_budget_not_proved := True.intro
  rh_not_assumed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS318
