import Mathlib.Tactic
import TS.Goldbach.Strong.TS318.WeightedKusminLandauKernelReduction

namespace TS319
namespace Goldbach

noncomputable section

/-!
# TS319: nonresonant discrete logarithmic phase bounds

This module closes the small-frequency branch of the TS318 phase contract,
records the exact dyadic increment geometry needed by Kusmin-Landau, and
inhabits the indexed TS318 contract with an unconditional height-dependent
constant.  It separates that coarse fact from the still-open uniform
oscillatory estimate needed for numerical smallness.

No global analytic assumption, RH, close-pair estimate, or rational half-budget is
introduced.
-/

theorem discreteLogPhase_norm_eq_one
    (x : Nat) (hx : 0 < x) (frequency : Real) :
    norm (TS318.Goldbach.discreteLogPhase x frequency) = 1 := by
  unfold TS318.Goldbach.discreteLogPhase
  rw [Complex.norm_natCast_cpow_of_pos hx]
  simp

theorem discreteLogPhasePartialSum_norm_le_card
    (X Y : Nat) (hX : 0 < X)
    (frequency : Real) :
    norm (Finset.sum (Finset.Ico X Y) (fun x =>
      TS318.Goldbach.discreteLogPhase x frequency)) <=
        (Finset.Ico X Y).card := by
  calc
    norm (Finset.sum (Finset.Ico X Y) (fun x =>
        TS318.Goldbach.discreteLogPhase x frequency)) <=
      Finset.sum (Finset.Ico X Y) (fun x =>
        norm (TS318.Goldbach.discreteLogPhase x frequency)) := norm_sum_le _ _
    _ = Finset.sum (Finset.Ico X Y) (fun _ => (1 : Real)) := by
      apply Finset.sum_congr rfl
      intro x hxMem
      exact discreteLogPhase_norm_eq_one x
        (lt_of_lt_of_le hX (Finset.mem_Ico.mp hxMem).1) frequency
    _ = (Finset.Ico X Y).card := by simp

theorem discreteLogPhasePartialSum_norm_le_scale
    (X Y : Nat) (hX : 0 < X) (hXY : X <= Y) (hY : Y <= 2 * X)
    (frequency : Real) :
    norm (Finset.sum (Finset.Ico X Y) (fun x =>
      TS318.Goldbach.discreteLogPhase x frequency)) <= (X : Real) := by
  have hCard := discreteLogPhasePartialSum_norm_le_card X Y hX frequency
  rw [Nat.card_Ico] at hCard
  have hSub : Y - X <= X := by omega
  exact hCard.trans (by exact_mod_cast hSub)

theorem safeFrequencyDecayWeight_eq_one_of_abs_le_one
    (frequency : Real) (hFrequency : abs frequency <= 1) :
    TS318.Goldbach.safeFrequencyDecayWeight frequency = 1 := by
  unfold TS318.Goldbach.safeFrequencyDecayWeight
  rw [max_eq_left hFrequency]
  norm_num

theorem discreteLogPhase_neg_eq_conj
    (x : Nat) (frequency : Real) :
    TS318.Goldbach.discreteLogPhase x (-frequency) =
      (starRingEnd Complex) (TS318.Goldbach.discreteLogPhase x frequency) := by
  unfold TS318.Goldbach.discreteLogPhase
  have hArg : Not ((x : Complex).arg = Real.pi) := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  rw [show Complex.I * ((-frequency : Real) : Complex) =
      (starRingEnd Complex) (Complex.I * (frequency : Complex)) by simp]
  simpa only [map_natCast] using
    Complex.cpow_conj (x : Complex) (Complex.I * (frequency : Complex)) hArg

theorem discreteLogPhasePartialSum_neg_norm_eq
    (X Y : Nat) (frequency : Real) :
    norm (Finset.sum (Finset.Ico X Y) (fun x =>
        TS318.Goldbach.discreteLogPhase x (-frequency))) =
      norm (Finset.sum (Finset.Ico X Y) (fun x =>
        TS318.Goldbach.discreteLogPhase x frequency)) := by
  have hSum :
      Finset.sum (Finset.Ico X Y) (fun x =>
          TS318.Goldbach.discreteLogPhase x (-frequency)) =
        (starRingEnd Complex) (Finset.sum (Finset.Ico X Y) (fun x =>
          TS318.Goldbach.discreteLogPhase x frequency)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact discreteLogPhase_neg_eq_conj x frequency
  calc
    norm (Finset.sum (Finset.Ico X Y) (fun x =>
        TS318.Goldbach.discreteLogPhase x (-frequency))) =
      norm ((starRingEnd Complex) (Finset.sum (Finset.Ico X Y) (fun x =>
        TS318.Goldbach.discreteLogPhase x frequency))) := congrArg norm hSum
    _ = norm (Finset.sum (Finset.Ico X Y) (fun x =>
        TS318.Goldbach.discreteLogPhase x frequency)) := norm_star _

noncomputable def logarithmicPhaseIncrement
    (n : Nat) (frequency : Real) : Real :=
  frequency * Real.log (((n + 1 : Nat) : Real) / (n : Real))

theorem discreteLogPhase_succ_eq_mul_exp_increment
    (n : Nat) (hn : 0 < n) (frequency : Real) :
    TS318.Goldbach.discreteLogPhase (n + 1) frequency =
      TS318.Goldbach.discreteLogPhase n frequency *
        Complex.exp (Complex.I * (logarithmicPhaseIncrement n frequency : Complex)) := by
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hnSuccReal : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hLog :
      Real.log ((n + 1 : Nat) : Real) =
        Real.log (n : Real) +
          Real.log (((n + 1 : Nat) : Real) / (n : Real)) := by
    rw [Real.log_div hnSuccReal.ne' hnReal.ne']
    ring
  unfold TS318.Goldbach.discreteLogPhase logarithmicPhaseIncrement
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.ne_of_gt hn)]
  rw [<- Complex.exp_add]
  congr 1
  rw [<- Complex.natCast_log, <- Complex.natCast_log]
  rw [hLog]
  push_cast
  ring

theorem log_succ_div_self_bounds
    (n : Nat) (hn : 0 < n) :
    1 / ((n + 1 : Nat) : Real) <=
        Real.log (((n + 1 : Nat) : Real) / (n : Real)) /\
      Real.log (((n + 1 : Nat) : Real) / (n : Real)) <=
        1 / (n : Real) := by
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hnSuccReal : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hRatio : (0 : Real) < ((n + 1 : Nat) : Real) / (n : Real) :=
    div_pos hnSuccReal hnReal
  have hLower := Real.one_sub_inv_le_log_of_pos hRatio
  have hUpper := Real.log_le_sub_one_of_pos hRatio
  have hRatioInv :
      Inv.inv (((n + 1 : Nat) : Real) / (n : Real)) =
        (n : Real) / ((n + 1 : Nat) : Real) := by
    rw [inv_div]
  have hLowerEq :
      1 - (n : Real) / ((n + 1 : Nat) : Real) =
        1 / ((n + 1 : Nat) : Real) := by
    field_simp
  have hUpperEq :
      ((n + 1 : Nat) : Real) / (n : Real) - 1 =
        1 / (n : Real) := by
    field_simp
  rw [hRatioInv, hLowerEq] at hLower
  rw [hUpperEq] at hUpper
  exact And.intro hLower hUpper

theorem logarithmicPhaseIncrement_bounds_of_pos
    (n : Nat) (hn : 0 < n)
    (frequency : Real) (hFrequency : 0 <= frequency) :
    frequency / ((n + 1 : Nat) : Real) <=
        logarithmicPhaseIncrement n frequency /\
      logarithmicPhaseIncrement n frequency <=
        frequency / (n : Real) := by
  have hBounds := log_succ_div_self_bounds n hn
  unfold logarithmicPhaseIncrement
  constructor
  case left =>
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hBounds.1 hFrequency
  case right =>
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hBounds.2 hFrequency

theorem logarithmicPhaseIncrement_succ_le
    (n : Nat) (hn : 0 < n)
    (frequency : Real) (hFrequency : 0 <= frequency) :
    logarithmicPhaseIncrement (n + 1) frequency <=
      logarithmicPhaseIncrement n frequency := by
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hnSuccReal : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hRatioPos :
      (0 : Real) < ((n + 2 : Nat) : Real) / ((n + 1 : Nat) : Real) := by
    positivity
  have hRatioLe :
      ((n + 2 : Nat) : Real) / ((n + 1 : Nat) : Real) <=
        ((n + 1 : Nat) : Real) / (n : Real) := by
    have hLeft :
        ((n + 2 : Nat) : Real) / ((n + 1 : Nat) : Real) =
          1 + 1 / ((n + 1 : Nat) : Real) := by
      field_simp
      ring
    have hRight :
        ((n + 1 : Nat) : Real) / (n : Real) =
          1 + 1 / (n : Real) := by
      field_simp
    rw [hLeft, hRight]
    exact add_le_add_left
      (one_div_le_one_div_of_le hnReal (by exact_mod_cast Nat.le_succ n)) 1
  have hLogLe := Real.log_le_log hRatioPos hRatioLe
  have hNum :
      ((n + 2 : Nat) : Real) = ((n + 1 : Nat) : Real) + 1 := by
    push_cast
    ring
  rw [hNum] at hLogLe
  unfold logarithmicPhaseIncrement
  simpa only [Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_left hLogLe hFrequency

theorem logarithmicPhaseIncrement_dyadic_bounds
    (X T n : Nat) (hX : 0 < X) (hnLower : X <= n) (hnUpper : n < 2 * X)
    (frequency : Real) (hFrequency : 1 < frequency)
    (hFrequencyUpper : frequency <= 2 * (T : Real))
    (hCompat : 4 * T <= X) :
    frequency / (2 * (X : Real)) <=
        logarithmicPhaseIncrement n frequency /\
      logarithmicPhaseIncrement n frequency <= 1 / 2 := by
  have hn : 0 < n := lt_of_lt_of_le hX hnLower
  have hBounds := logarithmicPhaseIncrement_bounds_of_pos n hn frequency
    (le_trans (by norm_num) hFrequency.le)
  have hnSuccLe : n + 1 <= 2 * X := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hXReal : (0 : Real) < (X : Real) := by exact_mod_cast hX
  have hFreqNonneg : 0 <= frequency := le_trans (by norm_num) hFrequency.le
  constructor
  case left =>
    calc
      frequency / (2 * (X : Real)) <=
          frequency / ((n + 1 : Nat) : Real) := by
        exact div_le_div_of_nonneg_left hFreqNonneg
          (by exact_mod_cast Nat.succ_pos n)
          (by exact_mod_cast hnSuccLe)
      _ <= logarithmicPhaseIncrement n frequency := hBounds.1
  case right =>
    have hFreqX : frequency <= (X : Real) / 2 := by
      have hCompatReal : (4 : Real) * (T : Real) <= (X : Real) := by
        exact_mod_cast hCompat
      nlinarith
    calc
      logarithmicPhaseIncrement n frequency <= frequency / (n : Real) :=
        hBounds.2
      _ <= ((X : Real) / 2) / (n : Real) := by
        exact div_le_div_of_nonneg_right hFreqX hnReal.le
      _ <= ((X : Real) / 2) / (X : Real) := by
        exact div_le_div_of_nonneg_left (by positivity) hXReal
          (by exact_mod_cast hnLower)
      _ = 1 / 2 := by
        field_simp
        ring

noncomputable def coarseLogPhaseConstant (T : Nat) : Real :=
  max 1 (2 * (T : Real))

theorem coarseLogPhaseConstant_nonnegative (T : Nat) :
    0 <= coarseLogPhaseConstant T := by
  unfold coarseLogPhaseConstant
  exact zero_le_one.trans (le_max_left 1 (2 * (T : Real)))

theorem coarseLogPhaseConstant_dominates_frequency
    (T : Nat) (frequency : Real)
    (hFrequency : abs frequency <= 2 * (T : Real)) :
    max 1 (abs frequency) <= coarseLogPhaseConstant T := by
  unfold coarseLogPhaseConstant
  exact max_le_max le_rfl hFrequency

theorem coarseNonresonantDiscreteLogPhasePartialSumBound
    (X T : Nat) (hCompat : 4 * T <= X) (hX : 0 < X) :
    TS318.Goldbach.NonresonantDiscreteLogPhasePartialSumBoundStatement
      X T (coarseLogPhaseConstant T) := by
  refine And.intro hCompat (And.intro (coarseLogPhaseConstant_nonnegative T) ?_)
  intro frequency hFrequency Y hXY hY
  have hTrivial := discreteLogPhasePartialSum_norm_le_scale
    X Y hX hXY hY frequency
  let D : Real := max 1 (abs frequency)
  have hDPos : 0 < D := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (abs frequency))
  have hDC : D <= coarseLogPhaseConstant T :=
    coarseLogPhaseConstant_dominates_frequency T frequency hFrequency
  have hFactorNonneg : 0 <= (X : Real) * (1 / D) :=
    mul_nonneg (Nat.cast_nonneg X) (one_div_nonneg.mpr hDPos.le)
  have hScale :
      (X : Real) <= coarseLogPhaseConstant T * (X : Real) * (1 / D) := by
    calc
      (X : Real) = D * ((X : Real) * (1 / D)) := by
        field_simp
      _ <= coarseLogPhaseConstant T * ((X : Real) * (1 / D)) :=
        mul_le_mul_of_nonneg_right hDC hFactorNonneg
      _ = coarseLogPhaseConstant T * (X : Real) * (1 / D) := by ring
  exact hTrivial.trans hScale

theorem coarseWeightedKusminLandauKernelBound
    (X T : Nat) (hCompat : 4 * T <= X) (hX : 0 < X) :
    TS317.Goldbach.WeightedKusminLandauKernelBoundStatement
      X T (4 * coarseLogPhaseConstant T) := by
  exact TS318.Goldbach.weightedKusminLandauKernelBound_of_partial_sum
    X T hX (coarseLogPhaseConstant T)
      (coarseNonresonantDiscreteLogPhasePartialSumBound X T hCompat hX)

def OscillatoryDiscreteLogPhasePartialSumBoundStatement
    (X T : Nat) (oscillationConstant : Real) : Prop :=
  4 * T <= X /\
    0 <= oscillationConstant /\
      forall frequency : Real,
        1 < abs frequency ->
          abs frequency <= 2 * (T : Real) ->
            forall Y : Nat, X <= Y -> Y <= 2 * X ->
              norm (Finset.sum (Finset.Ico X Y) (fun x =>
                TS318.Goldbach.discreteLogPhase x frequency)) <=
                  oscillationConstant * (X : Real) *
                    TS318.Goldbach.safeFrequencyDecayWeight frequency

def UniformOscillatoryDiscreteLogPhasePartialSumBoundStatement
    (oscillationConstant : Real) : Prop :=
  0 <= oscillationConstant /\
    forall X T : Nat, 0 < X -> 4 * T <= X ->
      OscillatoryDiscreteLogPhasePartialSumBoundStatement
        X T oscillationConstant

def UniformNonresonantDiscreteLogPhasePartialSumBoundStatement
    (oscillationConstant : Real) : Prop :=
  0 <= oscillationConstant /\
    forall X T : Nat, 0 < X -> 4 * T <= X ->
      TS318.Goldbach.NonresonantDiscreteLogPhasePartialSumBoundStatement
        X T oscillationConstant

theorem nonresonantBound_of_oscillatoryBound
    (X T : Nat) (hX : 0 < X) (oscillationConstant : Real)
    (hOsc : OscillatoryDiscreteLogPhasePartialSumBoundStatement
      X T oscillationConstant) :
    TS318.Goldbach.NonresonantDiscreteLogPhasePartialSumBoundStatement
      X T (max 1 oscillationConstant) := by
  refine And.intro hOsc.1 (And.intro (zero_le_one.trans (le_max_left 1 _)) ?_)
  intro frequency hFrequency Y hXY hY
  by_cases hSmall : abs frequency <= 1
  case pos =>
    rw [safeFrequencyDecayWeight_eq_one_of_abs_le_one frequency hSmall]
    have hTrivial := discreteLogPhasePartialSum_norm_le_scale
      X Y hX hXY hY frequency
    have hOne : (1 : Real) <= max 1 oscillationConstant := le_max_left _ _
    calc
      norm (Finset.sum (Finset.Ico X Y) (fun x =>
          TS318.Goldbach.discreteLogPhase x frequency)) <= (X : Real) := hTrivial
      _ = 1 * (X : Real) := by ring
      _ <= max 1 oscillationConstant * (X : Real) :=
        mul_le_mul_of_nonneg_right hOne (Nat.cast_nonneg X)
      _ = max 1 oscillationConstant * (X : Real) * 1 := by ring
  case neg =>
    have hLarge : 1 < abs frequency := lt_of_not_ge hSmall
    have hBound := hOsc.2.2 frequency hLarge hFrequency Y hXY hY
    have hConstant : oscillationConstant <= max 1 oscillationConstant :=
      le_max_right _ _
    have hFactor :
        0 <= (X : Real) * TS318.Goldbach.safeFrequencyDecayWeight frequency :=
      mul_nonneg (Nat.cast_nonneg X)
        (TS318.Goldbach.safeFrequencyDecayWeight_nonnegative frequency)
    calc
      norm (Finset.sum (Finset.Ico X Y) (fun x =>
          TS318.Goldbach.discreteLogPhase x frequency)) <=
        oscillationConstant * (X : Real) *
          TS318.Goldbach.safeFrequencyDecayWeight frequency := hBound
      _ <= max 1 oscillationConstant * (X : Real) *
          TS318.Goldbach.safeFrequencyDecayWeight frequency := by
        nlinarith

theorem uniformNonresonantBound_of_uniformOscillatoryBound
    (oscillationConstant : Real)
    (hOsc : UniformOscillatoryDiscreteLogPhasePartialSumBoundStatement
      oscillationConstant) :
    UniformNonresonantDiscreteLogPhasePartialSumBoundStatement
      (max 1 oscillationConstant) := by
  refine And.intro (zero_le_one.trans (le_max_left 1 _)) ?_
  intro X T hX hCompat
  exact nonresonantBound_of_oscillatoryBound X T hX oscillationConstant
    (hOsc.2 X T hX hCompat)

structure TS319Ledger where
  unit_modulus_phase_proved : True
  small_frequency_trivial_bound_proved : True
  negative_frequency_reduced_by_conjugation : True
  dyadic_increment_geometry_proved : True
  coarse_height_dependent_phase_contract_proved : True
  coarse_weighted_kernel_contract_proved : True
  uniform_oscillatory_kusmin_landau_not_proved : True
  close_pair_smallness_not_proved : True
  rational_half_budget_not_proved : True
  riemann_hypothesis_not_used : True
  goldbach_not_claimed : True

def ts319Ledger : TS319Ledger where
  unit_modulus_phase_proved := True.intro
  small_frequency_trivial_bound_proved := True.intro
  negative_frequency_reduced_by_conjugation := True.intro
  dyadic_increment_geometry_proved := True.intro
  coarse_height_dependent_phase_contract_proved := True.intro
  coarse_weighted_kernel_contract_proved := True.intro
  uniform_oscillatory_kusmin_landau_not_proved := True.intro
  close_pair_smallness_not_proved := True.intro
  rational_half_budget_not_proved := True.intro
  riemann_hypothesis_not_used := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS319
