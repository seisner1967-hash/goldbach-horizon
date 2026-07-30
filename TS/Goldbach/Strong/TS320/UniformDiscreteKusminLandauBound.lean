import Mathlib.Tactic
import TS.Goldbach.Strong.TS319.NonresonantDiscreteLogPhaseBound

namespace TS320
namespace Goldbach

noncomputable section

/-!
# TS320: uniform discrete Kusmin-Landau bound

This module proves a purely discrete unit-phase estimate for monotone positive
phase increments.  A direct exponential remainder bound controls the phase
chord, reciprocal differences have telescoping total variation, and finite
summation by parts yields the uniform constant `12 / gap`.

Instantiating the abstract result with the TS319 logarithmic increments gives
an absolute oscillatory constant `24`, independent of height.  The existing
TS318 transfer then closes the TS317 weighted pointwise kernel contract with
constant `96`.

No zero-spacing estimate, close-pair smallness, rational half-budget, RH,
OTSA, or Goldbach conclusion is introduced.
-/

noncomputable def phaseStep (u : Real) : Complex :=
  Complex.exp (Complex.I * (u : Complex)) - 1

noncomputable def phaseReciprocal (u : Real) : Complex :=
  Inv.inv (phaseStep u)

theorem phaseStep_norm_lower
    {u : Real} (hu : 0 < u) (huUpper : u <= 1 / 2) :
    u / 2 <= norm (phaseStep u) := by
  let x : Complex := Complex.I * (u : Complex)
  have hxNorm : norm x = u := by
    simp [x, abs_of_pos hu]
  have hxAbs : Complex.abs x <= 1 := by
    change norm x <= 1
    rw [hxNorm]
    linarith
  have hApprox := Complex.abs_exp_sub_one_sub_id_le hxAbs
  have hApproxNorm :
      norm (Complex.exp x - 1 - x) <= norm x ^ 2 := by
    exact hApprox
  have hTriangle :
      norm x <= norm (Complex.exp x - 1) +
        norm (Complex.exp x - 1 - x) := by
    calc
      norm x = norm ((Complex.exp x - 1) -
          (Complex.exp x - 1 - x)) := by ring_nf
      _ <= norm (Complex.exp x - 1) +
          norm (Complex.exp x - 1 - x) := norm_sub_le _ _
  have hSquare : u ^ 2 <= u / 2 := by nlinarith
  unfold phaseStep
  change u / 2 <= norm (Complex.exp x - 1)
  rw [hxNorm] at hApproxNorm hTriangle
  nlinarith

theorem phaseStep_ne_zero
    {u : Real} (hu : 0 < u) (huUpper : u <= 1 / 2) :
    Ne (phaseStep u) 0 := by
  have hLower := phaseStep_norm_lower hu huUpper
  have hPos : 0 < norm (phaseStep u) := by nlinarith
  exact norm_ne_zero_iff.mp hPos.ne'

theorem phaseReciprocal_norm_le
    {u gap : Real} (hGap : 0 < gap) (hGapU : gap <= u)
    (huUpper : u <= 1 / 2) :
    norm (phaseReciprocal u) <= 2 / gap := by
  have hu : 0 < u := hGap.trans_le hGapU
  have hLower := phaseStep_norm_lower hu huUpper
  unfold phaseReciprocal
  rw [norm_inv, inv_eq_one_div]
  calc
    1 / norm (phaseStep u) <= 1 / (u / 2) :=
      one_div_le_one_div_of_le (by positivity) hLower
    _ <= 1 / (gap / 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = 2 / gap := by field_simp

theorem phaseReciprocal_mul_phaseStep
    {u : Real} (hu : 0 < u) (huUpper : u <= 1 / 2) :
    phaseReciprocal u * phaseStep u = 1 := by
  unfold phaseReciprocal
  field_simp [phaseStep_ne_zero hu huUpper]

theorem phaseStep_sub_norm_le
    {v u : Real} (hv : 0 <= v) (hvu : v <= u) (huUpper : u <= 1 / 2) :
    norm (phaseStep u - phaseStep v) <= 2 * (u - v) := by
  let d : Real := u - v
  have hd : 0 <= d := sub_nonneg.mpr hvu
  have hdUpper : d <= 1 := by
    dsimp [d]
    linarith
  let x : Complex := Complex.I * (d : Complex)
  have hxNorm : norm x = d := by
    simp [x, abs_of_nonneg hd]
  have hxAbs : Complex.abs x <= 1 := by
    change norm x <= 1
    rw [hxNorm]
    exact hdUpper
  have hExp := Complex.abs_exp_sub_one_le hxAbs
  have hFactor :
      phaseStep u - phaseStep v =
        Complex.exp (Complex.I * (v : Complex)) *
          (Complex.exp x - 1) := by
    unfold phaseStep
    have hArg :
        Complex.I * (v : Complex) + x = Complex.I * (u : Complex) := by
      dsimp [x, d]
      push_cast
      ring
    calc
      (Complex.exp (Complex.I * (u : Complex)) - 1) -
          (Complex.exp (Complex.I * (v : Complex)) - 1) =
        Complex.exp (Complex.I * (u : Complex)) -
          Complex.exp (Complex.I * (v : Complex)) := by ring
      _ = Complex.exp (Complex.I * (v : Complex)) * Complex.exp x -
          Complex.exp (Complex.I * (v : Complex)) := by
        rw [<- Complex.exp_add, hArg]
      _ = Complex.exp (Complex.I * (v : Complex)) *
          (Complex.exp x - 1) := by ring
  have hUnit : norm (Complex.exp (Complex.I * (v : Complex))) = 1 := by
    rw [show Complex.I * (v : Complex) = (v : Complex) * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I v
  rw [hFactor, norm_mul, hUnit, one_mul]
  change norm (Complex.exp x - 1) <= 2 * d
  rw [<- hxNorm]
  exact hExp

theorem phaseReciprocal_sub_norm_le
    {v u : Real} (hv : 0 < v) (hvu : v <= u) (huUpper : u <= 1 / 2) :
    norm (phaseReciprocal v - phaseReciprocal u) <=
      8 * (1 / v - 1 / u) := by
  have hu : 0 < u := hv.trans_le hvu
  have hvUpper : v <= 1 / 2 := hvu.trans huUpper
  have hvStep : Ne (phaseStep v) 0 := phaseStep_ne_zero hv hvUpper
  have huStep : Ne (phaseStep u) 0 := phaseStep_ne_zero hu huUpper
  have hNumerator := phaseStep_sub_norm_le hv.le hvu huUpper
  have hvLower := phaseStep_norm_lower hv hvUpper
  have huLower := phaseStep_norm_lower hu huUpper
  have hDenominator :
      (v / 2) * (u / 2) <= norm (phaseStep v) * norm (phaseStep u) := by
    exact mul_le_mul hvLower huLower (by positivity) (norm_nonneg _)
  have hDenominatorPos :
      0 < norm (phaseStep v) * norm (phaseStep u) := by
    exact mul_pos
      (norm_pos_iff.mpr hvStep)
      (norm_pos_iff.mpr huStep)
  have hInvDenominator :
      1 / (norm (phaseStep v) * norm (phaseStep u)) <=
        1 / ((v / 2) * (u / 2)) := by
    exact one_div_le_one_div_of_le (by positivity) hDenominator
  unfold phaseReciprocal
  rw [inv_sub_inv hvStep huStep]
  rw [norm_div, norm_mul]
  calc
    norm (phaseStep u - phaseStep v) /
        (norm (phaseStep v) * norm (phaseStep u)) =
      norm (phaseStep u - phaseStep v) *
        (1 / (norm (phaseStep v) * norm (phaseStep u))) := by
          rw [div_eq_mul_inv, one_div]
    _ <= (2 * (u - v)) *
        (1 / (norm (phaseStep v) * norm (phaseStep u))) := by
      exact mul_le_mul_of_nonneg_right hNumerator
        (one_div_nonneg.mpr hDenominatorPos.le)
    _ <= (2 * (u - v)) * (1 / ((v / 2) * (u / 2))) := by
      exact mul_le_mul_of_nonneg_left hInvDenominator (by nlinarith)
    _ = 8 * (1 / v - 1 / u) := by
      field_simp
      ring

theorem sum_Ico_succ_sub
    (f : Nat -> Real) {m n : Nat} (hmn : m <= n) :
    Finset.sum (Finset.Ico m n) (fun i => f (i + 1) - f i) =
      f n - f m := by
  have h := congrArg Neg.neg
    (TS318.Goldbach.sum_Ico_sub_succ f hmn)
  rw [<- Finset.sum_neg_distrib] at h
  simpa only [neg_sub] using h

theorem phaseReciprocal_totalVariation_le
    (delta : Nat -> Real) {m n : Nat} (gap : Real)
    (hmn : m < n) (hGap : 0 < gap)
    (hDelta : forall k, m <= k -> k < n ->
      gap <= delta k /\ delta k <= 1 / 2)
    (hAnti : forall k, m <= k -> k + 1 < n ->
      delta (k + 1) <= delta k) :
    Finset.sum (Finset.Ico m (n - 1)) (fun k =>
      norm (phaseReciprocal (delta (k + 1)) -
        phaseReciprocal (delta k))) <= 8 / gap := by
  have hmLast : m <= n - 1 := Nat.le_sub_one_of_lt hmn
  have hTerm : forall k, Membership.mem (Finset.Ico m (n - 1)) k ->
      norm (phaseReciprocal (delta (k + 1)) -
          phaseReciprocal (delta k)) <=
        8 * (1 / delta (k + 1) - 1 / delta k) := by
    intro k hk
    have hkLower : m <= k := (Finset.mem_Ico.mp hk).1
    have hkSuccUpper : k + 1 < n := by
      have hkUpper := (Finset.mem_Ico.mp hk).2
      omega
    have hkUpper : k < n := lt_trans (Nat.lt_succ_self k) hkSuccUpper
    have hkData := hDelta k hkLower hkUpper
    have hkSuccData := hDelta (k + 1) (by omega) hkSuccUpper
    exact phaseReciprocal_sub_norm_le
      (hGap.trans_le hkSuccData.1)
      (hAnti k hkLower hkSuccUpper)
      hkData.2
  have hLastData := hDelta (n - 1) hmLast (by omega)
  have hFirstData := hDelta m le_rfl hmn
  calc
    Finset.sum (Finset.Ico m (n - 1)) (fun k =>
        norm (phaseReciprocal (delta (k + 1)) -
          phaseReciprocal (delta k))) <=
      Finset.sum (Finset.Ico m (n - 1)) (fun k =>
        8 * (1 / delta (k + 1) - 1 / delta k)) :=
          Finset.sum_le_sum hTerm
    _ = 8 * (1 / delta (n - 1) - 1 / delta m) := by
      rw [<- Finset.mul_sum]
      rw [sum_Ico_succ_sub (fun k => 1 / delta k) hmLast]
    _ <= 8 * (1 / gap) := by
      have hLastInv : 1 / delta (n - 1) <= 1 / gap :=
        one_div_le_one_div_of_le hGap hLastData.1
      have hFirstInv : 0 <= 1 / delta m := by
        exact one_div_nonneg.mpr (hGap.le.trans hFirstData.1)
      nlinarith
    _ = 8 / gap := by ring

theorem sum_Ico_mul_succ_sub
    (w z : Nat -> Complex) {m n : Nat} (hmn : m < n) :
    Finset.sum (Finset.Ico m n) (fun k =>
        w k * (z (k + 1) - z k)) =
      w (n - 1) * z n - w m * z m -
        Finset.sum (Finset.Ico m (n - 1)) (fun k =>
          (w (k + 1) - w k) * z (k + 1)) := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
      by_cases hmn' : m < n
      case pos =>
        rw [Finset.sum_Ico_succ_top (Nat.le_of_lt hmn')]
        rw [Nat.succ_sub_one]
        have hVariation :
            Finset.sum (Finset.Ico m n) (fun k =>
                (w (k + 1) - w k) * z (k + 1)) =
              Finset.sum (Finset.Ico m (n - 1)) (fun k =>
                  (w (k + 1) - w k) * z (k + 1)) +
                (w (n - 1 + 1) - w (n - 1)) * z (n - 1 + 1) := by
          have hmLast : m <= n - 1 := Nat.le_sub_one_of_lt hmn'
          conv_lhs =>
            rw [show n = n - 1 + 1 by omega]
          rw [Finset.sum_Ico_succ_top hmLast]
        rw [hVariation]
        rw [ih hmn']
        have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn'
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnPos.ne')]
        ring
      case neg =>
        have hmEq : m = n := by omega
        subst m
        rw [Nat.succ_sub_one]
        simp
        ring

def MonotoneUnitPhaseBoundStatement (C : Real) : Prop :=
  0 <= C /\
    forall (m n : Nat) (z : Nat -> Complex) (delta : Nat -> Real)
        (gap : Real),
      m < n ->
      0 < gap ->
      (forall k, m <= k -> k <= n -> norm (z k) = 1) ->
      (forall k, m <= k -> k < n ->
        z (k + 1) =
          z k * Complex.exp (Complex.I * (delta k : Complex))) ->
      (forall k, m <= k -> k + 1 < n ->
        delta (k + 1) <= delta k) ->
      (forall k, m <= k -> k < n ->
        gap <= delta k /\ delta k <= 1 / 2) ->
      norm (Finset.sum (Finset.Ico m n) z) <= C / gap

theorem monotoneUnitPhaseBound : MonotoneUnitPhaseBoundStatement 12 := by
  constructor
  case left => norm_num
  case right =>
   intro m n z delta gap hmn hGap hUnit hRecurrence hAnti hDelta
   let w : Nat -> Complex := fun k => phaseReciprocal (delta k)
   have hPointwise : forall k, m <= k -> k < n ->
      z k = w k * (z (k + 1) - z k) := by
    intro k hkLower hkUpper
    have hkData := hDelta k hkLower hkUpper
    have hkPos : 0 < delta k := hGap.trans_le hkData.1
    have hStep : phaseReciprocal (delta k) * phaseStep (delta k) = 1 :=
      phaseReciprocal_mul_phaseStep hkPos hkData.2
    have hDifference :
        z (k + 1) - z k = z k * phaseStep (delta k) := by
      rw [hRecurrence k hkLower hkUpper]
      unfold phaseStep
      ring
    dsimp [w]
    rw [hDifference]
    symm
    calc
      phaseReciprocal (delta k) * (z k * phaseStep (delta k)) =
          z k * (phaseReciprocal (delta k) * phaseStep (delta k)) := by ring
      _ = z k := by rw [hStep, mul_one]
   have hSumRewrite :
      Finset.sum (Finset.Ico m n) z =
        Finset.sum (Finset.Ico m n) (fun k =>
          w k * (z (k + 1) - z k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hPointwise k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
   have hBoundaryLast : norm (w (n - 1) * z n) <= 2 / gap := by
    have hmLast : m <= n - 1 := Nat.le_sub_one_of_lt hmn
    have hLastData := hDelta (n - 1) hmLast (by omega)
    rw [norm_mul, hUnit n (by omega) le_rfl, mul_one]
    exact phaseReciprocal_norm_le hGap hLastData.1 hLastData.2
   have hBoundaryFirst : norm (w m * z m) <= 2 / gap := by
    have hFirstData := hDelta m le_rfl hmn
    rw [norm_mul, hUnit m le_rfl (by omega), mul_one]
    exact phaseReciprocal_norm_le hGap hFirstData.1 hFirstData.2
   have hVariationNorm :
      norm (Finset.sum (Finset.Ico m (n - 1)) (fun k =>
        (w (k + 1) - w k) * z (k + 1))) <= 8 / gap := by
    calc
      norm (Finset.sum (Finset.Ico m (n - 1)) (fun k =>
          (w (k + 1) - w k) * z (k + 1))) <=
        Finset.sum (Finset.Ico m (n - 1)) (fun k =>
          norm ((w (k + 1) - w k) * z (k + 1))) := norm_sum_le _ _
      _ = Finset.sum (Finset.Ico m (n - 1)) (fun k =>
          norm (phaseReciprocal (delta (k + 1)) -
            phaseReciprocal (delta k))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkLower : m <= k := (Finset.mem_Ico.mp hk).1
        have hkFinUpper : k < n - 1 := (Finset.mem_Ico.mp hk).2
        have hkUpper : k + 1 < n := by omega
        rw [norm_mul, hUnit (k + 1) (by omega) (by omega), mul_one]
      _ <= 8 / gap :=
        phaseReciprocal_totalVariation_le delta gap hmn hGap hDelta hAnti
   rw [hSumRewrite, sum_Ico_mul_succ_sub w z hmn]
   calc
    norm (w (n - 1) * z n - w m * z m -
        Finset.sum (Finset.Ico m (n - 1)) (fun k =>
          (w (k + 1) - w k) * z (k + 1))) <=
      norm (w (n - 1) * z n) + norm (w m * z m) +
        norm (Finset.sum (Finset.Ico m (n - 1)) (fun k =>
          (w (k + 1) - w k) * z (k + 1))) := by
      calc
        norm (w (n - 1) * z n - w m * z m -
            Finset.sum (Finset.Ico m (n - 1)) (fun k =>
              (w (k + 1) - w k) * z (k + 1))) <=
          norm (w (n - 1) * z n - w m * z m) +
            norm (Finset.sum (Finset.Ico m (n - 1)) (fun k =>
              (w (k + 1) - w k) * z (k + 1))) := norm_sub_le _ _
        _ <= norm (w (n - 1) * z n) + norm (w m * z m) +
            norm (Finset.sum (Finset.Ico m (n - 1)) (fun k =>
              (w (k + 1) - w k) * z (k + 1))) := by
          gcongr
          exact norm_sub_le _ _
    _ <= 2 / gap + 2 / gap + 8 / gap := by gcongr
    _ = 12 / gap := by ring

theorem safeFrequencyDecayWeight_eq_one_div_abs
    {frequency : Real} (hFrequency : 1 < abs frequency) :
    TS318.Goldbach.safeFrequencyDecayWeight frequency =
      1 / abs frequency := by
  unfold TS318.Goldbach.safeFrequencyDecayWeight
  rw [max_eq_right hFrequency.le]

theorem positiveDiscreteLogPhasePartialSumBound
    (X T : Nat) (hX : 0 < X) (hCompat : 4 * T <= X)
    (frequency : Real) (hFrequency : 1 < frequency)
    (hFrequencyUpper : frequency <= 2 * (T : Real))
    (Y : Nat) (hXY : X <= Y) (hY : Y <= 2 * X) :
    norm (Finset.sum (Finset.Ico X Y) (fun x =>
      TS318.Goldbach.discreteLogPhase x frequency)) <=
        24 * (X : Real) *
          TS318.Goldbach.safeFrequencyDecayWeight frequency := by
  by_cases hEq : X = Y
  case pos =>
    subst Y
    simp
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg X))
      (TS318.Goldbach.safeFrequencyDecayWeight_nonnegative frequency)
  case neg =>
    have hXYlt : X < Y := lt_of_le_of_ne hXY hEq
    let gap : Real := frequency / (2 * (X : Real))
    have hXReal : 0 < (X : Real) := by exact_mod_cast hX
    have hGap : 0 < gap := by
      dsimp [gap]
      positivity
    have hAbstract := monotoneUnitPhaseBound.2 X Y
      (fun x => TS318.Goldbach.discreteLogPhase x frequency)
      (fun x => TS319.Goldbach.logarithmicPhaseIncrement x frequency)
      gap hXYlt hGap
    have hUnit : forall k, X <= k -> k <= Y ->
        norm (TS318.Goldbach.discreteLogPhase k frequency) = 1 := by
      intro k hkLower _
      exact TS319.Goldbach.discreteLogPhase_norm_eq_one k
        (lt_of_lt_of_le hX hkLower) frequency
    have hRecurrence : forall k, X <= k -> k < Y ->
        TS318.Goldbach.discreteLogPhase (k + 1) frequency =
          TS318.Goldbach.discreteLogPhase k frequency *
            Complex.exp (Complex.I *
              (TS319.Goldbach.logarithmicPhaseIncrement k frequency :
                Complex)) := by
      intro k hkLower _
      exact TS319.Goldbach.discreteLogPhase_succ_eq_mul_exp_increment
        k (lt_of_lt_of_le hX hkLower) frequency
    have hAnti : forall k, X <= k -> k + 1 < Y ->
        TS319.Goldbach.logarithmicPhaseIncrement (k + 1) frequency <=
          TS319.Goldbach.logarithmicPhaseIncrement k frequency := by
      intro k hkLower _
      exact TS319.Goldbach.logarithmicPhaseIncrement_succ_le k
        (lt_of_lt_of_le hX hkLower) frequency (by linarith)
    have hDelta : forall k, X <= k -> k < Y ->
        gap <= TS319.Goldbach.logarithmicPhaseIncrement k frequency /\
          TS319.Goldbach.logarithmicPhaseIncrement k frequency <= 1 / 2 := by
      intro k hkLower hkUpper
      dsimp [gap]
      exact TS319.Goldbach.logarithmicPhaseIncrement_dyadic_bounds
        X T k hX hkLower (lt_of_lt_of_le hkUpper hY) frequency
          hFrequency hFrequencyUpper hCompat
    have hBound := hAbstract hUnit hRecurrence hAnti hDelta
    have hFrequencyPos : 0 < frequency := by linarith
    have hAbs : abs frequency = frequency := abs_of_pos hFrequencyPos
    have hAbsLarge : 1 < abs frequency := by rwa [hAbs]
    calc
      norm (Finset.sum (Finset.Ico X Y) (fun x =>
          TS318.Goldbach.discreteLogPhase x frequency)) <= 12 / gap := hBound
      _ = 24 * (X : Real) * (1 / frequency) := by
        dsimp [gap]
        field_simp
        ring
      _ = 24 * (X : Real) *
          TS318.Goldbach.safeFrequencyDecayWeight frequency := by
        rw [safeFrequencyDecayWeight_eq_one_div_abs hAbsLarge, hAbs]

theorem uniformOscillatoryDiscreteLogPhasePartialSumBound :
    TS319.Goldbach.UniformOscillatoryDiscreteLogPhasePartialSumBoundStatement
      24 := by
  constructor
  case left => norm_num
  case right =>
    intro X T hX hCompat
    refine And.intro hCompat (And.intro (by norm_num) ?_)
    intro frequency hFrequency hFrequencyUpper Y hXY hY
    by_cases hFrequencyNonneg : 0 <= frequency
    case pos =>
      have hFrequencyPos : 1 < frequency := by
        rwa [abs_of_nonneg hFrequencyNonneg] at hFrequency
      exact positiveDiscreteLogPhasePartialSumBound X T hX hCompat
        frequency hFrequencyPos
          (by rwa [abs_of_nonneg hFrequencyNonneg] at hFrequencyUpper)
            Y hXY hY
    case neg =>
      have hFrequencyNeg : frequency < 0 := lt_of_not_ge hFrequencyNonneg
      let positiveFrequency : Real := -frequency
      have hPositiveFrequency : 1 < positiveFrequency := by
        dsimp [positiveFrequency]
        rwa [abs_of_neg hFrequencyNeg] at hFrequency
      have hPositiveFrequencyUpper :
          positiveFrequency <= 2 * (T : Real) := by
        dsimp [positiveFrequency]
        rwa [abs_of_neg hFrequencyNeg] at hFrequencyUpper
      have hPositiveBound := positiveDiscreteLogPhasePartialSumBound
        X T hX hCompat positiveFrequency hPositiveFrequency
          hPositiveFrequencyUpper Y hXY hY
      have hNormEq :=
        TS319.Goldbach.discreteLogPhasePartialSum_neg_norm_eq
          X Y positiveFrequency
      have hWeightEq :
          TS318.Goldbach.safeFrequencyDecayWeight positiveFrequency =
            TS318.Goldbach.safeFrequencyDecayWeight frequency := by
        unfold TS318.Goldbach.safeFrequencyDecayWeight
        dsimp [positiveFrequency]
        rw [abs_neg]
      calc
        norm (Finset.sum (Finset.Ico X Y) (fun x =>
            TS318.Goldbach.discreteLogPhase x frequency)) =
          norm (Finset.sum (Finset.Ico X Y) (fun x =>
            TS318.Goldbach.discreteLogPhase x positiveFrequency)) := by
              simpa [positiveFrequency] using hNormEq
        _ <= 24 * (X : Real) *
            TS318.Goldbach.safeFrequencyDecayWeight positiveFrequency :=
              hPositiveBound
        _ = 24 * (X : Real) *
            TS318.Goldbach.safeFrequencyDecayWeight frequency := by rw [hWeightEq]

theorem uniformNonresonantDiscreteLogPhasePartialSumBound :
    TS319.Goldbach.UniformNonresonantDiscreteLogPhasePartialSumBoundStatement
      24 := by
  simpa using
    TS319.Goldbach.uniformNonresonantBound_of_uniformOscillatoryBound 24
      uniformOscillatoryDiscreteLogPhasePartialSumBound

theorem uniformWeightedKusminLandauKernelBound
    (X T : Nat) (hX : 0 < X) (hCompat : 4 * T <= X) :
    TS317.Goldbach.WeightedKusminLandauKernelBoundStatement X T 96 := by
  have hPhase := uniformNonresonantDiscreteLogPhasePartialSumBound.2
    X T hX hCompat
  have hKernel := TS318.Goldbach.weightedKusminLandauKernelBound_of_partial_sum
    X T hX 24 hPhase
  norm_num at hKernel
  exact hKernel

structure TS320Ledger where
  phase_step_lower_bound_proved : True
  phase_reciprocal_variation_proved : True
  finite_summation_by_parts_identity_proved : True
  monotone_unit_phase_bound_proved : True
  uniform_oscillatory_log_phase_bound_proved : True
  uniform_nonresonant_phase_contract_proved : True
  weighted_kusmin_landau_kernel_contract_proved : True
  close_pair_envelope_smallness_not_proved : True
  rational_half_budget_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts320Ledger : TS320Ledger where
  phase_step_lower_bound_proved := True.intro
  phase_reciprocal_variation_proved := True.intro
  finite_summation_by_parts_identity_proved := True.intro
  monotone_unit_phase_bound_proved := True.intro
  uniform_oscillatory_log_phase_bound_proved := True.intro
  uniform_nonresonant_phase_contract_proved := True.intro
  weighted_kusmin_landau_kernel_contract_proved := True.intro
  close_pair_envelope_smallness_not_proved := True.intro
  rational_half_budget_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS320
