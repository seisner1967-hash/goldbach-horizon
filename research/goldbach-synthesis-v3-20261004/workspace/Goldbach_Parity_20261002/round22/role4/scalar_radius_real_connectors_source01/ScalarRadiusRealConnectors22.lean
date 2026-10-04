import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
SOURCE ONLY. Real connectors for the fixed scalar Mellin radius.
No local prospective imports, candidate evaluation, or compiler invocation.
The conclusions concern an explicit real expression; they do not compute a
circle coefficient or assert a sign for any arithmetic residue.
-/

noncomputable section

open Set
open scoped BigOperators

namespace GoldbachScalarRadius22

def pointA : ℝ := 1 / 100000000
def pointHeight : ℝ := 100000000000
def pointTau : ℝ := 1 / 1000000

def radiusAmplitude (a : ℝ) : ℝ :=
  Real.exp (-a) / (1 - Real.exp (-a)) ^ 2

def radiusDecay (a : ℝ) : ℝ := Real.arctan (a / Real.pi) / 2

def radiusEpsilon (a H : ℝ) : ℝ :=
  24 * Real.exp (-radiusDecay a * H) / (Real.pi * a ^ 2 * radiusDecay a)

def radiusError (a H : ℝ) (N : ℕ) : ℝ :=
  Real.exp (a * (N : ℝ)) *
    (2 * radiusAmplitude a * radiusEpsilon a H + radiusEpsilon a H ^ 2)

theorem atanGap_hasDerivAt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.arctan y - y / (1 + y))
      (2 * x / ((1 + x ^ 2) * (1 + x) ^ 2)) x := by
  have hp : 0 < 1 + x := by linarith
  have hq : 0 < 1 + x ^ 2 := by positivity
  have hd := (Real.hasDerivAt_arctan x).sub
    ((hasDerivAt_id x).div
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hp.ne')
  convert hd using 1 <;> field_simp [hp.ne', hq.ne'] <;> ring

theorem atan_lower_nonneg {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.arctan x := by
  have hc : ContinuousOn (fun y : ℝ => Real.arctan y - y / (1 + y)) (Ici 0) :=
    fun y hy => (atanGap_hasDerivAt hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn (fun y : ℝ => Real.arctan y - y / (1 + y)) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc
      (fun y hy => (atanGap_hasDerivAt (by
        rw [interior_Ici, mem_Ioi] at hy
        exact hy.le)).hasDerivWithinAt)
      (fun y hy => by
        rw [interior_Ici, mem_Ioi] at hy
        exact div_nonneg (mul_nonneg (by norm_num) hy.le)
          (mul_nonneg (by positivity) (sq_nonneg (1 + y))))
  have hz := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx hx
  simp only [Real.arctan_zero, zero_div, sub_zero] at hz
  exact sub_nonneg.mp hz

theorem amplitude_eq_sinh {a : ℝ} (ha : 0 < a) :
    radiusAmplitude a = 1 / (2 * Real.sinh (a / 2)) ^ 2 := by
  have hh : a / 2 ≤ Real.sinh (a / 2) :=
    Real.self_le_sinh_iff.mpr (by linarith)
  have hs : 0 < 2 * Real.sinh (a / 2) := by linarith
  have ht : Real.exp (a / 2) * Real.exp (-(a / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hv : Real.exp (-(a / 2)) ^ 2 = Real.exp (-a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-(a / 2)) * (2 * Real.sinh (a / 2)) =
      1 - Real.exp (-a) := by
    rw [Real.sinh_eq]
    nlinarith [ht, hv]
  have hp : 0 < 1 - Real.exp (-a) := by
    rw [← he]
    exact mul_pos (Real.exp_pos _) hs
  have hcross : Real.exp (-a) * (2 * Real.sinh (a / 2)) ^ 2 =
      (1 - Real.exp (-a)) ^ 2 := by
    rw [← he, ← hv]
    ring
  unfold radiusAmplitude
  apply (div_eq_div_iff (pow_ne_zero 2 hp.ne') (pow_ne_zero 2 hs.ne')).mpr
  simpa only [one_mul] using hcross

theorem amplitude_le_inv_square {a : ℝ} (ha : 0 < a) :
    radiusAmplitude a ≤ 1 / a ^ 2 := by
  have hh : a / 2 ≤ Real.sinh (a / 2) :=
    Real.self_le_sinh_iff.mpr (by linarith)
  have hs : 0 < 2 * Real.sinh (a / 2) := by linarith
  have hsq : a ^ 2 ≤ (2 * Real.sinh (a / 2)) ^ 2 := by
    exact pow_le_pow_left₀ ha.le (by linarith) 2
  rw [amplitude_eq_sinh ha]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos ha)).mpr
    (by simpa only [one_mul] using hsq)

theorem pointA_pos : 0 < pointA := by norm_num [pointA]

theorem pointHeight_nonneg : 0 ≤ pointHeight := by norm_num [pointHeight]

theorem decay_point_gt : 1 / (8 * (100000000 : ℝ)) < radiusDecay pointA := by
  have ha := pointA_pos
  have hp : 0 < Real.pi + pointA := add_pos Real.pi_pos ha
  have hsmall : pointA < (1 : ℝ) / 2 := by norm_num [pointA]
  have hpi : Real.pi + pointA < 4 := by linarith [Real.pi_lt_d2]
  have hden : 0 < 1 + pointA / Real.pi := by positivity
  have he : (pointA / Real.pi) / (1 + pointA / Real.pi) =
      pointA / (Real.pi + pointA) := by
    field_simp [Real.pi_ne_zero, hden.ne', hp.ne'] <;> ring
  have hb := atan_lower_nonneg (div_nonneg ha.le Real.pi_pos.le)
  rw [he] at hb
  have hf : pointA / 4 < pointA / (Real.pi + pointA) :=
    (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hp).mpr (by nlinarith)
  have hfin : pointA / 4 < Real.arctan (pointA / Real.pi) := hf.trans_le hb
  unfold radiusDecay
  norm_num [pointA] at hfin ⊢
  linarith

theorem decay_point_pos : 0 < radiusDecay pointA :=
  lt_trans (by norm_num) decay_point_gt

theorem finite_exp_five : (100 : ℝ) < Real.exp 5 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 7
  have he : (∑ k ∈ Finset.range 7, (5 : ℝ) ^ k / (Nat.factorial k : ℝ)) =
      (16289 : ℝ) / 144 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [he] at hs
  linarith

theorem exp125_gt : (10 : ℝ) ^ 50 < Real.exp 125 := by
  have hp : (100 : ℝ) ^ 25 < Real.exp 5 ^ 25 :=
    pow_lt_pow_left₀ finite_exp_five (by norm_num) (by norm_num)
  have he : Real.exp 125 = Real.exp 5 ^ 25 := by
    convert Real.exp_nat_mul (5 : ℝ) 25 using 1 <;> norm_num
  rw [he]
  convert hp using 1 <;> norm_num

theorem exp_neg125_lt : Real.exp (-125) < 1 / (10 : ℝ) ^ 50 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_div_iff₀ (Real.exp_pos 125) (by norm_num)).mpr
  simpa only [one_mul] using exp125_gt

theorem exp_neg250_eq_square : Real.exp (-250) = Real.exp (-125) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  norm_num

theorem exp_one_lt3 : Real.exp 1 < 3 := by
  linarith [Real.exp_one_lt_d9]

theorem amplitude_point_le : radiusAmplitude pointA ≤ (100000000 : ℝ) ^ 2 := by
  have h := amplitude_le_inv_square pointA_pos
  norm_num [pointA] at h ⊢
  exact h

theorem epsilon_point_pos : 0 < radiusEpsilon pointA pointHeight := by
  unfold radiusEpsilon
  exact div_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (mul_pos (mul_pos Real.pi_pos (sq_pos_of_pos pointA_pos)) decay_point_pos)

theorem epsilon_point_lt : radiusEpsilon pointA pointHeight < 64 / (10 : ℝ) ^ 26 := by
  have hd := decay_point_gt
  have hdp := decay_point_pos
  have hexp : Real.exp (-radiusDecay pointA * pointHeight) ≤ Real.exp (-125) := by
    apply Real.exp_le_exp.mpr
    norm_num [pointHeight] at hd ⊢
    linarith
  have hden : (3 : ℝ) / (8 * (100000000 : ℝ) ^ 3) <
      Real.pi * pointA ^ 2 * radiusDecay pointA := by
    calc
      (3 : ℝ) / (8 * (100000000 : ℝ) ^ 3) =
          3 * pointA ^ 2 * (1 / (8 * (100000000 : ℝ))) := by norm_num [pointA]
      _ < 3 * pointA ^ 2 * radiusDecay pointA :=
        mul_lt_mul_of_pos_left hd (by norm_num [pointA])
      _ ≤ Real.pi * pointA ^ 2 * radiusDecay pointA :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg pointA)) hdp.le
  have hp : 0 < Real.pi * pointA ^ 2 * radiusDecay pointA :=
    mul_pos (mul_pos Real.pi_pos (sq_pos_of_pos pointA_pos)) hdp
  have hr : radiusEpsilon pointA pointHeight ≤
      (24 * Real.exp (-125)) / ((3 : ℝ) / (8 * (100000000 : ℝ) ^ 3)) := by
    unfold radiusEpsilon
    apply (div_le_div_iff₀ hp (by norm_num)).mpr
    have hn : 24 * Real.exp (-radiusDecay pointA * pointHeight) ≤
        24 * Real.exp (-125) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hn
      (show (0 : ℝ) ≤ 3 / (8 * (100000000 : ℝ) ^ 3) by norm_num)
    have hk := mul_le_mul_of_nonneg_left hden.le
      (show (0 : ℝ) ≤ 24 * Real.exp (-125) by positivity)
    exact hm.trans hk
  have hr' : radiusEpsilon pointA pointHeight ≤
      (64 * (100000000 : ℝ) ^ 3) * Real.exp (-125) := by
    convert hr using 1 <;> norm_num <;> ring
  have ht := mul_lt_mul_of_pos_left exp_neg125_lt
    (show (0 : ℝ) < 64 * (100000000 : ℝ) ^ 3 by norm_num)
  have hb : (64 * (100000000 : ℝ) ^ 3) * Real.exp (-125) <
      64 / (10 : ℝ) ^ 26 := by
    convert ht using 1 <;> norm_num
  exact hr'.trans_lt hb

theorem error_point_le576 : radiusError pointA pointHeight 100000000 ≤
    576 / (10 : ℝ) ^ 10 := by
  have he := epsilon_point_pos.le
  have hu := amplitude_point_le
  have ht := epsilon_point_lt
  have hs : radiusEpsilon pointA pointHeight ≤ (100000000 : ℝ) ^ 2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hu he
  have hq := mul_le_mul_of_nonneg_right hs he
  have hi : 2 * radiusAmplitude pointA * radiusEpsilon pointA pointHeight +
      radiusEpsilon pointA pointHeight ^ 2 ≤
      3 * (100000000 : ℝ) ^ 2 * radiusEpsilon pointA pointHeight := by
    nlinarith [hm, hq]
  have hI : 0 ≤ 2 * radiusAmplitude pointA * radiusEpsilon pointA pointHeight +
      radiusEpsilon pointA pointHeight ^ 2 := by
    unfold radiusAmplitude
    positivity
  have hx : Real.exp (pointA * (100000000 : ℝ)) ≤ 3 := by
    norm_num [pointA]
    exact exp_one_lt3.le
  have hprod := mul_le_mul_of_nonneg_right hx hI
  have hprod' := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 3)
  have hb : radiusError pointA pointHeight 100000000 ≤
      9 * (100000000 : ℝ) ^ 2 * radiusEpsilon pointA pointHeight := by
    unfold radiusError
    nlinarith [hprod, hprod']
  have ht' := mul_le_mul_of_nonneg_left ht.le
    (show (0 : ℝ) ≤ 9 * (100000000 : ℝ) ^ 2 by norm_num)
  calc
    radiusError pointA pointHeight 100000000 ≤
        9 * (100000000 : ℝ) ^ 2 * radiusEpsilon pointA pointHeight := hb
    _ ≤ 9 * (100000000 : ℝ) ^ 2 * (64 / (10 : ℝ) ^ 26) := ht'
    _ = 576 / (10 : ℝ) ^ 10 := by norm_num

theorem tau_gt576 : 576 / (10 : ℝ) ^ 10 < pointTau := by norm_num [pointTau]

theorem error_point_lt_tau : radiusError pointA pointHeight 100000000 < pointTau :=
  error_point_le576.trans_lt tau_gt576

end GoldbachScalarRadius22

#print axioms GoldbachScalarRadius22.pointA
#print axioms GoldbachScalarRadius22.pointHeight
#print axioms GoldbachScalarRadius22.pointTau
#print axioms GoldbachScalarRadius22.radiusAmplitude
#print axioms GoldbachScalarRadius22.radiusDecay
#print axioms GoldbachScalarRadius22.radiusEpsilon
#print axioms GoldbachScalarRadius22.radiusError
#print axioms GoldbachScalarRadius22.atanGap_hasDerivAt
#print axioms GoldbachScalarRadius22.atan_lower_nonneg
#print axioms GoldbachScalarRadius22.amplitude_eq_sinh
#print axioms GoldbachScalarRadius22.amplitude_le_inv_square
#print axioms GoldbachScalarRadius22.pointA_pos
#print axioms GoldbachScalarRadius22.pointHeight_nonneg
#print axioms GoldbachScalarRadius22.decay_point_gt
#print axioms GoldbachScalarRadius22.decay_point_pos
#print axioms GoldbachScalarRadius22.finite_exp_five
#print axioms GoldbachScalarRadius22.exp125_gt
#print axioms GoldbachScalarRadius22.exp_neg125_lt
#print axioms GoldbachScalarRadius22.exp_neg250_eq_square
#print axioms GoldbachScalarRadius22.exp_one_lt3
#print axioms GoldbachScalarRadius22.amplitude_point_le
#print axioms GoldbachScalarRadius22.epsilon_point_pos
#print axioms GoldbachScalarRadius22.epsilon_point_lt
#print axioms GoldbachScalarRadius22.error_point_le576
#print axioms GoldbachScalarRadius22.tau_gt576
#print axioms GoldbachScalarRadius22.error_point_lt_tau
