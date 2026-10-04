import FriableEulerRankin
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals

namespace GoldbachRound20.Friable

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem pseries_partial_le_one_add_inv {sigma : ℝ} (hs : 0 < sigma) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-1 - sigma)) ≤ 1 + sigma⁻¹ := by
  by_cases hN0 : N = 0
  · simp [hN0]
    positivity
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  rw [← Finset.sum_erase_add (Icc 1 N) _ (Finset.left_mem_Icc.mpr hN), add_comm]
  simp only [Nat.cast_one, Real.one_rpow, Finset.Icc_erase_left]
  apply add_le_add_left
  have hanti : AntitoneOn (fun x : ℝ => (x - 1) ^ (-1 - sigma))
      (Set.Icc (2 : ℝ) (N + 1 : ℕ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_exponent_nonpos (by linarith [hx.1])
      (by linarith) (by linarith)
  calc
    (∑ n ∈ Ico 2 (N + 1), (n : ℝ) ^ (-1 - sigma)) =
        ∑ n ∈ Ico 2 (N + 1), ((n + 1 : ℕ) - (1 : ℝ)) ^ (-1 - sigma) := by
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    _ ≤ ∫ x in (2 : ℝ)..(N + 1 : ℕ), (x - 1) ^ (-1 - sigma) :=
      @AntitoneOn.sum_le_integral_Ico 2 (N + 1) _ (by omega) hanti
    _ = ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-1 - sigma) := by
      convert intervalIntegral.integral_comp_sub_right
        (fun x : ℝ => x ^ (-1 - sigma)) 1 using 1 <;> norm_num
    _ = ((N : ℝ) ^ (-sigma) - 1) / (-sigma) := by
      rw [integral_rpow]
      · congr 1 <;> ring_nf <;> simp <;> ring
      · right
        refine ⟨by linarith, ?_⟩
        rw [Set.uIcc_of_le (by exact_mod_cast hN)]
        simp
    _ ≤ sigma⁻¹ := by
      have hp : 0 ≤ (N : ℝ) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      apply (div_le_iff_of_neg (show -sigma < 0 by linarith)).mpr
      field_simp
      nlinarith

theorem pseries_tsum_le_one_add_inv {sigma : ℝ} (hs : 0 < sigma) :
    (∑' n : ℕ, (n : ℝ) ^ (-1 - sigma)) ≤ 1 + sigma⁻¹ := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - sigma)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply tsum_le_of_sum_range_le hsum
  intro N
  by_cases hN : N = 0
  · simp [hN]
    positivity
  have he : range N = insert 0 (Icc 1 (N - 1)) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [he, sum_insert (by simp)]
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : (-1 - sigma) ≠ 0), zero_add]
  exact pseries_partial_le_one_add_inv hs (N - 1)

theorem actual_euler_minus_le_pseries {sigma : ℝ} (hs : 0 < sigma) (Y : ℕ) :
    eulerProduct Y (-1 - sigma) ≤ 1 + sigma⁻¹ := by
  have hh := actual_smooth_rpow_hasSum Y (show -1 - sigma < 0 by linarith)
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - sigma)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hle := hasSum_le_inj (fun n : Nat.smoothNumbers (Y + 1) => n.val)
    Subtype.val_injective
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-1 - sigma))
    (fun _ => le_rfl) hh hg.hasSum
  exact hle.trans (pseries_tsum_le_one_add_inv hs)

theorem eulerProduct_pos (Y : ℕ) {s : ℝ} (hs : s < 0) :
    0 < eulerProduct Y s := by
  unfold eulerProduct
  apply Finset.prod_pos
  intro p hp
  apply inv_pos.mpr
  have hh := prime_rpow_norm_lt_one (Nat.prime_of_mem_primesBelow hp) hs
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) s)] at hh
  linarith

theorem log_eulerProduct (Y : ℕ) {s : ℝ} (hs : s < 0) :
    Real.log (eulerProduct Y s) =
      ∑ p ∈ Nat.primesBelow (Y + 1), -Real.log (1 - (p : ℝ) ^ s) := by
  unfold eulerProduct
  rw [Real.log_prod]
  · simp only [Real.log_inv]
  · intro p hp
    apply inv_ne_zero
    have hh := prime_rpow_norm_lt_one (Nat.prime_of_mem_primesBelow hp) hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) s)] at hh
    linarith

theorem prime_rpow_sigma_le_three {Y p : ℕ} (hp : p.Prime) (hpY : p ≤ Y)
    {sigma : ℝ} (hs : 0 ≤ sigma) (hscale : Real.log (Y : ℝ) * sigma ≤ 1) :
    (p : ℝ) ^ sigma ≤ 3 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog := Real.log_le_log hpR (show (p : ℝ) ≤ (Y : ℝ) by exact_mod_cast hpY)
  rw [Real.rpow_def_of_pos hpR]
  calc
    Real.exp (Real.log (p : ℝ) * sigma) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hlog hs).trans hscale)
    _ ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)

theorem prime_reciprocal_le_three_euler_minus_term {Y p : ℕ}
    (hp : p.Prime) (hpY : p ≤ Y) {sigma : ℝ} (hs : 0 ≤ sigma)
    (hscale : Real.log (Y : ℝ) * sigma ≤ 1) :
    (p : ℝ)⁻¹ ≤ 3 * (p : ℝ) ^ (-1 - sigma) := by
  have he : (p : ℝ) ^ sigma * (p : ℝ) ^ (-1 - sigma) = (p : ℝ)⁻¹ := by
    rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
    convert Real.rpow_neg_one (p : ℝ) using 1 <;> ring
  rw [← he]
  exact mul_le_mul_of_nonneg_right (prime_rpow_sigma_le_three hp hpY hs hscale)
    (Real.rpow_nonneg (Nat.cast_nonneg p) _)

theorem prime_harmonic_le_three_log_one_add_inv {Y : ℕ} {sigma : ℝ}
    (hs : 0 < sigma) (hscale : Real.log (Y : ℝ) * sigma ≤ 1) :
    (∑ p ∈ Nat.primesBelow (Y + 1), (p : ℝ)⁻¹) ≤
      3 * Real.log (1 + sigma⁻¹) := by
  have hlog : (∑ p ∈ Nat.primesBelow (Y + 1), (p : ℝ) ^ (-1 - sigma)) ≤
      Real.log (eulerProduct Y (-1 - sigma)) := by
    rw [log_eulerProduct Y (by linarith)]
    apply Finset.sum_le_sum
    intro p hp
    have hr := prime_rpow_norm_lt_one (Nat.prime_of_mem_primesBelow hp)
      (show -1 - sigma < 0 by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)] at hr
    have hb := Real.log_le_sub_one_of_pos (show 0 < 1 - (p : ℝ) ^ (-1 - sigma) by linarith)
    linarith
  calc
    _ ≤ ∑ p ∈ Nat.primesBelow (Y + 1), 3 * (p : ℝ) ^ (-1 - sigma) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpY : p ≤ Y := by have := Nat.lt_of_mem_primesBelow hp; omega
      exact prime_reciprocal_le_three_euler_minus_term
        (Nat.prime_of_mem_primesBelow hp) hpY hs.le hscale
    _ = 3 * ∑ p ∈ Nat.primesBelow (Y + 1), (p : ℝ) ^ (-1 - sigma) := by rw [Finset.mul_sum]
    _ ≤ 3 * Real.log (eulerProduct Y (-1 - sigma)) := by gcongr
    _ ≤ 3 * Real.log (1 + sigma⁻¹) := by
      apply mul_le_mul_of_nonneg_left
        (Real.log_le_log (eulerProduct_pos Y (by linarith))
          (actual_euler_minus_le_pseries hs Y)) (by norm_num)

theorem prime_plus_term_le_two_thirds {p : ℕ} (hp : p.Prime)
    {sigma : ℝ} (hs : sigma ≤ (1 : ℝ) / 4) :
    (p : ℝ) ^ (sigma - 1) ≤ (2 : ℝ) / 3 := by
  have htwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hh : (p : ℝ) ^ (sigma - 1) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
    calc
      _ ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_nonpos (by norm_num) htwo (by norm_num)
  have hpow : ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 4 = (1 : ℝ) / 8 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hbound : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (2 : ℝ) / 3 := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [hpow]
    norm_num
  exact hh.trans hbound

theorem neg_log_one_sub_le_three_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (2 : ℝ) / 3) :
    -Real.log (1 - t) ≤ 3 * t := by
  have hp : 0 < 1 - t := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have hid : (1 - t)⁻¹ - 1 = t * (1 - t)⁻¹ := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left (show (1 - t)⁻¹ ≤ 3 by
    apply (inv_le_iff_one_le_mul₀ hp).mpr; linarith) ht0
  rw [← hid] at hmul
  linarith

theorem log_euler_plus_le_nine_prime_harmonic {Y : ℕ} {sigma : ℝ}
    (hs0 : 0 ≤ sigma) (hs1 : sigma ≤ (1 : ℝ) / 4)
    (hscale : Real.log (Y : ℝ) * sigma ≤ 1) :
    Real.log (eulerProduct Y (sigma - 1)) ≤
      9 * ∑ p ∈ Nat.primesBelow (Y + 1), (p : ℝ)⁻¹ := by
  rw [log_eulerProduct Y (by linarith), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hpY : p ≤ Y := by have := Nat.lt_of_mem_primesBelow hp; omega
  have hsmall := prime_plus_term_le_two_thirds hprime hs1
  have hbound := neg_log_one_sub_le_three_mul
    (Real.rpow_nonneg (Nat.cast_nonneg p) _) hsmall
  have hprod : (p : ℝ) ^ (sigma - 1) = (p : ℝ) ^ sigma * (p : ℝ)⁻¹ := by
    rw [Real.rpow_sub (by exact_mod_cast hprime.pos), Real.rpow_one, div_eq_mul_inv]
  have hterm : (p : ℝ) ^ (sigma - 1) ≤ 3 * (p : ℝ)⁻¹ := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (prime_rpow_sigma_le_three hprime hpY hs0 hscale)
      (by positivity)
  linarith

/-- The Euler power is derived from the p-series and logarithmic scale guards. -/
theorem actual_euler_plus_le_u_pow_27 {Y : ℕ} {u : ℝ}
    (hu : 0 < u) (hY : 4 ≤ Real.log (Y : ℝ))
    (hYu : 1 + Real.log (Y : ℝ) ≤ u) :
    eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1) ≤ u ^ 27 := by
  have hlog : 0 < Real.log (Y : ℝ) := by linarith
  have hs : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlog
  have hs1 : (Real.log (Y : ℝ))⁻¹ ≤ (1 : ℝ) / 4 := by
    apply (inv_le_iff_one_le_mul₀ hlog).mpr
    linarith
  have hscale : Real.log (Y : ℝ) * (Real.log (Y : ℝ))⁻¹ ≤ 1 := by
    rw [mul_inv_cancel₀ hlog.ne']
  have hp := prime_harmonic_le_three_log_one_add_inv hs hscale
  simp only [inv_inv] at hp
  have hp' : (∑ p ∈ Nat.primesBelow (Y + 1), (p : ℝ)⁻¹) ≤ 3 * Real.log u := by
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) hYu) (by norm_num))
  have he := log_euler_plus_le_nine_prime_harmonic hs.le hs1 hscale
  have hfinal : Real.log (eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1)) ≤ 27 * Real.log u := by
    linarith
  calc
    _ = Real.exp (Real.log (eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1))) :=
      (Real.exp_log (eulerProduct_pos Y (by linarith))).symm
    _ ≤ Real.exp (27 * Real.log u) := Real.exp_le_exp.mpr hfinal
    _ = u ^ 27 := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hu]
      congr 1
      ring

theorem actual_rankin_D_le_u_neg64 {D Y : ℕ} {u : ℝ}
    (hD : 0 < D) (hu : 0 < u) (hY : 0 < Real.log (Y : ℝ))
    (hDlog : u / 2 ≤ Real.log (D : ℝ))
    (hscale : 128 * Real.log u * Real.log (Y : ℝ) ≤ u) :
    (D : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) ≤ u ^ (-64 : ℝ) := by
  have hh : 64 * Real.log u ≤ Real.log (D : ℝ) / Real.log (Y : ℝ) := by
    apply (le_div_iff₀ hY).mpr
    linarith
  rw [Real.rpow_def_of_pos (by exact_mod_cast hD), Real.rpow_def_of_pos hu]
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hh
  nlinarith

/-- No small inverse mass is assumed: both Rankin and Euler factors are derived. -/
theorem actual_divisor_band_mass_le_u_neg37 {D Y : ℕ} {u : ℝ}
    (hD : 0 < D) (hu : 0 < u) (hY : 4 ≤ Real.log (Y : ℝ))
    (hYu : 1 + Real.log (Y : ℝ) ≤ u)
    (hDlog : u / 2 ≤ Real.log (D : ℝ))
    (hscale : 128 * Real.log u * Real.log (Y : ℝ) ≤ u) :
    (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) ≤ u ^ (-37 : ℝ) := by
  have hlog : 0 < Real.log (Y : ℝ) := by linarith
  have hs0 : 0 ≤ (Real.log (Y : ℝ))⁻¹ := (inv_pos.mpr hlog).le
  have hs1 : (Real.log (Y : ℝ))⁻¹ < 1 := by
    apply (inv_lt_one₀ hlog).mpr
    linarith
  have he := actual_euler_plus_le_u_pow_27 hu hY hYu
  have hd := actual_rankin_D_le_u_neg64 hD hu hlog hDlog hscale
  calc
    _ ≤ (D : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) *
        eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1) := actual_divisor_inverse_tail hD hs0 hs1
    _ ≤ u ^ (-64 : ℝ) * u ^ 27 :=
      mul_le_mul hd he (le_of_lt (eulerProduct_pos Y (by linarith)))
        (Real.rpow_nonneg hu.le _)
    _ = u ^ (-37 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu]
      norm_num

theorem actual_rankin_M_le_u_neg96 {M Y : ℕ} {u : ℝ}
    (hM : 0 < M) (hu : 0 < u) (hY : 0 < Real.log (Y : ℝ))
    (hMlog : 3 * u / 4 ≤ Real.log (M : ℝ))
    (hscale : 128 * Real.log u * Real.log (Y : ℝ) ≤ u) :
    (M : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) ≤ u ^ (-96 : ℝ) := by
  have hh : 96 * Real.log u ≤ Real.log (M : ℝ) / Real.log (Y : ℝ) := by
    apply (le_div_iff₀ hY).mpr
    linarith
  rw [Real.rpow_def_of_pos (by exact_mod_cast hM), Real.rpow_def_of_pos hu]
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hh
  nlinarith

/-- The actual tau tail is quantitatively paid under independent scale guards. -/
theorem actual_smooth_tau_tail_le_N_u_neg42 {M N Y : ℕ} {u : ℝ}
    (hM : 0 < M) (hu : 0 < u) (hY : 4 ≤ Real.log (Y : ℝ))
    (hYu : 1 + Real.log (Y : ℝ) ≤ u)
    (hMlog : 3 * u / 4 ≤ Real.log (M : ℝ))
    (hscale : 128 * Real.log u * Real.log (Y : ℝ) ≤ u) :
    (∑ n ∈ smoothInterval M N Y, tau n) ≤ (N : ℝ) * u ^ (-42 : ℝ) := by
  have hlog : 0 < Real.log (Y : ℝ) := by linarith
  have hs0 : 0 ≤ (Real.log (Y : ℝ))⁻¹ := (inv_pos.mpr hlog).le
  have hs1 : (Real.log (Y : ℝ))⁻¹ < 1 := by
    apply (inv_lt_one₀ hlog).mpr
    linarith
  have he := actual_euler_plus_le_u_pow_27 hu hY hYu
  have he0 := (eulerProduct_pos Y (show (Real.log (Y : ℝ))⁻¹ - 1 < 0 by linarith)).le
  have he2 : eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1) ^ 2 ≤ u ^ 54 := by
    calc
      _ = eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1) *
          eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1) := by ring
      _ ≤ u ^ 27 * u ^ 27 := mul_le_mul he he he0 (pow_nonneg hu.le _)
      _ = u ^ 54 := by rw [← pow_add]
  have hm := actual_rankin_M_le_u_neg96 hM hu hlog hMlog hscale
  calc
    _ ≤ (N : ℝ) * (M : ℝ) ^ (-(Real.log (Y : ℝ))⁻¹) *
        eulerProduct Y ((Real.log (Y : ℝ))⁻¹ - 1) ^ 2 := actual_smooth_tau_tail hM hs0 hs1
    _ ≤ (N : ℝ) * u ^ (-96 : ℝ) * u ^ 54 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg N)) he2
        (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hu.le _))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hu]
      norm_num

#print axioms pseries_partial_le_one_add_inv
#print axioms pseries_tsum_le_one_add_inv
#print axioms actual_euler_minus_le_pseries
#print axioms eulerProduct_pos
#print axioms log_eulerProduct
#print axioms prime_rpow_sigma_le_three
#print axioms prime_reciprocal_le_three_euler_minus_term
#print axioms prime_harmonic_le_three_log_one_add_inv
#print axioms prime_plus_term_le_two_thirds
#print axioms neg_log_one_sub_le_three_mul
#print axioms log_euler_plus_le_nine_prime_harmonic
#print axioms actual_euler_plus_le_u_pow_27
#print axioms actual_rankin_D_le_u_neg64
#print axioms actual_divisor_band_mass_le_u_neg37
#print axioms actual_rankin_M_le_u_neg96
#print axioms actual_smooth_tau_tail_le_N_u_neg42

end
end GoldbachRound20.Friable
