import FriablePhysicalPrefix
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GoldbachRound20.Friable

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def rpowNatHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' m n := by
    change ((m * n : ℕ) : ℝ) ^ s = (m : ℝ) ^ s * (n : ℝ) ^ s
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

def eulerProduct (Y : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesBelow (Y + 1), (1 - (p : ℝ) ^ s)⁻¹

def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

theorem tau_nonneg (n : ℕ) : 0 ≤ tau n := by
  exact Nat.cast_nonneg _

theorem tau_mul {m n : ℕ} (h : m.Coprime n) :
    tau (m * n) = tau m * tau n := by
  unfold tau
  rw [h.card_divisors_mul, Nat.cast_mul]

theorem tau_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tau (p ^ k) = (k : ℝ) + 1 := by
  unfold tau
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  norm_cast

theorem nat_pow_rpow (p k : ℕ) (s : ℝ) :
    ((p ^ k : ℕ) : ℝ) ^ s = ((p : ℝ) ^ s) ^ k := by
  rw [Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]

theorem prime_rpow_norm_lt_one {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : s < 0) : ‖(p : ℝ) ^ s‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) s)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) hs

/-- Only the finite-prime support is summed. No global zeta summability at s>-1. -/
theorem actual_smooth_rpow_hasSum (Y : ℕ) {s : ℝ} (hs : s < 0) :
    HasSum (fun n : Nat.smoothNumbers (Y + 1) => (n.val : ℝ) ^ s)
      (eulerProduct Y s) := by
  exact (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rpowNatHom s) (fun hp => prime_rpow_norm_lt_one hp hs) (Y + 1)).2

theorem actual_smooth_rpow_summable (Y : ℕ) {s : ℝ} (hs : s < 0) :
    Summable (fun n : Nat.smoothNumbers (Y + 1) => (n.val : ℝ) ^ s) :=
  (actual_smooth_rpow_hasSum Y hs).summable

theorem local_tau_geometric_hasSum {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : s < 0) :
    HasSum (fun k : ℕ => tau (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ s)
      ((1 - (p : ℝ) ^ s)⁻¹ ^ 2) := by
  have hh := hasSum_choose_mul_geometric_of_norm_lt_one 1
    (prime_rpow_norm_lt_one hp hs)
  convert hh using 1
  · ext k
    simp only [tau_prime_pow hp, nat_pow_rpow, Nat.choose_one_right,
      Nat.cast_add, Nat.cast_one]
  · simp only [one_add_one_eq_two, one_div, inv_pow]

/-- The actual divisor cardinal, including repeated prime factors. -/
theorem actual_smooth_tau_rpow_hasSum (Y : ℕ) {s : ℝ} (hs : s < 0) :
    HasSum (fun n : Nat.smoothNumbers (Y + 1) => tau n.val * (n.val : ℝ) ^ s)
      (eulerProduct Y s ^ 2) := by
  let f : ℕ → ℝ := fun n => tau n * (n : ℝ) ^ s
  have hf : f 1 = 1 := by simp [f, tau]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, tau_mul h, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hl {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖f (p ^ k)‖) := by
    have hh := (local_tau_geometric_hasSum hp hs).summable
    convert hh using 1
    ext k
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (tau_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) s)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf hm hl
      (Y + 1)).2
  convert hsum using 1
  unfold eulerProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  exact (local_tau_geometric_hasSum (Nat.prime_of_mem_primesBelow hp) hs).tsum_eq.symm

theorem finite_smooth_rpow_sum_le (Y : ℕ) {s : ℝ} (hs : s < 0)
    (S : Finset ℕ) (hS : ∀ n ∈ S, Smooth Y n) :
    (∑ n ∈ S, (n : ℝ) ^ s) ≤ eulerProduct Y s := by
  have hh := sum_le_hasSum (S.subtype (Smooth Y))
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n.val) s)
    (actual_smooth_rpow_hasSum Y hs)
  rw [Finset.sum_subtype_of_mem (fun n : ℕ => (n : ℝ) ^ s) hS] at hh
  exact hh

theorem finite_smooth_tau_rpow_sum_le (Y : ℕ) {s : ℝ} (hs : s < 0)
    (S : Finset ℕ) (hS : ∀ n ∈ S, Smooth Y n) :
    (∑ n ∈ S, tau n * (n : ℝ) ^ s) ≤ eulerProduct Y s ^ 2 := by
  have hh := sum_le_hasSum (S.subtype (Smooth Y))
    (fun n _ => mul_nonneg (tau_nonneg n.val)
      (Real.rpow_nonneg (Nat.cast_nonneg n.val) s))
    (actual_smooth_tau_rpow_hasSum Y hs)
  rw [Finset.sum_subtype_of_mem (fun n : ℕ => tau n * (n : ℝ) ^ s) hS] at hh
  exact hh

theorem rankin_inverse_term {D n : ℕ} (hD : 0 < D) (hDn : D ≤ n)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    (n : ℝ)⁻¹ ≤ (D : ℝ) ^ (-sigma) * (n : ℝ) ^ (sigma - 1) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (hD.trans_le hDn)
  have hp := Real.rpow_le_rpow_of_exponent_nonpos
    (show 0 < (D : ℝ) by exact_mod_cast hD)
    (show (D : ℝ) ≤ (n : ℝ) by exact_mod_cast hDn) (neg_nonpos.mpr hsigma)
  have he : (n : ℝ) ^ (-sigma) * (n : ℝ) ^ (sigma - 1) = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_add hn]
    convert Real.rpow_neg_one (n : ℝ) using 1 <;> ring
  rw [← he]
  exact mul_le_mul_of_nonneg_right hp
    (Real.rpow_nonneg (Nat.cast_nonneg n) (sigma - 1))

/-- An actual finite divisor-band mass, with its Euler bound derived. -/
theorem actual_divisor_inverse_tail {D Y : ℕ} (hD : 0 < D)
    {sigma : ℝ} (hs0 : 0 ≤ sigma) (hs1 : sigma < 1) :
    (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) ≤
      (D : ℝ) ^ (-sigma) * eulerProduct Y (sigma - 1) := by
  calc
    (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) ≤
        ∑ d ∈ divisorBand D Y, (D : ℝ) ^ (-sigma) * (d : ℝ) ^ (sigma - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      exact rankin_inverse_term hD (mem_Icc.mp (mem_filter.mp hd).1).1 hs0
    _ = (D : ℝ) ^ (-sigma) * ∑ d ∈ divisorBand D Y, (d : ℝ) ^ (sigma - 1) := by
      rw [Finset.mul_sum]
    _ ≤ (D : ℝ) ^ (-sigma) * eulerProduct Y (sigma - 1) := by
      apply mul_le_mul_of_nonneg_left
        (finite_smooth_rpow_sum_le Y (by linarith) (divisorBand D Y)
          (fun d hd => (mem_filter.mp hd).2))
      exact Real.rpow_nonneg (Nat.cast_nonneg D) _

theorem actual_divisor_band_card_le_mass (D Y : ℕ) :
    ((divisorBand D Y).card : ℝ) ≤
      (D * Y : ℕ) * ∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹ := by
  have hterm : ∀ d ∈ divisorBand D Y, (1 : ℝ) ≤ (D * Y : ℕ) * (d : ℝ)⁻¹ := by
    intro d hd
    have hs := (mem_filter.mp hd).2
    have hp : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs.1
    have hb : (d : ℝ) ≤ (D * Y : ℕ) := by
      exact_mod_cast (mem_Icc.mp (mem_filter.mp hd).1).2
    exact (one_le_div hp).mpr hb
  calc
    ((divisorBand D Y).card : ℝ) = ∑ d ∈ divisorBand D Y, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ divisorBand D Y, (D * Y : ℕ) * (d : ℝ)⁻¹ :=
      Finset.sum_le_sum hterm
    _ = (D * Y : ℕ) * ∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹ := by rw [Finset.mul_sum]

def smoothInterval (M N Y : ℕ) : Finset ℕ := (Icc M N).filter (Smooth Y)

theorem actual_tau_rankin_term {M n N : ℕ} (hM : 0 < M) (hMn : M ≤ n)
    (hnN : n ≤ N) {sigma : ℝ} (hs : 0 ≤ sigma) :
    tau n ≤ (N : ℝ) * (M : ℝ) ^ (-sigma) * (tau n * (n : ℝ) ^ (sigma - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hM.trans_le hMn))
  have hi := rankin_inverse_term hM hMn hs
  calc
    tau n = (n : ℝ) * (tau n * (n : ℝ)⁻¹) := by
      field_simp [hn0]
    _ ≤ (n : ℝ) * (tau n * ((M : ℝ) ^ (-sigma) * (n : ℝ) ^ (sigma - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (tau_nonneg n))
        (Nat.cast_nonneg n)
    _ ≤ (N : ℝ) * (tau n * ((M : ℝ) ^ (-sigma) * (n : ℝ) ^ (sigma - 1))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hnN)
        (mul_nonneg (tau_nonneg n) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg M) _)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    _ = _ := by ring

theorem actual_smooth_tau_tail {M N Y : ℕ} (hM : 0 < M)
    {sigma : ℝ} (hs0 : 0 ≤ sigma) (hs1 : sigma < 1) :
    (∑ n ∈ smoothInterval M N Y, tau n) ≤
      (N : ℝ) * (M : ℝ) ^ (-sigma) * eulerProduct Y (sigma - 1) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ smoothInterval M N Y,
        (N : ℝ) * (M : ℝ) ^ (-sigma) * (tau n * (n : ℝ) ^ (sigma - 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := mem_Icc.mp (mem_filter.mp hn).1
      exact actual_tau_rankin_term hM hh.1 hh.2 hs0
    _ = (N : ℝ) * (M : ℝ) ^ (-sigma) *
        ∑ n ∈ smoothInterval M N Y, tau n * (n : ℝ) ^ (sigma - 1) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (M : ℝ) ^ (-sigma) * eulerProduct Y (sigma - 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (finite_smooth_tau_rpow_sum_le Y (by linarith) (smoothInterval M N Y)
          (fun n hn => (mem_filter.mp hn).2))
        (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Nat.cast_nonneg M) _))

#print axioms rpowNatHom
#print axioms eulerProduct
#print axioms tau
#print axioms tau_nonneg
#print axioms tau_mul
#print axioms tau_prime_pow
#print axioms nat_pow_rpow
#print axioms prime_rpow_norm_lt_one
#print axioms actual_smooth_rpow_hasSum
#print axioms actual_smooth_rpow_summable
#print axioms local_tau_geometric_hasSum
#print axioms actual_smooth_tau_rpow_hasSum
#print axioms finite_smooth_rpow_sum_le
#print axioms finite_smooth_tau_rpow_sum_le
#print axioms rankin_inverse_term
#print axioms actual_divisor_inverse_tail
#print axioms actual_divisor_band_card_le_mass
#print axioms smoothInterval
#print axioms actual_tau_rankin_term
#print axioms actual_smooth_tau_tail

end
end GoldbachRound20.Friable
