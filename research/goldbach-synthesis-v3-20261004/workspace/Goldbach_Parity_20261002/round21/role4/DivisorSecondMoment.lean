import FriableSourceBudget
import Mathlib.NumberTheory.Harmonic.Bounds

namespace GoldbachRound21.NonfriableReciprocal

open Finset GoldbachRound20.Friable
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

def quadProduct (v : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  v.1.1 * v.1.2 * v.2.1 * v.2.2

def quadAmbient (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Icc 1 N).product (Icc 1 N)).product ((Icc 1 N).product (Icc 1 N))

def factorQuadDomain (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (quadAmbient n).filter fun v => quadProduct v = n

def fourDivisorCount (n : ℕ) : ℕ := (factorQuadDomain n).card

def quadBelow (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (quadAmbient N).filter fun v => quadProduct v ≤ N

theorem mem_quadAmbient {N : ℕ} {v : (ℕ × ℕ) × (ℕ × ℕ)} :
    v ∈ quadAmbient N ↔
      (1 ≤ v.1.1 ∧ v.1.1 ≤ N) ∧ (1 ≤ v.1.2 ∧ v.1.2 ≤ N) ∧
      (1 ≤ v.2.1 ∧ v.2.1 ≤ N) ∧ (1 ≤ v.2.2 ∧ v.2.2 ≤ N) := by
  simp only [quadAmbient, mem_product, mem_Icc]
  tauto

theorem positive_quad_factor_bounds {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a ≤ a * b * c * d ∧ b ≤ a * b * c * d ∧
      c ≤ a * b * c * d ∧ d ≤ a * b * c * d := by
  have h1 : 1 ≤ b * c * d := by positivity
  have h2 : 1 ≤ a * c * d := by positivity
  have h3 : 1 ≤ a * b * d := by positivity
  have h4 : 1 ≤ a * b * c := by positivity
  constructor
  · calc
      a = a * 1 := by omega
      _ ≤ a * (b * c * d) := Nat.mul_le_mul_left a h1
      _ = _ := by ring
  constructor
  · calc
      b = b * 1 := by omega
      _ ≤ b * (a * c * d) := Nat.mul_le_mul_left b h2
      _ = _ := by ring
  constructor
  · calc
      c = c * 1 := by omega
      _ ≤ c * (a * b * d) := Nat.mul_le_mul_left c h3
      _ = _ := by ring
  · calc
      d = d * 1 := by omega
      _ ≤ d * (a * b * c) := Nat.mul_le_mul_left d h4
      _ = _ := by ring

def divisorPairToQuad (n : ℕ) (v : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((Nat.gcd v.1 v.2, v.1 / Nat.gcd v.1 v.2),
    (v.2 / Nat.gcd v.1 v.2, n / Nat.lcm v.1 v.2))

theorem divisorPairToQuad_reconstruct {n : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ n.divisors.product n.divisors) :
    (divisorPairToQuad n v).1.1 * (divisorPairToQuad n v).1.2 = v.1 ∧
      (divisorPairToQuad n v).1.1 * (divisorPairToQuad n v).2.1 = v.2 := by
  constructor
  · simpa only [divisorPairToQuad, Nat.mul_comm] using
      Nat.div_mul_cancel (Nat.gcd_dvd_left v.1 v.2)
  · simpa only [divisorPairToQuad, Nat.mul_comm] using
      Nat.div_mul_cancel (Nat.gcd_dvd_right v.1 v.2)

theorem divisorPairToQuad_mem {n : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ n.divisors.product n.divisors) :
    divisorPairToQuad n v ∈ factorQuadDomain n := by
  obtain ⟨hr, hs⟩ := mem_product.mp hv
  have hrp := Nat.pos_of_mem_divisors hr
  have hsp := Nat.pos_of_mem_divisors hs
  have hrn := Nat.divisor_le hr
  have hsn := Nat.divisor_le hs
  have hn : 0 < n := lt_of_lt_of_le hrp hrn
  have hg : 0 < Nat.gcd v.1 v.2 := Nat.gcd_pos_of_pos_left v.2 hrp
  have hgr : Nat.gcd v.1 v.2 ≤ v.1 := Nat.le_of_dvd hrp (Nat.gcd_dvd_left _ _)
  have hgs : Nat.gcd v.1 v.2 ≤ v.2 := Nat.le_of_dvd hsp (Nat.gcd_dvd_right _ _)
  have hx : 0 < v.1 / Nat.gcd v.1 v.2 := Nat.div_pos hgr hg
  have hy : 0 < v.2 / Nat.gcd v.1 v.2 := Nat.div_pos hgs hg
  have hld : Nat.lcm v.1 v.2 ∣ n :=
    Nat.lcm_dvd (Nat.dvd_of_mem_divisors hr) (Nat.dvd_of_mem_divisors hs)
  have hl : 0 < Nat.lcm v.1 v.2 := Nat.lcm_pos hrp hsp
  have hz : 0 < n / Nat.lcm v.1 v.2 := Nat.div_pos (Nat.le_of_dvd hn hld) hl
  have hrec := divisorPairToQuad_reconstruct hv
  have hgxy : Nat.gcd v.1 v.2 * (v.1 / Nat.gcd v.1 v.2) *
      (v.2 / Nat.gcd v.1 v.2) = Nat.lcm v.1 v.2 := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      _ = (Nat.gcd v.1 v.2 * (v.1 / Nat.gcd v.1 v.2)) *
        (Nat.gcd v.1 v.2 * (v.2 / Nat.gcd v.1 v.2)) := by ring
      _ = v.1 * v.2 := by simpa only [divisorPairToQuad] using congrArg₂ Nat.mul hrec.1 hrec.2
      _ = _ := (Nat.gcd_mul_lcm v.1 v.2).symm
  apply mem_filter.mpr
  constructor
  · apply mem_quadAmbient.mpr
    exact ⟨⟨hg, hgr.trans hrn⟩,
      ⟨hx, (Nat.div_le_self _ _).trans hrn⟩,
      ⟨hy, (Nat.div_le_self _ _).trans hsn⟩,
      ⟨hz, Nat.div_le_self _ _⟩⟩
  · change Nat.gcd v.1 v.2 * (v.1 / Nat.gcd v.1 v.2) *
        (v.2 / Nat.gcd v.1 v.2) * (n / Nat.lcm v.1 v.2) = n
    rw [hgxy]
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hld

theorem divisorPairToQuad_injective (n : ℕ) :
    Set.InjOn (divisorPairToQuad n) (n.divisors.product n.divisors) := by
  intro v hv w hw heq
  have hvrec := divisorPairToQuad_reconstruct hv
  have hwrec := divisorPairToQuad_reconstruct hw
  apply Prod.ext
  · calc
      v.1 = (divisorPairToQuad n v).1.1 * (divisorPairToQuad n v).1.2 := hvrec.1.symm
      _ = (divisorPairToQuad n w).1.1 * (divisorPairToQuad n w).1.2 := by rw [heq]
      _ = w.1 := hwrec.1
  · calc
      v.2 = (divisorPairToQuad n v).1.1 * (divisorPairToQuad n v).2.1 := hvrec.2.symm
      _ = (divisorPairToQuad n w).1.1 * (divisorPairToQuad n w).2.1 := by rw [heq]
      _ = w.2 := hwrec.2

theorem actual_tau_square_le_fourDivisorCount (n : ℕ) :
    tau n ^ 2 ≤ (fourDivisorCount n : ℝ) := by
  have hc : n.divisors.card ^ 2 ≤ (factorQuadDomain n).card := by
    simpa only [card_product, pow_two] using
      Finset.card_le_card_of_injOn (divisorPairToQuad n)
        (fun v hv => divisorPairToQuad_mem hv) (divisorPairToQuad_injective n)
  unfold tau fourDivisorCount
  exact_mod_cast hc

theorem factorQuadDomain_eq_ambient_filter {n N : ℕ} (hn : n ≤ N) :
    factorQuadDomain n = (quadAmbient N).filter (fun v => quadProduct v = n) := by
  ext v
  simp only [factorQuadDomain, mem_filter]
  constructor
  · rintro ⟨hv, he⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_quadAmbient.mp hv
    exact ⟨mem_quadAmbient.mpr ⟨⟨h1.1, h1.2.trans hn⟩, ⟨h2.1, h2.2.trans hn⟩,
      ⟨h3.1, h3.2.trans hn⟩, ⟨h4.1, h4.2.trans hn⟩⟩, he⟩
  · rintro ⟨hv, he⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_quadAmbient.mp hv
    have hb := positive_quad_factor_bounds h1.1 h2.1 h3.1 h4.1
    change v.1.1 * v.1.2 * v.2.1 * v.2.2 = n at he
    rw [he] at hb
    exact ⟨mem_quadAmbient.mpr ⟨⟨h1.1, hb.1⟩, ⟨h2.1, hb.2.1⟩,
      ⟨h3.1, hb.2.2.1⟩, ⟨h4.1, hb.2.2.2⟩⟩, he⟩

theorem sum_fourDivisorCount_eq_quadBelow (N : ℕ) :
    (∑ n ∈ Icc 1 N, fourDivisorCount n) = (quadBelow N).card := by
  have he : (∑ n ∈ Icc 1 N, fourDivisorCount n) =
      ∑ n ∈ Icc 1 N, ((quadAmbient N).filter (fun v => quadProduct v = n)).card := by
    apply sum_congr rfl
    intro n hn
    unfold fourDivisorCount
    rw [factorQuadDomain_eq_ambient_filter (mem_Icc.mp hn).2]
  rw [he, Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext v
  simp only [quadBelow, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hv, _, hN⟩
    exact ⟨hv, hN⟩
  · rintro ⟨hv, hN⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_quadAmbient.mp hv
    have hp : 0 < quadProduct v := by unfold quadProduct; positivity
    exact ⟨hv, hp, hN⟩

theorem positive_product_front_count {N a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((Icc 1 N).filter (fun d => a * b * c * d ≤ N)).card = N / (a * b * c) := by
  have habc : 0 < a * b * c := by positivity
  have he : (Icc 1 N).filter (fun d => a * b * c * d ≤ N) =
      Icc 1 (N / (a * b * c)) := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hp⟩
      exact ⟨hd, (Nat.le_div_iff_mul_le habc).mpr (by simpa only [mul_comm] using hp)⟩
    · rintro ⟨hd, hbnd⟩
      exact ⟨⟨hd, hbnd.trans (Nat.div_le_self _ _)⟩,
        by simpa only [mul_comm] using (Nat.le_div_iff_mul_le habc).mp hbnd⟩
  rw [he]
  simp

theorem quadBelow_card_eq_sum_div (N : ℕ) :
    (quadBelow N).card = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
      N / (a * b * c) := by
  unfold quadBelow quadAmbient
  rw [Finset.card_filter]
  simp only [Finset.sum_product, quadProduct]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro c hc
  rw [← Finset.card_filter]
  exact positive_product_front_count (mem_Icc.mp ha).1 (mem_Icc.mp hb).1 (mem_Icc.mp hc).1

theorem triple_reciprocal_sum_harmonic (N : ℕ) :
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
      (N : ℝ) / ((a * b * c : ℕ) : ℝ)) = (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  symm
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    pow_succ, pow_zero, mul_one, Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro c hc
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem actual_four_divisor_sum_le_harmonic_cube (N : ℕ) :
    (∑ n ∈ Icc 1 N, (fourDivisorCount n : ℝ)) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  have he : (∑ n ∈ Icc 1 N, (fourDivisorCount n : ℝ)) = ((quadBelow N).card : ℝ) := by
    exact_mod_cast sum_fourDivisorCount_eq_quadBelow N
  rw [he, quadBelow_card_eq_sum_div, Nat.cast_sum]
  simp only [Nat.cast_sum]
  calc
    _ ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N,
        (N : ℝ) / ((a * b * c : ℕ) : ℝ) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      apply sum_le_sum
      intro c hc
      exact Nat.cast_div_le
    _ = _ := triple_reciprocal_sum_harmonic N

theorem actual_tau_second_moment_le_harmonic_cube (N : ℕ) :
    (∑ n ∈ Icc 1 N, tau n ^ 2) ≤ (N : ℝ) * (harmonic N : ℝ) ^ 3 :=
  (sum_le_sum (fun n _ => actual_tau_square_le_fourDivisorCount n)).trans
    (actual_four_divisor_sum_le_harmonic_cube N)

theorem actual_tau_second_moment_le_eight {N : ℕ} (hu : 1 ≤ Real.log (N : ℝ)) :
    (∑ n ∈ Icc 1 N, tau n ^ 2) ≤ 8 * (N : ℝ) * Real.log (N : ℝ) ^ 3 := by
  have hn : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    simp [hz] at hu
  have hh : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  have hh2 : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by linarith
  have hh0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    positivity
  have hp := pow_le_pow_left₀ hh0 hh2 3
  calc
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ 3 := actual_tau_second_moment_le_harmonic_cube N
    _ ≤ (N : ℝ) * (2 * Real.log (N : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)
    _ = _ := by ring

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.NonfriableReciprocal.quadProduct
#print axioms GoldbachRound21.NonfriableReciprocal.quadAmbient
#print axioms GoldbachRound21.NonfriableReciprocal.factorQuadDomain
#print axioms GoldbachRound21.NonfriableReciprocal.fourDivisorCount
#print axioms GoldbachRound21.NonfriableReciprocal.quadBelow
#print axioms GoldbachRound21.NonfriableReciprocal.mem_quadAmbient
#print axioms GoldbachRound21.NonfriableReciprocal.positive_quad_factor_bounds
#print axioms GoldbachRound21.NonfriableReciprocal.divisorPairToQuad
#print axioms GoldbachRound21.NonfriableReciprocal.divisorPairToQuad_reconstruct
#print axioms GoldbachRound21.NonfriableReciprocal.divisorPairToQuad_mem
#print axioms GoldbachRound21.NonfriableReciprocal.divisorPairToQuad_injective
#print axioms GoldbachRound21.NonfriableReciprocal.actual_tau_square_le_fourDivisorCount
#print axioms GoldbachRound21.NonfriableReciprocal.factorQuadDomain_eq_ambient_filter
#print axioms GoldbachRound21.NonfriableReciprocal.sum_fourDivisorCount_eq_quadBelow
#print axioms GoldbachRound21.NonfriableReciprocal.positive_product_front_count
#print axioms GoldbachRound21.NonfriableReciprocal.quadBelow_card_eq_sum_div
#print axioms GoldbachRound21.NonfriableReciprocal.triple_reciprocal_sum_harmonic
#print axioms GoldbachRound21.NonfriableReciprocal.actual_four_divisor_sum_le_harmonic_cube
#print axioms GoldbachRound21.NonfriableReciprocal.actual_tau_second_moment_le_harmonic_cube
#print axioms GoldbachRound21.NonfriableReciprocal.actual_tau_second_moment_le_eight

end
end GoldbachRound21.NonfriableReciprocal
