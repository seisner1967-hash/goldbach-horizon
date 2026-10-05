import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace AlgebraicGoldbach

def high (N : ℕ) : ℕ :=
  if N / 2 % 2 = 0 then N / 2 + 1 else N / 2 + 2

def selected (N n : ℕ) : Prop :=
  n = 2 ∨ (3 ≤ n ∧ n < N / 2 ∧ n % 2 = 1 ∧ n ≠ N - high N) ∨ n = high N

instance (N n : ℕ) : Decidable (selected N n) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def bit (N n : ℕ) : ℕ := if selected N n then 1 else 0

theorem high_bounds (N : ℕ) : N / 2 + 1 ≤ high N ∧ high N ≤ N / 2 + 2 := by
  unfold high
  split_ifs <;> omega

theorem high_odd (N : ℕ) : high N % 2 = 1 := by
  unfold high
  have hmod := Nat.mod_lt (N / 2) (by omega : 0 < 2)
  split_ifs <;> omega

theorem bit_boolean (N n : ℕ) : bit N n * bit N n = bit N n := by
  unfold bit
  split_ifs <;> norm_num

theorem selected_coarse (N : ℕ) (hN : 24 ≤ N) :
    ¬ selected N 0 ∧ ¬ selected N 1 ∧
      ∀ n, 2 < n → n % 2 = 0 → ¬ selected N n := by
  have hb := high_bounds N
  have ho := high_odd N
  unfold selected
  constructor
  · omega
  constructor
  · omega
  intro n hn he
  omega

theorem selected_no_sum (N : ℕ) (hN : 24 ≤ N) (n q : ℕ)
    (hn : selected N n) (hq : selected N q) : n + q ≠ N := by
  have hb := high_bounds N
  unfold selected at hn hq
  rcases hn with hn | hn | hn <;> rcases hq with hq | hq | hq
  all_goals omega

theorem selected_bertrand (N : ℕ) (hN : 24 ≤ N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    ∃ n, m < n ∧ n ≤ 2 * m ∧ selected N n := by
  by_cases hm1 : m = 1
  · refine ⟨2, ?_, ?_, Or.inl rfl⟩ <;> omega
  have hm2 : 2 ≤ m := by omega
  let n := if (m + 1) % 2 = 1 then m + 1 else m + 2
  have hn : m + 1 ≤ n ∧ n ≤ m + 2 ∧ n % 2 = 1 := by
    have hmod := Nat.mod_lt (m + 1) (by omega : 0 < 2)
    dsimp [n]
    split_ifs <;> omega
  have hb := high_bounds N
  by_cases hsmall : n < N / 2 ∧ n ≠ N - high N
  · exact ⟨n, by omega, by omega, Or.inr (Or.inl ⟨by omega, hsmall.1, hn.2.2, hsmall.2⟩)⟩
  · refine ⟨high N, ?_, ?_, Or.inr (Or.inr rfl)⟩
    · omega
    · omega

theorem bit_goldbach_zero (N : ℕ) (hN : 24 ≤ N) :
    (∑ n ∈ Finset.range (N + 1), bit N n * bit N (N - n)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hnN : n ≤ N := by
    have : n < N + 1 := Finset.mem_range.mp hn
    omega
  unfold bit
  split_ifs with hs ht ht
  · have hc := selected_no_sum N hN n (N - n) hs ht
    omega
  all_goals norm_num

theorem prime_indicator_bertrand (N m : ℕ) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    ∃ p, p.Prime ∧ m < p ∧ p ≤ 2 * m ∧ p ≤ N := by
  obtain ⟨p, hp, hmp, hpm⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  exact ⟨p, hp, hmp, hpm, by omega⟩

theorem bit_bertrand_product (N : ℕ) (hN : 24 ≤ N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    (Finset.prod (Finset.Icc (m + 1) (2 * m)) (fun n => (1 : ℚ) - (bit N n : ℚ))) = 0 := by
  obtain ⟨n, hmn, hnm, hs⟩ := selected_bertrand N hN m hm hmN
  apply Finset.prod_eq_zero (i := n) (Finset.mem_Icc.mpr ⟨by omega, hnm⟩)
  simp [bit, hs]

def primeBit (n : ℕ) : ℕ := if n.Prime then 1 else 0

theorem prime_bit_boolean (n : ℕ) : primeBit n * primeBit n = primeBit n := by
  unfold primeBit
  split_ifs <;> norm_num

theorem prime_bit_coarse : primeBit 0 = 0 ∧ primeBit 1 = 0 ∧
    ∀ n, 2 < n → n % 2 = 0 → primeBit n = 0 := by
  constructor
  · norm_num [primeBit]
  constructor
  · norm_num [primeBit]
  intro n hn he
  have hnp : ¬ n.Prime := by
    intro hp
    rcases hp.eq_two_or_odd with h | h <;> omega
  simp [primeBit, hnp]

theorem prime_bit_bertrand_product (N m : ℕ) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    (Finset.prod (Finset.Icc (m + 1) (2 * m)) (fun n => (1 : ℚ) - (primeBit n : ℚ))) = 0 := by
  obtain ⟨p, hp, hmp, hpm, _⟩ := prime_indicator_bertrand N m hm hmN
  apply Finset.prod_eq_zero (i := p) (Finset.mem_Icc.mpr ⟨by omega, hpm⟩)
  simp [primeBit, hp]

theorem bit_coarse (N : ℕ) (hN : 24 ≤ N) : bit N 0 = 0 ∧ bit N 1 = 0 ∧
    ∀ n, 2 < n → n % 2 = 0 → bit N n = 0 := by
  obtain ⟨h0, h1, he⟩ := selected_coarse N hN
  exact ⟨by simp [bit, h0], by simp [bit, h1], fun n hn hm => by simp [bit, he n hn hm]⟩

theorem uniform_bertrand_countermodel (N : ℕ) (hN : 24 ≤ N) :
    (∀ n, bit N n * bit N n = bit N n) ∧
    (bit N 0 = 0 ∧ bit N 1 = 0 ∧ ∀ n, 2 < n → n % 2 = 0 → bit N n = 0) ∧
    (∀ m, 1 ≤ m → 2 * m ≤ N →
      (Finset.prod (Finset.Icc (m + 1) (2 * m)) (fun n => (1 : ℚ) - (bit N n : ℚ))) = 0) ∧
    (∑ n ∈ Finset.range (N + 1), bit N n * bit N (N - n)) = 0 := by
  exact ⟨bit_boolean N, bit_coarse N hN, bit_bertrand_product N hN, bit_goldbach_zero N hN⟩

end AlgebraicGoldbach
