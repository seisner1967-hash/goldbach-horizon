import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

/-!
A finite factor-count prime-detection weight on the actual rough domain.
Omega counts prime factors WITH multiplicity. No squarefree assumption is used.
The prime indicator identity supplies no estimate of its additive mean.
-/

namespace GoldbachResearch.ChenWeight

open scoped BigOperators

def factorCount (n : ℕ) : ℕ := ArithmeticFunction.cardFactors n

noncomputable def weight (n : ℕ) : ℝ :=
  ((factorCount n : ℝ) - 2) * ((factorCount n : ℝ) - 3) / 2

theorem weight_expansion (n : ℕ) :
    weight n = 3 - 2 * (factorCount n : ℝ) +
      (factorCount n : ℝ) * ((factorCount n : ℝ) - 1) / 2 := by
  unfold weight
  ring

theorem lower_bound_list_product (b : ℕ) (l : List ℕ)
    (hl : ∀ p ∈ l, b ≤ p) : b ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.length_cons, List.prod_cons, pow_succ]
    have hp : b ≤ p := hl p (by simp)
    have ht : ∀ q ∈ l, b ≤ q := by
      intro q hq
      exact hl q (by simp [hq])
    simpa only [mul_comm] using Nat.mul_le_mul (ih ht) hp

theorem factorCount_le_three_of_rough {alpha n : ℕ}
    (hn : n ≠ 0) (hbound : n < (alpha + 1) ^ 4)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n → alpha < p) :
    factorCount n ≤ 3 := by
  have hprod : (alpha + 1) ^ n.primeFactorsList.length ≤ n := by
    calc
      _ ≤ n.primeFactorsList.prod := by
        apply lower_bound_list_product
        intro p hp
        exact Nat.succ_le_of_lt
          (hrough p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp))
      _ = n := Nat.prod_primeFactorsList hn
  by_contra hcount
  have hfour : 4 ≤ n.primeFactorsList.length := by
    change ¬ n.primeFactorsList.length ≤ 3 at hcount
    omega
  have hpow : (alpha + 1) ^ 4 ≤ (alpha + 1) ^ n.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega : 0 < alpha + 1) hfour
  omega

theorem factorCount_positive_of_gt_one {n : ℕ} (hn : 1 < n) :
    1 ≤ factorCount n := by
  by_contra h
  have hzero : n.primeFactorsList.length = 0 := by
    change ¬ 1 ≤ n.primeFactorsList.length at h
    omega
  have hnil : n.primeFactorsList = [] := List.length_eq_zero.mp hzero
  have hn01 := (Nat.primeFactorsList_eq_nil n).mp hnil
  omega

theorem weight_prime_indicator_of_factorCount {n : ℕ}
    (hpos : 1 ≤ factorCount n) (hle : factorCount n ≤ 3) :
    weight n = if n.Prime then 1 else 0 := by
  have hcases : factorCount n = 1 ∨ factorCount n = 2 ∨ factorCount n = 3 := by omega
  have hprime : n.Prime ↔ factorCount n = 1 :=
    ArithmeticFunction.cardFactors_eq_one_iff_prime.symm
  simp only [hprime]
  rcases hcases with h | h | h <;> norm_num [weight, h]

theorem weight_prime_indicator_of_rough {alpha n : ℕ}
    (hn : 1 < n) (hbound : n < (alpha + 1) ^ 4)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n → alpha < p) :
    weight n = if n.Prime then 1 else 0 := by
  apply weight_prime_indicator_of_factorCount (factorCount_positive_of_gt_one hn)
  exact factorCount_le_three_of_rough (by omega) hbound hrough

theorem weight_prime_indicator_of_N {alpha N n : ℕ}
    (hn : 1 < n) (hnN : n < N) (hN : N ≤ alpha ^ 4)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n → alpha < p) :
    weight n = if n.Prime then 1 else 0 := by
  apply weight_prime_indicator_of_rough hn
  · have hpow : alpha ^ 4 ≤ (alpha + 1) ^ 4 :=
      Nat.pow_le_pow_left (by omega : alpha ≤ alpha + 1) 4
    exact lt_of_lt_of_le hnN (le_trans hN hpow)
  · exact hrough

theorem weighted_prime_identity_real {ι : Type*} (s : Finset ι)
    (r : ι → ℕ) (c : ι → ℝ) {alpha N : ℕ} (hN : N ≤ alpha ^ 4)
    (hs : ∀ t ∈ s, 1 < r t ∧ r t < N ∧
      (∀ p : ℕ, p.Prime → p ∣ r t → alpha < p)) :
    ∑ t ∈ s, c t * weight (r t) =
      ∑ t ∈ s, c t * (if (r t).Prime then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [weight_prime_indicator_of_N (hs t ht).1 (hs t ht).2.1 hN (hs t ht).2.2]

#print axioms weight_expansion
#print axioms lower_bound_list_product
#print axioms factorCount_le_three_of_rough
#print axioms factorCount_positive_of_gt_one
#print axioms weight_prime_indicator_of_factorCount
#print axioms weight_prime_indicator_of_rough
#print axioms weight_prime_indicator_of_N
#print axioms weighted_prime_identity_real

end GoldbachResearch.ChenWeight
