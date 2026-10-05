# Frozen UNIFORM signatures

```lean
theorem high_bounds (N : ℕ) : N / 2 + 1 ≤ high N ∧ high N ≤ N / 2 + 2

theorem high_odd (N : ℕ) : high N % 2 = 1

theorem bit_boolean (N n : ℕ) : bit N n * bit N n = bit N n

theorem selected_coarse (N : ℕ) (hN : 24 ≤ N) :
    ¬ selected N 0 ∧ ¬ selected N 1 ∧
      ∀ n, 2 < n → n % 2 = 0 → ¬ selected N n

theorem selected_no_sum (N : ℕ) (hN : 24 ≤ N) (n q : ℕ)
    (hn : selected N n) (hq : selected N q) : n + q ≠ N

theorem selected_bertrand (N : ℕ) (hN : 24 ≤ N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    ∃ n, m < n ∧ n ≤ 2 * m ∧ selected N n

theorem bit_goldbach_zero (N : ℕ) (hN : 24 ≤ N) :
    (∑ n ∈ Finset.range (N + 1), bit N n * bit N (N - n)) = 0

theorem prime_indicator_bertrand (N m : ℕ) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    ∃ p, p.Prime ∧ m < p ∧ p ≤ 2 * m ∧ p ≤ N

theorem bit_bertrand_product (N : ℕ) (hN : 24 ≤ N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    (Finset.prod (Finset.Icc (m + 1) (2 * m)) (fun n => (1 : ℚ) - (bit N n : ℚ))) = 0

theorem prime_bit_boolean (n : ℕ) : primeBit n * primeBit n = primeBit n

theorem prime_bit_coarse : primeBit 0 = 0 ∧ primeBit 1 = 0 ∧
    ∀ n, 2 < n → n % 2 = 0 → primeBit n = 0

theorem prime_bit_bertrand_product (N m : ℕ) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    (Finset.prod (Finset.Icc (m + 1) (2 * m)) (fun n => (1 : ℚ) - (primeBit n : ℚ))) = 0

theorem bit_coarse (N : ℕ) (hN : 24 ≤ N) : bit N 0 = 0 ∧ bit N 1 = 0 ∧
    ∀ n, 2 < n → n % 2 = 0 → bit N n = 0

theorem uniform_bertrand_countermodel (N : ℕ) (hN : 24 ≤ N) :
    (∀ n, bit N n * bit N n = bit N n) ∧
    (bit N 0 = 0 ∧ bit N 1 = 0 ∧ ∀ n, 2 < n → n % 2 = 0 → bit N n = 0) ∧
    (∀ m, 1 ≤ m → 2 * m ≤ N →
      (Finset.prod (Finset.Icc (m + 1) (2 * m)) (fun n => (1 : ℚ) - (bit N n : ℚ))) = 0) ∧
    (∑ n ∈ Finset.range (N + 1), bit N n * bit N (N - n)) = 0

theorem uniform_model_selects_composite_nine (N : ℕ) (hN : 24 ≤ N) :
    bit N 9 = 1 ∧ primeBit 9 = 0

theorem uniform_model_differs_from_primes (N : ℕ) (hN : 24 ≤ N) :
    bit N ≠ primeBit
```
