# Frozen C1 signatures

```lean
theorem pair_sets_injective (N : ℕ) :
    Set.InjOn (fun p => ({p, N - p} : Finset ℕ)) ↑(pairRepresentatives N)

theorem mem_unorderedPrimePairs {N : ℕ} {E : Finset ℕ} :
    E ∈ unorderedPrimePairs N ↔
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N ∧ E = {p, q}

theorem pi_eq_primeCounting (N : ℕ) : pi N = N.primeCounting

theorem r_eq_card_representatives (N : ℕ) : r N = (pairRepresentatives N).card

theorem upperEndpoints_subset (N : ℕ) : upperEndpoints N ⊆ primes N

theorem upperEndpoints_card (N : ℕ) : (upperEndpoints N).card = r N

theorem maximumSupport_card (N : ℕ) : (maximumSupport N).card = pi N - r N

theorem maximumSupport_independent (N : ℕ) : Independent N (maximumSupport N)

theorem independent_card_le {N : ℕ} {S : Finset ℕ} (hS : Independent N S) :
    S.card ≤ pi N - r N

theorem independent_exists_iff (N m : ℕ) :
    (∃ S : Finset ℕ, Independent N S ∧ S.card = m) ↔ m ≤ pi N - r N

theorem boolean_iff (a : ℚ) : a ^ 2 - a = 0 ↔ a = 0 ∨ a = 1

theorem support_subset_primes {N : ℕ} {x : ℕ → ℚ}
    (hz : ∀ p ≤ N, ¬ Nat.Prime p → x p = 0) : support N x ⊆ primes N

theorem sum_eq_support_card {N : ℕ} {x : ℕ → ℚ}
    (hb : ∀ p ≤ N, x p ^ 2 - x p = 0) :
    (∑ p ∈ range (N + 1), x p) = ((support N x).card : ℚ)

theorem g_zero_iff_independent {N : ℕ} {x : ℕ → ℚ}
    (hb : ∀ p ≤ N, x p ^ 2 - x p = 0)
    (hz : ∀ p ≤ N, ¬ Nat.Prime p → x p = 0) :
    g N x = 0 ↔ Independent N (support N x)

theorem characteristic_boolean (S : Finset ℕ) (p : ℕ) :
    characteristic S p ^ 2 - characteristic S p = 0

theorem support_characteristic {N : ℕ} {S : Finset ℕ} (hS : S ⊆ primes N) :
    support N (characteristic S) = S

theorem C1 (N m : ℕ) :
    (∃ x : ℕ → ℚ, D N m x ∧ g N x = 0) ↔ m ≤ pi N - r N

theorem C1_primeCounting (N m : ℕ) :
    (∃ x : ℕ → ℚ, D N m x ∧ g N x = 0) ↔ m ≤ N.primeCounting - r N

theorem r_le_pi (N : ℕ) : r N ≤ pi N

theorem no_pseudo_solution_at_full_count_iff (N : ℕ) :
    (¬ ∃ x : ℕ → ℚ, D N (pi N) x ∧ g N x = 0) ↔ 1 ≤ r N

theorem r_positive_iff (N : ℕ) :
    1 ≤ r N ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

theorem D_true_prime_indicator (N : ℕ) :
    D N (pi N) (fun p => if Nat.Prime p then 1 else 0)

theorem D_full_count_pins {N : ℕ} {x : ℕ → ℚ} (hx : D N (pi N) x) :
    ∀ p ≤ N, x p = if Nat.Prime p then 1 else 0
```
