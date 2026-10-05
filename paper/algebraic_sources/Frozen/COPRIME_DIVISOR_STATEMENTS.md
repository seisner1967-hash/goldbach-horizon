# Frozen COPRIME_DIVISOR signatures

```lean
theorem nearFullPrimeSelection_iff_omitted_card_le_one {N : ℕ}
    (x : Fin (N + 1) → ℚ) :
    NearFullPrimeSelection N x ↔ (omittedPrimes N x).card ≤ 1

theorem pairDivisors_prime_pair (N : ℕ) (p q : Fin (N + 1))
    (hp : Nat.Prime p.val) (hq : Nat.Prime q.val) :
    pairDivisors N p.val q.val = {p, q}

theorem family_implies_ordered_prime_pair_selected {N : ℕ}
    (x : Fin (N + 1) → ℚ) (hF : ∀ m, eval x (family N m) = 0)
    (p q : Fin (N + 1)) (hp : Nat.Prime p.val) (hq : Nat.Prime q.val)
    (hpq : p.val < q.val) : x p = 1 ∨ x q = 1

theorem family_implies_nearFullPrimeSelection {N : ℕ}
    (x : Fin (N + 1) → ℚ) (hF : ∀ m, eval x (family N m) = 0) :
    NearFullPrimeSelection N x

theorem nearFullPrimeSelection_implies_family {N : ℕ}
    (x : Fin (N + 1) → ℚ) (hx : NearFullPrimeSelection N x) (m : Index N) :
    eval x (family N m) = 0

theorem family_iff_nearFullPrimeSelection {N : ℕ} (x : Fin (N + 1) → ℚ) :
    (∀ m, eval x (family N m) = 0) ↔ NearFullPrimeSelection N x

theorem family_iff_at_most_one_omitted_prime {N : ℕ} (x : Fin (N + 1) → ℚ) :
    (∀ m, eval x (family N m) = 0) ↔ (omittedPrimes N x).card ≤ 1

theorem primePoint_family (N : ℕ) (m : Index N) :
    eval (primePoint N ℚ) (family N m) = 0

theorem onePoint_family (N : ℕ) (m : Index N) :
    eval (ProperBertrand.onePoint N) (family N m) = 0

theorem exceptPoint_family (N : ℕ) (target : Fin (N + 1)) (m : Index N) :
    eval (ProperBertrand.exceptPoint N target) (family N m) = 0

theorem family_does_not_pin_any_coordinate (N : ℕ) (target : Fin (N + 1)) :
    (∀ m, eval (ProperBertrand.exceptPoint N target) (family N m) = 0) ∧
    (∀ i, eval (ProperBertrand.exceptPoint N target) (booleanConstraint i) = 0) ∧
    ProperBertrand.exceptPoint N target target = 0 ∧
    (∀ m, eval (ProperBertrand.onePoint N) (family N m) = 0) ∧
    (∀ i, eval (ProperBertrand.onePoint N) (booleanConstraint i) = 0) ∧
    ProperBertrand.onePoint N target = 1

theorem family_has_second_boolean_solution (N : ℕ) :
    (∀ m, eval (primePoint N ℚ) (family N m) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ m, eval (ProperBertrand.onePoint N) (family N m) = 0) ∧
    (∀ i, eval (ProperBertrand.onePoint N) (booleanConstraint i) = 0) ∧
    ProperBertrand.onePoint N ≠ primePoint N ℚ
```
