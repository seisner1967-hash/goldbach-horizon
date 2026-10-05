# Frozen FACTOR_HORIZON signatures

```lean
theorem minFac_le_horizon (N M m : ℕ) (hm : 1 < m) (hmc : ¬ Nat.Prime m)
    (hmM : m ≤ M) (hMN : M ≤ N ^ 2) : Nat.minFac m ≤ N

theorem primePoint_factorPolynomial (N M m : ℕ) (hMN : M ≤ N ^ 2)
    (hm : 1 < m) (hmM : m ≤ M) (hmc : ¬ Nat.Prime m) :
    eval (primePoint N ℚ) (factorPolynomial N m) = 0

theorem primePoint_coverage (N M : ℕ) (hMN : M ≤ N ^ 2) :
    Coverage N M (primePoint N ℚ)

theorem properDivisors_prime_square (N p : ℕ) (hp : Nat.Prime p) (hpN : p ≤ N) :
    properDivisors N (p ^ 2) = {⟨p, by omega⟩}

theorem coverage_implies_primePins (N M : ℕ) (x : Fin (N + 1) → ℚ)
    (hcov : Coverage N M x) : PrimePins N M x

theorem primePins_implies_coverage (N M : ℕ) (hMN : M ≤ N ^ 2)
    (x : Fin (N + 1) → ℚ) (hpins : PrimePins N M x) : Coverage N M x

theorem coverage_iff_primePins (N M : ℕ) (hMN : M ≤ N ^ 2)
    (x : Fin (N + 1) → ℚ) : Coverage N M x ↔ PrimePins N M x

theorem square_horizon_pins_prime_coordinates (N : ℕ) (x : Fin (N + 1) → ℚ)
    (hcov : Coverage N (N ^ 2) x) (i : Fin (N + 1)) (hi : Nat.Prime i.val) :
    x i = 1

theorem square_horizon_and_sieve_pin_vector (N : ℕ) (x : Fin (N + 1) → ℚ)
    (hcov : Coverage N (N ^ 2) x)
    (hsieve : ∀ i, ¬ Nat.Prime i.val → x i = 0) : x = primePoint N ℚ

theorem modelPoint_small_prime (N p : ℕ) (hp : Nat.Prime p)
    (hpN : p ≤ N) (hpH : p ≤ N / 2 - 3) : modelPoint N ⟨p, by omega⟩ = 1

theorem modelPoint_coverage (N M : ℕ) (hM : M ≤ (N / 2 - 3) ^ 2) :
    Coverage N M (modelPoint N)

theorem primePoint_horizonFamily (N M : ℕ) (hMN : M ≤ N ^ 2)
    (j : HorizonFamilyIndex N M) : eval (primePoint N ℚ) (horizonFamily N M j) = 0

theorem modelPoint_horizonFamily (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) (j : HorizonFamilyIndex N M) :
    eval (modelPoint N) (horizonFamily N M j) = 0

theorem horizonFamily_common_zero (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) :
    (∀ j, eval (modelPoint N) (horizonFamily N M j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    eval (modelPoint N) (g N ℚ) = 0

theorem horizonFamily_no_certificate (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) (A : HorizonFamilyIndex N M → R N ℚ)
    (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) : ¬ Certificate (horizonFamily N M) A U B

theorem horizonFamily_has_second_boolean_solution (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) :
    (∀ j, eval (primePoint N ℚ) (horizonFamily N M j) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ j, eval (modelPoint N) (horizonFamily N M j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    modelPoint N ≠ primePoint N ℚ
```
