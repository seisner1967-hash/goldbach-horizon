# Frozen KARY_IDEAL signatures

```lean
theorem leastFactor_val {N : ℕ} (u : Fin (N + 1)) (hu : 2 ≤ u.val) :
    (leastFactor u).val = Nat.minFac u.val

theorem leastFactor_prime {N : ℕ} (u : Fin (N + 1)) (hu : 2 ≤ u.val) :
    Nat.Prime (leastFactor u).val

theorem leastFactor_dvd {N : ℕ} (u : Fin (N + 1)) (hu : 2 ≤ u.val) :
    (leastFactor u).val ∣ u.val

theorem leastFactor_injective_on {N k : ℕ} (S : Finset (Fin (N + 1)))
    (hS : ArithmeticAllowed k S) :
    Set.InjOn (leastFactor (N := N)) (S : Set (Fin (N + 1)))

theorem leastFactor_image_primeAllowed {N k : ℕ} (S : Finset (Fin (N + 1)))
    (hS : ArithmeticAllowed k S) : PrimeAllowed k (S.image leastFactor)

theorem leastFactor_image_subset_divisors {N k : ℕ}
    (S : Finset (Fin (N + 1))) (hS : ArithmeticAllowed k S) :
    S.image leastFactor ⊆ divisors N S

theorem primeAllowed_arithmeticAllowed {N k : ℕ}
    (T : Finset (Fin (N + 1))) (hT : PrimeAllowed k T) :
    ArithmeticAllowed k T

theorem prime_divisors_eq {N k : ℕ} (T : Finset (Fin (N + 1)))
    (hT : PrimeAllowed k T) : divisors N T = T

theorem arithmetic_factorization {N k : ℕ} (S : Finset (Fin (N + 1)))
    (hS : ArithmeticAllowed k S) :
    product N (divisors N S) =
      product N (S.image leastFactor) *
        product N (divisors N S \ S.image leastFactor)

theorem arithmeticIdeal_eq_primeIdeal (N k : ℕ) :
    arithmeticIdeal N k = primeIdeal N k
```
