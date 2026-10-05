# Frozen SIGN_DEFINITE signatures

```lean
theorem coefficient_on_primes_eq_zero {N : ℕ} (P : R N ℚ)
    (hcoeff : NonnegativeCoefficients P)
    (htruth : eval (primePoint N ℚ) P = 0)
    (d : Fin (N + 1) →₀ ℕ)
    (hprime : ∀ i ∈ d.support, Nat.Prime i.val) : coeff d P = 0

theorem nonnegative_equation_vanishes_on_sievePoint {N : ℕ} (P : R N ℚ)
    (hcoeff : NonnegativeCoefficients P)
    (htruth : eval (primePoint N ℚ) P = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x) : eval x P = 0

theorem sign_definite_equation_vanishes_on_sievePoint {N : ℕ} (P : R N ℚ)
    (hcoeff : SignDefiniteCoefficients P)
    (htruth : eval (primePoint N ℚ) P = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x) : eval x P = 0

theorem sign_definite_family_preserves_sieve_common_zero {N : ℕ}
    {ι κ : Type*} (F : ι → R N ℚ) (P : κ → R N ℚ)
    (hcoeff : ∀ j, SignDefiniteCoefficients (P j))
    (htruth : ∀ j, eval (primePoint N ℚ) (P j) = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x)
    (hF : ∀ j, eval x (F j) = 0) :
    ∀ j : ι ⊕ κ, eval x (Sum.elim F P j) = 0

theorem sign_definite_strengthening_has_no_certificate {N : ℕ}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → R N ℚ) (P : κ → R N ℚ)
    (hcoeff : ∀ j, SignDefiniteCoefficients (P j))
    (htruth : ∀ j, eval (primePoint N ℚ) (P j) = 0)
    (x : Fin (N + 1) → ℚ) (hx : SievePoint N x)
    (hF : ∀ j, eval x (F j) = 0)
    (hBool : ∀ i, eval x (booleanConstraint i) = 0)
    (hg : eval x (g N ℚ) = 0)
    (A : ι ⊕ κ → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) :
    ¬ Certificate (Sum.elim F P) A U B
```
