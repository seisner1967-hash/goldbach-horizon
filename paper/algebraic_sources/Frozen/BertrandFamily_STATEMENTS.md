# Frozen Bertrand family statements

Actual finite rational MvPolynomial family, uniform constants in N and m. Boolean constraints are separate as in Certificate. Source is compiled by pinned Lean 4.15.0 and mathlib 9837ca9d65d9de6fad1ef4381750ca688774e608.

```lean
namespace AlgebraicGoldbach
theorem primePoint_bertrandPolynomial (N m : ℕ) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    eval (primePoint N ℚ) (bertrandPolynomial N m) = 0

theorem primePoint_bertrandFamily (N : ℕ) (j : BertrandFamilyIndex N) :
    eval (primePoint N ℚ) (bertrandFamily N j) = 0

theorem modelPoint_boolean (N : ℕ) (i : Fin (N + 1)) :
    eval (modelPoint N) (booleanConstraint i) = 0

theorem modelPoint_coarse (N : ℕ) (hN : 24 ≤ N) (i : Fin (N + 1)) :
    eval (modelPoint N) (coarseConstraint i) = 0

theorem modelPoint_bertrandPolynomial (N : ℕ) (hN : 24 ≤ N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    eval (modelPoint N) (bertrandPolynomial N m) = 0

theorem modelPoint_bertrandFamily (N : ℕ) (hN : 24 ≤ N) (j : BertrandFamilyIndex N) :
    eval (modelPoint N) (bertrandFamily N j) = 0

theorem modelPoint_g_zero (N : ℕ) (hN : 24 ≤ N) :
    eval (modelPoint N) (g N ℚ) = 0

theorem modelPoint_differs_from_primePoint (N : ℕ) (hN : 24 ≤ N) :
    modelPoint N ≠ primePoint N ℚ

theorem bertrandFamily_common_zero (N : ℕ) (hN : 24 ≤ N) :
    (∀ j, eval (modelPoint N) (bertrandFamily N j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    eval (modelPoint N) (g N ℚ) = 0

theorem bertrandFamily_has_second_boolean_solution (N : ℕ) (hN : 24 ≤ N) :
    (∀ j, eval (primePoint N ℚ) (bertrandFamily N j) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ j, eval (modelPoint N) (bertrandFamily N j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    modelPoint N ≠ primePoint N ℚ

theorem bertrandFamily_no_certificate (N : ℕ) (hN : 24 ≤ N)
    (A : BertrandFamilyIndex N → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) :
    ¬Certificate (bertrandFamily N) A U B

end AlgebraicGoldbach
```
