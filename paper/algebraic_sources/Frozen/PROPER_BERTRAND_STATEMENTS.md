# Frozen PROPER_BERTRAND signatures

```lean
theorem primePoint_family (N : ℕ) (m : Index N) :
    eval (primePoint N ℚ) (family N m) = 0

theorem onePoint_boolean (N : ℕ) (i : Fin (N + 1)) :
    eval (onePoint N) (booleanConstraint i) = 0

theorem exceptPoint_boolean (N : ℕ) (target i : Fin (N + 1)) :
    eval (exceptPoint N target) (booleanConstraint i) = 0

theorem onePoint_family (N : ℕ) (m : Index N) : eval (onePoint N) (family N m) = 0

theorem exceptPoint_family (N : ℕ) (target : Fin (N + 1)) (m : Index N) :
    eval (exceptPoint N target) (family N m) = 0

theorem onePoint_differs_from_primePoint (N : ℕ) : onePoint N ≠ primePoint N ℚ

theorem family_has_second_boolean_solution (N : ℕ) :
    (∀ m, eval (primePoint N ℚ) (family N m) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ m, eval (onePoint N) (family N m) = 0) ∧
    (∀ i, eval (onePoint N) (booleanConstraint i) = 0) ∧
    onePoint N ≠ primePoint N ℚ

theorem family_does_not_pin_any_coordinate (N : ℕ) (target : Fin (N + 1)) :
    (∀ m, eval (exceptPoint N target) (family N m) = 0) ∧
    (∀ i, eval (exceptPoint N target) (booleanConstraint i) = 0) ∧
    exceptPoint N target target = 0 ∧
    (∀ m, eval (onePoint N) (family N m) = 0) ∧
    (∀ i, eval (onePoint N) (booleanConstraint i) = 0) ∧
    onePoint N target = 1

theorem modelPoint_family (N : ℕ) (hN : 24 ≤ N) (m : Index N) :
    eval (modelPoint N) (family N m) = 0

theorem family_common_zero (N : ℕ) (hN : 24 ≤ N) :
    (∀ m, eval (modelPoint N) (family N m) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    eval (modelPoint N) (g N ℚ) = 0

theorem family_no_certificate (N : ℕ) (hN : 24 ≤ N)
    (A : Index N → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) :
    ¬ Certificate (family N) A U B
```
