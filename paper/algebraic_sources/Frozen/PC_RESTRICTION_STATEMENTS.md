# Frozen PC_RESTRICTION signatures

```lean
theorem degree_le {σ : Type*} {G : Set (MvPolynomial σ ℚ)} {d : ℕ}
    {f : MvPolynomial σ ℚ} (hf : Derives G d f) : f.totalDegree ≤ d

theorem scalar {σ : Type*} {G : Set (MvPolynomial σ ℚ)} {d : ℕ}
    {f : MvPolynomial σ ℚ} (hf : Derives G d f) (a : ℚ)
    (hdegree : (C a * f).totalDegree ≤ d) : Derives G d (C a * f)

theorem polynomial_nonprime (N : ℕ) (i : Fin (N + 1)) :
    polynomial N (nonprimeConstraint N i) = 0

theorem polynomial_boolean (N : ℕ) (i : Fin (N + 1)) :
    polynomial N (booleanConstraint i) =
      if h : i.val ∈ maximumSupport N then
        (X (⟨i, h⟩ : Vars N)) ^ 2 - X (⟨i, h⟩ : Vars N) else 0

theorem polynomial_g_zero (N : ℕ) : polynomial N (g N ℚ) = 0

theorem restrictedVariable_sum (N : ℕ) :
    (∑ i : Fin (N + 1), restrictedVariable N i) = ∑ i : Vars N, X i

theorem polynomial_count (N : ℕ) :
    polynomial N (countConstraint N) = knapsackCount (Vars N) (pi N)

theorem generator_image (N : ℕ) (f : R N ℚ) (hf : f ∈ dpiGenerators N) :
    polynomial N f = 0 ∨ polynomial N f ∈ knapsackGenerators (Vars N) (pi N)

theorem derivation_restriction (N d : ℕ) (f : R N ℚ)
    (hf : Derives (dpiGenerators N) d f) :
    polynomial N f = 0 ∨
      Derives (knapsackGenerators (Vars N) (pi N)) d (polynomial N f)

theorem dpi_refutation_restricts (N d : ℕ)
    (href : Refutation (dpiGenerators N) d) :
    Refutation (knapsackGenerators (Vars N) (pi N)) d

theorem dpi_degree_lower_bound_conditional (N d : ℕ)
    (hlower : KnapsackLowerBound (Vars N)) (halpha : 1 ≤ pi N - r N)
    (href : Refutation (dpiGenerators N) d) :
    (pi N - r N + 1) / 2 + 1 ≤ d
```
