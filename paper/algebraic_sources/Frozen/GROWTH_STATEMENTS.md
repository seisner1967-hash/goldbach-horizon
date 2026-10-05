# Frozen GROWTH signatures

```lean
theorem representatives_subset_maximumSupport_insert (N : ℕ) :
    pairRepresentatives N ⊆ insert (N / 2) (maximumSupport N)

theorem pair_count_le_independence_plus_one (N : ℕ) :
    r N ≤ pi N - r N + 1

theorem independence_ge_half_prime_count (N : ℕ) :
    pi N / 2 ≤ pi N - r N

theorem independence_unbounded_on_even :
    ∀ d : ℕ, ∃ N : ℕ, Even N ∧ 4 ≤ N ∧ d ≤ pi N - r N

theorem Dpi_standard_degree_unbounded_on_even :
    ∀ d : ℕ, ∃ N : ℕ, Even N ∧ 4 ≤ N ∧
      ∀ (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ),
        LowerBound.Restriction.DpiCertificate N A B U C →
        d < (A * LowerBound.Restriction.countConstraint N).totalDegree
```
