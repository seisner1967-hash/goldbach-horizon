import Calibration.LowerBound

namespace AlgebraicGoldbach.Calibration

theorem representatives_subset_maximumSupport_insert (N : ℕ) :
    pairRepresentatives N ⊆ insert (N / 2) (maximumSupport N) := by
  intro p hp
  obtain ⟨hpN, hpp, hqp, hpq⟩ := mem_pairRepresentatives.mp hp
  by_cases hstrict : p < N - p
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_primes.mpr ⟨hpN, hpp⟩, ?_⟩
    intro hu
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hu
    obtain ⟨hqN, _, _, hqle⟩ := mem_pairRepresentatives.mp hq
    omega
  · have he : p = N / 2 := by omega
    simp [he]

theorem pair_count_le_independence_plus_one (N : ℕ) :
    r N ≤ pi N - r N + 1 := by
  have hc := Finset.card_le_card (representatives_subset_maximumSupport_insert N)
  have hi := Finset.card_insert_le (N / 2) (maximumSupport N)
  rw [maximumSupport_card] at hi
  calc
    r N = (pairRepresentatives N).card := r_eq_card_representatives N
    _ ≤ (insert (N / 2) (maximumSupport N)).card := hc
    _ ≤ pi N - r N + 1 := hi

theorem independence_ge_half_prime_count (N : ℕ) :
    pi N / 2 ≤ pi N - r N := by
  have hr : r N ≤ pi N := by
    have hc := Finset.card_le_card (upperEndpoints_subset N)
    rw [upperEndpoints_card] at hc
    exact hc
  have h := pair_count_le_independence_plus_one N
  omega

theorem independence_unbounded_on_even :
    ∀ d : ℕ, ∃ N : ℕ, Even N ∧ 4 ≤ N ∧ d ≤ pi N - r N := by
  intro d
  obtain ⟨n, hn⟩ := Nat.surjective_primeCounting (2 * d)
  let N := 2 * (n + 2)
  have hcount : 2 * d ≤ N.primeCounting := by
    have hmono := Nat.monotone_primeCounting (show n ≤ N by dsimp [N]; omega)
    omega
  refine ⟨N, ⟨n + 2, by dsimp [N]; omega⟩, by dsimp [N]; omega, ?_⟩
  have h := independence_ge_half_prime_count N
  rw [pi_eq_primeCounting] at h
  rw [pi_eq_primeCounting]
  omega

theorem Dpi_standard_degree_unbounded_on_even :
    ∀ d : ℕ, ∃ N : ℕ, Even N ∧ 4 ≤ N ∧
      ∀ (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ),
        LowerBound.Restriction.DpiCertificate N A B U C →
        d < (A * LowerBound.Restriction.countConstraint N).totalDegree := by
  intro d
  obtain ⟨N, hEven, hN, hlarge⟩ := independence_unbounded_on_even d
  refine ⟨N, hEven, hN, ?_⟩
  intro A B U C hcert
  have hbound := LowerBound.Restriction.Dpi_standard_degree_lower_bound N A B U C hcert
  omega

end AlgebraicGoldbach.Calibration
