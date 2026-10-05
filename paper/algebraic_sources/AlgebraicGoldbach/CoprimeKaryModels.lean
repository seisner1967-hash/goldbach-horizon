import AlgebraicGoldbach.CoprimeKaryIdeal

/-!
The exact rational models of k-ary coprime divisor coverage are the assignments
omitting fewer than k prime coordinates. No Boolean or SIEVE assumption is used.
This makes the hidden density condition explicit; it gives no candidate credit.
-/

namespace AlgebraicGoldbach.CoprimeKaryModels

noncomputable section
open scoped BigOperators
open MvPolynomial CoprimeKaryIdeal

theorem family_iff_omitted_card_lt (N k : ℕ) (x : Fin (N + 1) → ℚ) :
    (∀ S : ArithmeticIndex N k, eval x (arithmeticFamily N k S) = 0) ↔
      (CoprimeDivisor.omittedPrimes N x).card < k := by
  classical
  constructor
  · intro hF
    by_contra hcard
    obtain ⟨T, hTO, hTk⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hcard)
    have hT : PrimeAllowed k T := by
      refine ⟨hTk, ?_⟩
      intro p hp
      have hpo := hTO hp
      simp only [CoprimeDivisor.omittedPrimes, Finset.mem_filter,
        Finset.mem_univ, true_and] at hpo
      exact hpo.1
    let S : ArithmeticIndex N k :=
      ⟨T, primeAllowed_arithmeticAllowed T hT⟩
    have hz := hF S
    have he : arithmeticFamily N k S = product N T := by
      simp only [arithmeticFamily, S, prime_divisors_eq T hT]
    rw [he] at hz
    have hnz : eval x (product N T) ≠ 0 := by
      simp only [product, map_prod, map_sub, map_one, eval_X]
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      have hpo := hTO hp
      simp only [CoprimeDivisor.omittedPrimes, Finset.mem_filter,
        Finset.mem_univ, true_and] at hpo
      intro heq
      exact hpo.2 (sub_eq_zero.mp heq).symm
    exact hnz hz
  · intro hcard S
    let T := S.val.image leastFactor
    have hT : PrimeAllowed k T := leastFactor_image_primeAllowed S.val S.property
    have hnot : ¬ T ⊆ CoprimeDivisor.omittedPrimes N x := by
      intro hsub
      have hc := Finset.card_le_card hsub
      rw [hT.1] at hc
      omega
    obtain ⟨p, hpT, hpO⟩ := Finset.not_subset.mp hnot
    have hpx : x p = 1 := by
      have hp := hT.2 p hpT
      simpa [CoprimeDivisor.omittedPrimes, hp] using hpO
    have hpD : p ∈ divisors N S.val :=
      leastFactor_image_subset_divisors S.val S.property hpT
    simp only [arithmeticFamily, product, map_prod]
    apply Finset.prod_eq_zero (i := p) hpD
    simp [hpx]

end
end AlgebraicGoldbach.CoprimeKaryModels
