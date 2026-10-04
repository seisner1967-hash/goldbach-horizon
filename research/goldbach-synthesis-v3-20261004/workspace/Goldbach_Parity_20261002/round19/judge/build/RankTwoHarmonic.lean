import TerminalPrimeExtraction

/-! Exact harmonic mass of true cofactor products with ranks one and two.
The diagonal prime squares is retained with its full reciprocal weight. -/
namespace GoldbachRound19.Harmonic

open Finset GoldbachRound19.Terminal
noncomputable section

def primesThrough (B : ℕ) : Finset ℕ := (Icc 2 B).filter Nat.Prime
def orderedPrimePairs (B : ℕ) : Finset (ℕ × ℕ) :=
  (primesThrough B ×ˢ primesThrough B).filter (fun z => z.1 ≤ z.2)
def pairValue (z : ℕ × ℕ) : ℕ := z.1 * z.2
def rankTwoCofactors (B : ℕ) : Finset ℕ :=
  primesThrough B ∪ (orderedPrimePairs B).image pairValue
def harmonic (s : Finset ℕ) : ℝ := ∑ n ∈ s, 1 / (n : ℝ)
def firstMoment (B : ℕ) : ℝ := harmonic (primesThrough B)
def secondMoment (B : ℕ) : ℝ := ∑ p ∈ primesThrough B, 1 / (p : ℝ) ^ 2

theorem mem_primesThrough {B p : ℕ} :
    p ∈ primesThrough B ↔ p.Prime ∧ p ≤ B := by
  simp only [primesThrough, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hB⟩, hp⟩; exact ⟨hp, hB⟩
  · rintro ⟨hp, hB⟩; exact ⟨⟨hp.two_le, hB⟩, hp⟩

theorem mem_orderedPrimePairs {B : ℕ} {z : ℕ × ℕ} :
    z ∈ orderedPrimePairs B ↔ z.1.Prime ∧ z.1 ≤ B ∧
      z.2.Prime ∧ z.2 ≤ B ∧ z.1 ≤ z.2 := by
  simp only [orderedPrimePairs, mem_filter, mem_product, mem_primesThrough]
  tauto

theorem ordered_prime_product_unique {p q r s : ℕ}
    (hp : p.Prime) (_hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≤ q) (hrs : r ≤ s) (he : p * q = r * s) : p = r ∧ q = s := by
  have hdiv : p ∣ r * s := he ▸ dvd_mul_right p q
  rcases hp.dvd_mul.mp hdiv with hpr | hps
  · have hpe : p = r := (Nat.dvd_prime hr).mp hpr |>.resolve_left hp.ne_one
    have hqe : q = s := by rw [← hpe] at he; exact Nat.eq_of_mul_eq_mul_left hp.pos he
    exact ⟨hpe, hqe⟩
  · have hpe : p = s := (Nat.dvd_prime hs).mp hps |>.resolve_left hp.ne_one
    have hqe : q = r := by
      rw [← hpe, mul_comm r p] at he
      exact Nat.eq_of_mul_eq_mul_left hp.pos he
    have hpq' : p = q := by omega
    constructor <;> omega

theorem pairValue_injective (B : ℕ) : Set.InjOn pairValue (orderedPrimePairs B) := by
  intro z hz z' hz' he
  obtain ⟨hp, _, hq, _, hpq⟩ := mem_orderedPrimePairs.mp hz
  obtain ⟨hr, _, hs, _, hrs⟩ := mem_orderedPrimePairs.mp hz'
  have hh := ordered_prime_product_unique hp hq hr hs hpq hrs he
  exact Prod.ext hh.1 hh.2

theorem prime_not_prime_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ¬ (p * q).Prime := by simp [Nat.prime_mul_iff, hp.ne_one, hq.ne_one]

theorem cofactor_union_disjoint (B : ℕ) :
    Disjoint (primesThrough B) ((orderedPrimePairs B).image pairValue) := by
  apply Finset.disjoint_left.mpr
  intro n hn hpairs
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hpairs
  have hzp := mem_orderedPrimePairs.mp hz
  have hnp := (mem_primesThrough.mp hn).1
  exact prime_not_prime_product hzp.1 hzp.2.2.1 (by simpa [← he, pairValue] using hnp)

theorem omega_prime_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    omega (p * q) = 2 := by
  have hl := (Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero).length_eq
  simpa [omega, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq] using hl

theorem rankTwoCofactors_rank {B h : ℕ} (hh : h ∈ rankTwoCofactors B) :
    omega h = 1 ∨ omega h = 2 := by
  rcases Finset.mem_union.mp hh with hp | hpq
  · left
    simp [omega, Nat.primeFactorsList_prime (mem_primesThrough.mp hp).1]
  · right
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hpq
    have hp := mem_orderedPrimePairs.mp hz
    exact omega_prime_product hp.1 hp.2.2.1

theorem diagonal_prime_square_kept {B p : ℕ} (hp : p ∈ primesThrough B) :
    p ^ 2 ∈ rankTwoCofactors B := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  refine ⟨(p, p), ?_, ?_⟩
  · simp [orderedPrimePairs, hp]
  · simp [pairValue, pow_two]

/-- Converse on the actual multiset, rather than a free representation
hypothesis: all rank-one/two cofactor integers have a unique ordered product. -/
theorem rankTwoCofactors_of_actual_multiset {B h : ℕ} (hh0 : h ≠ 0)
    (hrank : omega h = 1 ∨ omega h = 2)
    (hbound : ∀ p ∈ h.primeFactorsList, p ≤ B) : h ∈ rankTwoCofactors B := by
  rcases hrank with hlen | hlen
  · obtain ⟨p, hl⟩ := List.length_eq_one.mp hlen
    have hpm : p ∈ h.primeFactorsList := by simp [hl]
    have hp := Nat.prime_of_mem_primeFactorsList hpm
    have hpB := hbound p hpm
    have hprod := Nat.prod_primeFactorsList hh0
    rw [hl, List.prod_singleton] at hprod
    apply Finset.mem_union.mpr
    left
    rw [← hprod]
    exact mem_primesThrough.mpr ⟨hp, hpB⟩
  · obtain ⟨p, q, hl⟩ := List.length_eq_two.mp hlen
    have hpm : p ∈ h.primeFactorsList := by simp [hl]
    have hqm : q ∈ h.primeFactorsList := by simp [hl]
    have hp := Nat.prime_of_mem_primeFactorsList hpm
    have hq := Nat.prime_of_mem_primeFactorsList hqm
    have hpB := hbound p hpm
    have hqB := hbound q hqm
    have hprod := Nat.prod_primeFactorsList hh0
    have hprod' : p * q = h := by simpa [hl] using hprod
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    by_cases hle : p ≤ q
    · exact ⟨(p, q), mem_orderedPrimePairs.mpr ⟨hp, hpB, hq, hqB, hle⟩, hprod'⟩
    · exact ⟨(q, p), mem_orderedPrimePairs.mpr
        ⟨hq, hqB, hp, hpB, by omega⟩, by simpa [pairValue, mul_comm] using hprod'⟩

theorem rankTwoCofactors_two {B h : ℕ} (hh : h ∈ rankTwoCofactors B) : 2 ≤ h := by
  rcases Finset.mem_union.mp hh with hp | hpq
  · exact (mem_primesThrough.mp hp).1.two_le
  · obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hpq
    have hp := mem_orderedPrimePairs.mp hz
    dsimp only [pairValue] at he
    nlinarith [hp.1.two_le, hp.2.2.1.two_le]

/-- The cut family is exactly the finite interval selected by actual Omega. -/
theorem cut_cofactors_eq_actual_omega (B : ℕ) :
    (rankTwoCofactors B).filter (fun h => h ≤ B) =
      (Icc 2 B).filter (fun h => omega h = 1 ∨ omega h = 2) := by
  ext h
  constructor
  · intro hh
    obtain ⟨hmem, hB⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨rankTwoCofactors_two hmem, hB⟩, rankTwoCofactors_rank hmem⟩
  · intro hh
    obtain ⟨hI, hr⟩ := Finset.mem_filter.mp hh
    obtain ⟨h2, hB⟩ := Finset.mem_Icc.mp hI
    apply Finset.mem_filter.mpr
    refine ⟨rankTwoCofactors_of_actual_multiset (by omega) hr ?_, hB⟩
    intro p hp
    exact (Nat.le_of_mem_primeFactorsList hp).trans hB

/-- Direct application to the genuine cofactor extracted from a resource of
rank two or three; neither its prime representation nor its rank is assumed
as a free cofactor profile. -/
theorem actual_terminal_cofactor_mem_cut {B n : ℕ} (hn : 2 ≤ n)
    (hrank : omega n = 2 ∨ omega n = 3) (hcut : cofactor n ≤ B) :
    cofactor n ∈ (rankTwoCofactors B).filter (fun h => h ≤ B) := by
  have hOmega := omega_terminal hn
  have hcofactorRank : omega (cofactor n) = 1 ∨ omega (cofactor n) = 2 := by omega
  apply Finset.mem_filter.mpr
  refine ⟨rankTwoCofactors_of_actual_multiset (cofactor_pos hn).ne' hcofactorRank ?_, hcut⟩
  intro p hp
  exact (Nat.le_of_mem_primeFactorsList hp).trans hcut

/-- Ordered half of a symmetric product sum; equality contributes twice and
therefore yields the diagonal correction. -/
theorem unordered_pair_moment (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ s, ∑ q ∈ s, if p ≤ q then w p * w q else 0) =
      ((∑ p ∈ s, w p) ^ 2 + ∑ p ∈ s, w p ^ 2) / 2 := by
  have hpoint : ∀ p q : ℕ,
      (if p ≤ q then w p * w q else 0) +
        (if q ≤ p then w q * w p else 0) =
      w p * w q + (if p = q then w p ^ 2 else 0) := by
    intro p q
    rcases lt_trichotomy p q with hlt | he | hgt
    · simp [hlt.le, not_le_of_gt hlt, hlt.ne]
    · subst q; simp [pow_two]
    · simp [hgt.le, not_le_of_gt hgt, hgt.ne', mul_comm]
  have hsum := congrArg (fun f : ℕ → ℕ → ℝ => ∑ p ∈ s, ∑ q ∈ s, f p q)
    (funext fun p => funext fun q => hpoint p q)
  have hswap : (∑ p ∈ s, ∑ q ∈ s, if q ≤ p then w q * w p else 0) =
      ∑ p ∈ s, ∑ q ∈ s, if p ≤ q then w p * w q else 0 := by
    exact Finset.sum_comm
  have hfull : (∑ p ∈ s, ∑ q ∈ s, w p * w q) = (∑ p ∈ s, w p) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    exact (Finset.mul_sum s (fun q => w q) (w p)).symm
  have hdiag : (∑ p ∈ s, ∑ q ∈ s, if p = q then w p ^ 2 else 0) =
      ∑ p ∈ s, w p ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hswap, hfull, hdiag] at hsum
  linarith

theorem actual_ordered_products_harmonic (B : ℕ) :
    (∑ z ∈ orderedPrimePairs B, 1 / (pairValue z : ℝ)) =
      (firstMoment B ^ 2 + secondMoment B) / 2 := by
  unfold orderedPrimePairs
  rw [Finset.sum_filter, Finset.sum_product]
  have hw := unordered_pair_moment (primesThrough B) (fun p => 1 / (p : ℝ))
  convert hw using 1
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp [pairValue, Nat.cast_mul, one_div, mul_inv, mul_comm]
  · simp [firstMoment, harmonic, secondMoment, one_div, inv_pow]

/-- H8 on the actual, unique physical integers, including all prime squares. -/
theorem rankTwoCofactorHarmonicIdentity (B : ℕ) :
    harmonic (rankTwoCofactors B) =
      firstMoment B + (firstMoment B ^ 2 + secondMoment B) / 2 := by
  unfold harmonic rankTwoCofactors
  rw [Finset.sum_union (cofactor_union_disjoint B),
    Finset.sum_image (pairValue_injective B), actual_ordered_products_harmonic]
  rfl

theorem cut_harmonic_le_uncut (B : ℕ) :
    harmonic ((rankTwoCofactors B).filter (fun h => h ≤ B)) ≤
      firstMoment B + (firstMoment B ^ 2 + secondMoment B) / 2 := by
  rw [← rankTwoCofactorHarmonicIdentity B]
  unfold harmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro h _ _
  positivity

#print axioms primesThrough
#print axioms orderedPrimePairs
#print axioms pairValue
#print axioms rankTwoCofactors
#print axioms harmonic
#print axioms firstMoment
#print axioms secondMoment
#print axioms mem_primesThrough
#print axioms mem_orderedPrimePairs
#print axioms ordered_prime_product_unique
#print axioms pairValue_injective
#print axioms prime_not_prime_product
#print axioms cofactor_union_disjoint
#print axioms omega_prime_product
#print axioms rankTwoCofactors_rank
#print axioms diagonal_prime_square_kept
#print axioms rankTwoCofactors_of_actual_multiset
#print axioms rankTwoCofactors_two
#print axioms cut_cofactors_eq_actual_omega
#print axioms actual_terminal_cofactor_mem_cut
#print axioms unordered_pair_moment
#print axioms actual_ordered_products_harmonic
#print axioms rankTwoCofactorHarmonicIdentity
#print axioms cut_harmonic_le_uncut

end
end GoldbachRound19.Harmonic
