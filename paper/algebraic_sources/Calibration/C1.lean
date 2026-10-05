import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! C1 over ℚ, with the cardinality parameter explicitly natural. -/
namespace AlgebraicGoldbach.Calibration

open Finset

/-- All prime coordinates in the closed interval `[0,N]`. -/
def primes (N : ℕ) : Finset ℕ := (range (N + 1)).filter Nat.Prime

/-- The unique lower representative of each unordered prime pair, including loops. -/
def pairRepresentatives (N : ℕ) : Finset ℕ :=
  (primes N).filter (fun p => Nat.Prime (N - p) ∧ p ≤ N - p)

/-- Unordered pairs are finite sets; a loop is the singleton `{p}`. -/
def unorderedPrimePairs (N : ℕ) : Finset (Finset ℕ) :=
  (pairRepresentatives N).image (fun p => {p, N - p})

def pi (N : ℕ) : ℕ := (primes N).card

def r (N : ℕ) : ℕ := (unorderedPrimePairs N).card

/-- Independence forbids both selected endpoints, including selection of a loop. -/
def Independent (N : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ primes N ∧ ∀ p ∈ S, N - p ∉ S

def upperEndpoints (N : ℕ) : Finset ℕ :=
  (pairRepresentatives N).image (fun p => N - p)

def maximumSupport (N : ℕ) : Finset ℕ := primes N \ upperEndpoints N

@[simp] theorem mem_primes {N p : ℕ} : p ∈ primes N ↔ p ≤ N ∧ Nat.Prime p := by
  simp [primes, Nat.lt_succ_iff]

@[simp] theorem mem_pairRepresentatives {N p : ℕ} :
    p ∈ pairRepresentatives N ↔ p ≤ N ∧ Nat.Prime p ∧
      Nat.Prime (N - p) ∧ p ≤ N - p := by
  simp only [pairRepresentatives, mem_filter, mem_primes]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hq, hle⟩
    exact ⟨hpN, hp, hq, hle⟩
  · rintro ⟨hpN, hp, hq, hle⟩
    exact ⟨⟨hpN, hp⟩, hq, hle⟩

theorem pair_sets_injective (N : ℕ) :
    Set.InjOn (fun p => ({p, N - p} : Finset ℕ)) ↑(pairRepresentatives N) := by
  intro p hp q hq heq
  change ({p, N - p} : Finset ℕ) = {q, N - q} at heq
  have hp' := (mem_pairRepresentatives.mp hp).2.2.2
  have hq' := (mem_pairRepresentatives.mp hq).2.2.2
  have hpq : p = q ∨ p = N - q := by
    have : p ∈ ({q, N - q} : Finset ℕ) := by rw [← heq]; simp
    simpa using this
  have hqp : q = p ∨ q = N - p := by
    have : q ∈ ({p, N - p} : Finset ℕ) := by rw [heq]; simp
    simpa using this
  rcases hpq with h | h
  · exact h
  · rcases hqp with h' | h'
    · exact h'.symm
    · omega

/-- These are precisely the unordered prime decompositions of `N`, including equal primes. -/
theorem mem_unorderedPrimePairs {N : ℕ} {E : Finset ℕ} :
    E ∈ unorderedPrimePairs N ↔
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N ∧ E = {p, q} := by
  constructor
  · intro hE
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hE
    have hp' := mem_pairRepresentatives.mp hp
    exact ⟨p, N - p, hp'.2.1, hp'.2.2.1, by omega, rfl⟩
  · rintro ⟨p, q, hp, hq, hsum, rfl⟩
    by_cases hle : p ≤ q
    · apply mem_image.mpr
      have hqeq : N - p = q := by omega
      refine ⟨p, ?_, ?_⟩
      · apply mem_pairRepresentatives.mpr
        simpa only [hqeq] using (show p ≤ N ∧ Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q from
          ⟨by omega, hp, hq, hle⟩)
      · simp [hqeq]
    · apply mem_image.mpr
      have hpeq : N - q = p := by omega
      refine ⟨q, ?_, ?_⟩
      · apply mem_pairRepresentatives.mpr
        simpa only [hpeq] using (show q ≤ N ∧ Nat.Prime q ∧ Nat.Prime p ∧ q ≤ p from
          ⟨by omega, hq, hp, by omega⟩)
      · simp [hpeq, pair_comm]

/-- The custom finite-set count agrees with Mathlib's standard prime-counting function. -/
theorem pi_eq_primeCounting (N : ℕ) : pi N = N.primeCounting := by
  simp only [pi, primes, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- The representative count is exactly the number of unordered pairs, loops included. -/
theorem r_eq_card_representatives (N : ℕ) : r N = (pairRepresentatives N).card := by
  exact card_image_of_injOn (pair_sets_injective N)

theorem upperEndpoints_subset (N : ℕ) : upperEndpoints N ⊆ primes N := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  have hp' := mem_pairRepresentatives.mp hp
  exact mem_primes.mpr ⟨Nat.sub_le _ _, hp'.2.2.1⟩

theorem upperEndpoints_card (N : ℕ) : (upperEndpoints N).card = r N := by
  rw [r_eq_card_representatives]
  apply card_image_of_injOn
  intro p hp q hq heq
  change N - p = N - q at heq
  have hp' := (mem_pairRepresentatives.mp hp).1
  have hq' := (mem_pairRepresentatives.mp hq).1
  omega

theorem maximumSupport_card (N : ℕ) : (maximumSupport N).card = pi N - r N := by
  rw [maximumSupport, card_sdiff (upperEndpoints_subset N), upperEndpoints_card, pi]

theorem maximumSupport_independent (N : ℕ) : Independent N (maximumSupport N) := by
  constructor
  · exact sdiff_subset
  · intro p hp hq
    obtain ⟨hpP, hpU⟩ := mem_sdiff.mp hp
    obtain ⟨hqP, hqU⟩ := mem_sdiff.mp hq
    have hp' := mem_primes.mp hpP
    have hq' := mem_primes.mp hqP
    by_cases hle : p ≤ N - p
    · apply hqU
      apply mem_image.mpr
      exact ⟨p, mem_pairRepresentatives.mpr ⟨hp'.1, hp'.2, hq'.2, hle⟩, rfl⟩
    · apply hpU
      apply mem_image.mpr
      have hinv : N - (N - p) = p := by omega
      refine ⟨N - p, ?_, hinv⟩
      apply mem_pairRepresentatives.mpr
      simp only [hinv]
      exact ⟨hq'.1, hq'.2, hp'.2, by omega⟩

/-- Each disjoint pair forces a distinct omitted prime coordinate. -/
theorem independent_card_le {N : ℕ} {S : Finset ℕ} (hS : Independent N S) :
    S.card ≤ pi N - r N := by
  classical
  let f : ℕ → ℕ := fun p => if p ∈ S then N - p else p
  have hfmem : ∀ p ∈ pairRepresentatives N, f p ∈ primes N \ S := by
    intro p hp
    have hp' := mem_pairRepresentatives.mp hp
    by_cases hs : p ∈ S
    · simp only [f, if_pos hs]
      exact mem_sdiff.mpr ⟨mem_primes.mpr ⟨Nat.sub_le _ _, hp'.2.2.1⟩, hS.2 p hs⟩
    · simp only [f, if_neg hs]
      exact mem_sdiff.mpr ⟨mem_primes.mpr ⟨hp'.1, hp'.2.1⟩, hs⟩
  have hfinj : Set.InjOn f ↑(pairRepresentatives N) := by
    intro p hp q hq heq
    have hp' := mem_pairRepresentatives.mp hp
    have hq' := mem_pairRepresentatives.mp hq
    dsimp [f] at heq
    split_ifs at heq <;> omega
  have hbound : (pairRepresentatives N).card ≤ (primes N \ S).card :=
    card_le_card_of_injOn f hfmem hfinj
  have hcards := card_sdiff_add_card_eq_card hS.1
  rw [← r_eq_card_representatives] at hbound
  unfold pi
  omega

/-- Exact attainable cardinalities for the prime matching graph. -/
theorem independent_exists_iff (N m : ℕ) :
    (∃ S : Finset ℕ, Independent N S ∧ S.card = m) ↔ m ≤ pi N - r N := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact independent_card_le hS
  · intro hm
    rw [← maximumSupport_card] at hm
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hm
    refine ⟨S, ⟨?_, ?_⟩, hcard⟩
    · exact Subset.trans hS (maximumSupport_independent N).1
    · intro p hp hq
      exact (maximumSupport_independent N).2 p (hS hp) (hS hq)




/-- The Goldbach polynomial evaluated on the finite coordinate interval. -/
def g (N : ℕ) (x : ℕ → ℚ) : ℚ := ∑ p ∈ range (N + 1), x p * x (N - p)

/-- The count system includes Boolean equations and all nonprime zero coordinates. -/
def D (N m : ℕ) (x : ℕ → ℚ) : Prop :=
  (∀ p ≤ N, x p ^ 2 - x p = 0) ∧
  (∀ p ≤ N, ¬ Nat.Prime p → x p = 0) ∧
  (∑ p ∈ range (N + 1), x p) = (m : ℚ)

def support (N : ℕ) (x : ℕ → ℚ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => x p = 1)

theorem boolean_iff (a : ℚ) : a ^ 2 - a = 0 ↔ a = 0 ∨ a = 1 := by
  rw [show a ^ 2 - a = a * (a - 1) by ring, mul_eq_zero, sub_eq_zero]

@[simp] theorem mem_support {N p : ℕ} {x : ℕ → ℚ} :
    p ∈ support N x ↔ p ≤ N ∧ x p = 1 := by
  simp [support, Nat.lt_succ_iff]

theorem support_subset_primes {N : ℕ} {x : ℕ → ℚ}
    (hz : ∀ p ≤ N, ¬ Nat.Prime p → x p = 0) : support N x ⊆ primes N := by
  intro p hp
  have hp' := mem_support.mp hp
  refine mem_primes.mpr ⟨hp'.1, ?_⟩
  by_contra hn
  have hzero := hz p hp'.1 hn
  rw [hp'.2] at hzero
  norm_num at hzero

theorem sum_eq_support_card {N : ℕ} {x : ℕ → ℚ}
    (hb : ∀ p ≤ N, x p ^ 2 - x p = 0) :
    (∑ p ∈ range (N + 1), x p) = ((support N x).card : ℚ) := by
  rw [support, Finset.natCast_card_filter]
  apply sum_congr rfl
  intro p hp
  rcases (boolean_iff (x p)).mp (hb p (Nat.le_of_lt_succ (mem_range.mp hp))) with h | h
  · simp [h]
  · simp [h]

/-- Nonnegative Boolean terms make aggregate vanishing equivalent to independence. -/
theorem g_zero_iff_independent {N : ℕ} {x : ℕ → ℚ}
    (hb : ∀ p ≤ N, x p ^ 2 - x p = 0)
    (hz : ∀ p ≤ N, ¬ Nat.Prime p → x p = 0) :
    g N x = 0 ↔ Independent N (support N x) := by
  have hnonneg : ∀ p ≤ N, 0 ≤ x p := by
    intro p hp
    rcases (boolean_iff (x p)).mp (hb p hp) with h | h <;> simp [h]
  have hterms : ∀ p ∈ range (N + 1), 0 ≤ x p * x (N - p) := by
    intro p hp
    exact mul_nonneg (hnonneg p (Nat.le_of_lt_succ (mem_range.mp hp)))
      (hnonneg (N - p) (Nat.sub_le _ _))
  constructor
  · intro hg
    refine ⟨support_subset_primes hz, ?_⟩
    intro p hp hq
    have hp' := mem_support.mp hp
    have hq' := mem_support.mp hq
    have hterm := (sum_eq_zero_iff_of_nonneg hterms).mp hg p
      (mem_range.mpr (Nat.lt_succ_of_le hp'.1))
    rw [hp'.2, hq'.2] at hterm
    norm_num at hterm
  · intro hS
    apply sum_eq_zero
    intro p hp
    have hpN := Nat.le_of_lt_succ (mem_range.mp hp)
    rcases (boolean_iff (x p)).mp (hb p hpN) with h | h
    · simp [h]
    · have hqnot := hS.2 p (mem_support.mpr ⟨hpN, h⟩)
      have hq0 : x (N - p) = 0 := by
        rcases (boolean_iff (x (N - p))).mp (hb (N - p) (Nat.sub_le _ _)) with hq | hq
        · exact hq
        · exact False.elim (hqnot (mem_support.mpr ⟨Nat.sub_le _ _, hq⟩))
      simp [hq0]

/-- The characteristic vector associated to a finite support. -/
def characteristic (S : Finset ℕ) (p : ℕ) : ℚ := if p ∈ S then 1 else 0

theorem characteristic_boolean (S : Finset ℕ) (p : ℕ) :
    characteristic S p ^ 2 - characteristic S p = 0 := by
  unfold characteristic
  split_ifs <;> norm_num

theorem support_characteristic {N : ℕ} {S : Finset ℕ} (hS : S ⊆ primes N) :
    support N (characteristic S) = S := by
  ext p
  simp only [mem_support, characteristic]
  by_cases hp : p ∈ S
  · simp [hp, (mem_primes.mp (hS hp)).1]
  · simp [hp]

/-- Full C1 calibration: no parameter restriction other than `m : ℕ` is hidden. -/
theorem C1 (N m : ℕ) :
    (∃ x : ℕ → ℚ, D N m x ∧ g N x = 0) ↔ m ≤ pi N - r N := by
  constructor
  · rintro ⟨x, hx, hg⟩
    have hS := (g_zero_iff_independent hx.1 hx.2.1).mp hg
    have hcard : (support N x).card = m := by
      have hcast : ((support N x).card : ℚ) = (m : ℚ) := by
        rw [← sum_eq_support_card hx.1]
        exact hx.2.2
      exact Nat.cast_inj.mp hcast
    rw [← hcard]
    exact independent_card_le hS
  · intro hm
    obtain ⟨S, hS, hcard⟩ := (independent_exists_iff N m).mpr hm
    have hb : ∀ p ≤ N, characteristic S p ^ 2 - characteristic S p = 0 :=
      fun p _ => characteristic_boolean S p
    have hz : ∀ p ≤ N, ¬ Nat.Prime p → characteristic S p = 0 := by
      intro p _ hn
      have hp : p ∉ S := by
        intro hp
        exact hn (mem_primes.mp (hS.1 hp)).2
      simp [characteristic, hp]
    refine ⟨characteristic S, ⟨hb, hz, ?_⟩, ?_⟩
    · rw [sum_eq_support_card hb, support_characteristic hS.1, hcard]
    · apply (g_zero_iff_independent hb hz).mpr
      rw [support_characteristic hS.1]
      exact hS

/-- Standard-notation version of full C1. -/
theorem C1_primeCounting (N m : ℕ) :
    (∃ x : ℕ → ℚ, D N m x ∧ g N x = 0) ↔ m ≤ N.primeCounting - r N := by
  rw [C1, pi_eq_primeCounting]

theorem r_le_pi (N : ℕ) : r N ≤ pi N := by
  rw [← upperEndpoints_card]
  exact card_le_card (upperEndpoints_subset N)

/-- At the full prime count, excluding all pseudo-solutions is exactly the existence of a pair. -/
theorem no_pseudo_solution_at_full_count_iff (N : ℕ) :
    (¬ ∃ x : ℕ → ℚ, D N (pi N) x ∧ g N x = 0) ↔ 1 ≤ r N := by
  rw [C1]
  have hr := r_le_pi N
  omega

/-- A nonempty pair set is the usual prime-sum assertion for this `N`. -/
theorem r_positive_iff (N : ℕ) :
    1 ≤ r N ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  rw [show 1 ≤ r N ↔ 0 < (unorderedPrimePairs N).card by rfl, card_pos]
  constructor
  · rintro ⟨E, hE⟩
    obtain ⟨p, q, hp, hq, hsum, _⟩ := mem_unorderedPrimePairs.mp hE
    exact ⟨p, q, hp, hq, hsum⟩
  · rintro ⟨p, q, hp, hq, hsum⟩
    exact ⟨{p, q}, mem_unorderedPrimePairs.mpr ⟨p, q, hp, hq, hsum, rfl⟩⟩

/-- The true prime indicator is always a solution before adding `g=0`. -/
theorem D_true_prime_indicator (N : ℕ) :
    D N (pi N) (fun p => if Nat.Prime p then 1 else 0) := by
  have hb : ∀ p ≤ N, (if Nat.Prime p then (1 : ℚ) else 0) ^ 2 -
      (if Nat.Prime p then (1 : ℚ) else 0) = 0 := by
    intro p _
    split_ifs <;> norm_num
  refine ⟨hb, ?_, ?_⟩
  · intro p _ hp
    simp [hp]
  · rw [sum_eq_support_card hb]
    have hsupport : support N (fun p => if Nat.Prime p then 1 else 0) = primes N := by
      ext p
      simp [mem_support, mem_primes]
    rw [hsupport]
    rfl

/-- The full count pins every coordinate in `[0,N]` to the true prime bit. -/
theorem D_full_count_pins {N : ℕ} {x : ℕ → ℚ} (hx : D N (pi N) x) :
    ∀ p ≤ N, x p = if Nat.Prime p then 1 else 0 := by
  have hcard : (support N x).card = (primes N).card := by
    have hcast : ((support N x).card : ℚ) = ((primes N).card : ℚ) := by
      rw [← sum_eq_support_card hx.1]
      exact hx.2.2
    exact Nat.cast_inj.mp hcast
  have heq : support N x = primes N :=
    eq_of_subset_of_card_le (support_subset_primes hx.2.1) hcard.ge
  intro p hpN
  by_cases hp : Nat.Prime p
  · have hmem : p ∈ support N x := heq.symm ▸ (mem_primes.mpr ⟨hpN, hp⟩)
    simp only [if_pos hp]
    exact (mem_support.mp hmem).2
  · simp only [if_neg hp]
    exact hx.2.1 p hpN hp

#print axioms C1
#print axioms C1_primeCounting
#print axioms no_pseudo_solution_at_full_count_iff
#print axioms D_full_count_pins
#print axioms g_zero_iff_independent
#print axioms r_eq_card_representatives

end AlgebraicGoldbach.Calibration



