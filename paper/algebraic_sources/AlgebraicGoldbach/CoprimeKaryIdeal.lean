import AlgebraicGoldbach.CoprimeDivisor
import Mathlib.RingTheory.Ideal.Span

/-!
Exact ordinary-polynomial ideal reduction of arithmetic k-ary divisor coverage.
This classifies a density control; it is not a Goldbach certificate or an
admissible barrier-breaking family. Self-divisors are included, including k = 0.
-/

namespace AlgebraicGoldbach.CoprimeKaryIdeal

noncomputable section
open scoped BigOperators
open MvPolynomial

def ArithmeticAllowed {N : ℕ} (k : ℕ) (S : Finset (Fin (N + 1))) : Prop :=
  S.card = k ∧ (∀ u ∈ S, 2 ≤ u.val) ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Nat.Coprime u.val v.val

def PrimeAllowed {N : ℕ} (k : ℕ) (T : Finset (Fin (N + 1))) : Prop :=
  T.card = k ∧ ∀ p ∈ T, Nat.Prime p.val

abbrev ArithmeticIndex (N k : ℕ) :=
  {S : Finset (Fin (N + 1)) // ArithmeticAllowed k S}

abbrev PrimeIndex (N k : ℕ) :=
  {T : Finset (Fin (N + 1)) // PrimeAllowed k T}

def divisors (N : ℕ) (S : Finset (Fin (N + 1))) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun d => 1 < d.val ∧ ∃ u ∈ S, d.val ∣ u.val)

def product (N : ℕ) (T : Finset (Fin (N + 1))) : R N ℚ :=
  ∏ d ∈ T, (1 - X d)

def arithmeticFamily (N k : ℕ) (S : ArithmeticIndex N k) : R N ℚ :=
  product N (divisors N S.val)

def primeFamily (N k : ℕ) (T : PrimeIndex N k) : R N ℚ :=
  product N T.val

def arithmeticIdeal (N k : ℕ) : Ideal (R N ℚ) :=
  Ideal.span (Set.range (arithmeticFamily N k))

def primeIdeal (N k : ℕ) : Ideal (R N ℚ) :=
  Ideal.span (Set.range (primeFamily N k))

def leastFactor {N : ℕ} (u : Fin (N + 1)) : Fin (N + 1) :=
  if h : 2 ≤ u.val then
    ⟨Nat.minFac u.val, lt_of_le_of_lt (Nat.minFac_le (by omega)) u.isLt⟩
  else u

theorem leastFactor_val {N : ℕ} (u : Fin (N + 1)) (hu : 2 ≤ u.val) :
    (leastFactor u).val = Nat.minFac u.val := by
  simp [leastFactor, hu]

theorem leastFactor_prime {N : ℕ} (u : Fin (N + 1)) (hu : 2 ≤ u.val) :
    Nat.Prime (leastFactor u).val := by
  rw [leastFactor_val u hu]
  exact Nat.minFac_prime (by omega)

theorem leastFactor_dvd {N : ℕ} (u : Fin (N + 1)) (hu : 2 ≤ u.val) :
    (leastFactor u).val ∣ u.val := by
  rw [leastFactor_val u hu]
  exact Nat.minFac_dvd _

theorem leastFactor_injective_on {N k : ℕ} (S : Finset (Fin (N + 1)))
    (hS : ArithmeticAllowed k S) :
    Set.InjOn (leastFactor (N := N)) (S : Set (Fin (N + 1))) := by
  intro u hu v hv he
  by_contra hne
  have hp := leastFactor_prime u (hS.2.1 u hu)
  have hdu := leastFactor_dvd u (hS.2.1 u hu)
  have hdv : (leastFactor u).val ∣ v.val := by
    rw [he]
    exact leastFactor_dvd v (hS.2.1 v hv)
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (hS.2.2 u hu v hv hne) hdu hdv)

theorem leastFactor_image_primeAllowed {N k : ℕ} (S : Finset (Fin (N + 1)))
    (hS : ArithmeticAllowed k S) : PrimeAllowed k (S.image leastFactor) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_iff.mpr (leastFactor_injective_on S hS), hS.1]
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact leastFactor_prime u (hS.2.1 u hu)

theorem leastFactor_image_subset_divisors {N k : ℕ}
    (S : Finset (Fin (N + 1))) (hS : ArithmeticAllowed k S) :
    S.image leastFactor ⊆ divisors N S := by
  classical
  intro p hp
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  simp only [divisors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(leastFactor_prime u (hS.2.1 u hu)).one_lt,
    u, hu, leastFactor_dvd u (hS.2.1 u hu)⟩

theorem primeAllowed_arithmeticAllowed {N k : ℕ}
    (T : Finset (Fin (N + 1))) (hT : PrimeAllowed k T) :
    ArithmeticAllowed k T := by
  refine ⟨hT.1, ?_, ?_⟩
  · intro p hp
    exact (hT.2 p hp).two_le
  · intro p hp q hq hne
    apply (Nat.coprime_primes (hT.2 p hp) (hT.2 q hq)).mpr
    intro he
    exact hne (Fin.ext he)

theorem prime_divisors_eq {N k : ℕ} (T : Finset (Fin (N + 1)))
    (hT : PrimeAllowed k T) : divisors N T = T := by
  classical
  ext d
  simp only [divisors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hd, u, hu, hdu⟩
    have he := ((hT.2 u hu).eq_one_or_self_of_dvd d.val hdu).resolve_left (by omega)
    exact (Fin.ext he) ▸ hu
  · intro hd
    exact ⟨(hT.2 d hd).one_lt, d, hd, dvd_refl _⟩

theorem arithmetic_factorization {N k : ℕ} (S : Finset (Fin (N + 1)))
    (hS : ArithmeticAllowed k S) :
    product N (divisors N S) =
      product N (S.image leastFactor) *
        product N (divisors N S \ S.image leastFactor) := by
  classical
  unfold product
  rw [mul_comm]
  exact (Finset.prod_sdiff (leastFactor_image_subset_divisors S hS)).symm

theorem arithmeticIdeal_eq_primeIdeal (N k : ℕ) :
    arithmeticIdeal N k = primeIdeal N k := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨S, rfl⟩
    let T : PrimeIndex N k :=
      ⟨S.val.image leastFactor, leastFactor_image_primeAllowed S.val S.property⟩
    have hT : primeFamily N k T ∈ primeIdeal N k :=
      Ideal.subset_span ⟨T, rfl⟩
    rw [arithmeticFamily, arithmetic_factorization S.val S.property]
    exact Ideal.mul_mem_right _ _ hT
  · apply Ideal.span_le.mpr
    rintro f ⟨T, rfl⟩
    let S : ArithmeticIndex N k :=
      ⟨T.val, primeAllowed_arithmeticAllowed T.val T.property⟩
    have he : arithmeticFamily N k S = primeFamily N k T := by
      simp only [arithmeticFamily, primeFamily, S,
        prime_divisors_eq T.val T.property]
    rw [← he]
    exact Ideal.subset_span ⟨S, rfl⟩

end
end AlgebraicGoldbach.CoprimeKaryIdeal
