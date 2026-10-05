import AlgebraicGoldbach.ProperBertrand
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card

/-!
Arithmetic indexing can conceal near-full prime selection despite no fixed bit.
This is a density calibration, not an admissible barrier-breaking family.
-/

namespace AlgebraicGoldbach.CoprimeDivisor

noncomputable section
open scoped BigOperators
open MvPolynomial

abbrev Index (N : ℕ) :=
  {uv : Fin (N + 1) × Fin (N + 1) //
    2 ≤ uv.1.val ∧ uv.1.val < uv.2.val ∧ Nat.Coprime uv.1.val uv.2.val}

def pairDivisors (N u v : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun d => 1 < d.val ∧ (d.val ∣ u ∨ d.val ∣ v))

def family (N : ℕ) (m : Index N) : R N ℚ :=
  ∏ d ∈ pairDivisors N m.val.1.val m.val.2.val, (1 - X d)

def NearFullPrimeSelection (N : ℕ) (x : Fin (N + 1) → ℚ) : Prop :=
  ∀ p q : Fin (N + 1), Nat.Prime p.val → Nat.Prime q.val → p ≠ q →
    x p = 1 ∨ x q = 1

def omittedPrimes (N : ℕ) (x : Fin (N + 1) → ℚ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun p => Nat.Prime p.val ∧ x p ≠ 1)

theorem nearFullPrimeSelection_iff_omitted_card_le_one {N : ℕ}
    (x : Fin (N + 1) → ℚ) :
    NearFullPrimeSelection N x ↔ (omittedPrimes N x).card ≤ 1 := by
  classical
  constructor
  · intro hx
    apply Finset.card_le_one.mpr
    intro p hp q hq
    simp only [omittedPrimes, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    by_contra hne
    rcases hx p q hp.1 hq.1 hne with hpx | hqx
    · exact hp.2 hpx
    · exact hq.2 hqx
  · intro hc p q hp hq hne
    by_cases hpx : x p = 1
    · exact Or.inl hpx
    · right
      by_contra hqx
      have hpm : p ∈ omittedPrimes N x := by simp [omittedPrimes, hp, hpx]
      have hqm : q ∈ omittedPrimes N x := by simp [omittedPrimes, hq, hqx]
      exact hne (Finset.card_le_one.mp hc p hpm q hqm)

theorem pairDivisors_prime_pair (N : ℕ) (p q : Fin (N + 1))
    (hp : Nat.Prime p.val) (hq : Nat.Prime q.val) :
    pairDivisors N p.val q.val = {p, q} := by
  classical
  ext d
  simp only [pairDivisors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, hdiv | hdiv⟩
    · have he := (hp.eq_one_or_self_of_dvd d.val hdiv).resolve_left (by omega)
      exact Or.inl (Fin.ext he)
    · have he := (hq.eq_one_or_self_of_dvd d.val hdiv).resolve_left (by omega)
      exact Or.inr (Fin.ext he)
  · rintro (rfl | rfl)
    · exact ⟨hp.one_lt, Or.inl (dvd_refl _)⟩
    · exact ⟨hq.one_lt, Or.inr (dvd_refl _)⟩

theorem family_implies_ordered_prime_pair_selected {N : ℕ}
    (x : Fin (N + 1) → ℚ) (hF : ∀ m, eval x (family N m) = 0)
    (p q : Fin (N + 1)) (hp : Nat.Prime p.val) (hq : Nat.Prime q.val)
    (hpq : p.val < q.val) : x p = 1 ∨ x q = 1 := by
  classical
  have hne : p ≠ q := by intro he; have := congrArg Fin.val he; omega
  have hval : p.val ≠ q.val := by omega
  let m : Index N := ⟨(p, q), hp.two_le, hpq, (Nat.coprime_primes hp hq).mpr hval⟩
  have h := hF m
  have he : family N m = (1 - X p) * (1 - X q) := by
    simp [family, m, pairDivisors_prime_pair N p q hp hq, hne]
  rw [he] at h
  simp only [map_mul, map_sub, map_one, eval_X] at h
  rcases mul_eq_zero.mp h with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft).symm
  · exact Or.inr (sub_eq_zero.mp hright).symm

theorem family_implies_nearFullPrimeSelection {N : ℕ}
    (x : Fin (N + 1) → ℚ) (hF : ∀ m, eval x (family N m) = 0) :
    NearFullPrimeSelection N x := by
  intro p q hp hq hne
  have hval : p.val ≠ q.val := by
    intro he
    exact hne (Fin.ext he)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact family_implies_ordered_prime_pair_selected x hF p q hp hq hlt
  · exact (family_implies_ordered_prime_pair_selected x hF q p hq hp hgt).symm

theorem nearFullPrimeSelection_implies_family {N : ℕ}
    (x : Fin (N + 1) → ℚ) (hx : NearFullPrimeSelection N x) (m : Index N) :
    eval x (family N m) = 0 := by
  classical
  have hm := m.property
  let p : Fin (N + 1) := ⟨Nat.minFac m.val.1.val,
    lt_of_le_of_lt (Nat.minFac_le (by omega)) m.val.1.isLt⟩
  let q : Fin (N + 1) := ⟨Nat.minFac m.val.2.val,
    lt_of_le_of_lt (Nat.minFac_le (by omega)) m.val.2.isLt⟩
  have hp : Nat.Prime p.val := Nat.minFac_prime (by omega)
  have hq : Nat.Prime q.val := Nat.minFac_prime (by omega)
  have hpu : p.val ∣ m.val.1.val := Nat.minFac_dvd _
  have hqv : q.val ∣ m.val.2.val := Nat.minFac_dvd _
  have hne : p ≠ q := by
    intro he
    have hpv : p.val ∣ m.val.2.val := by
      rw [congrArg Fin.val he]
      exact hqv
    have hone := Nat.eq_one_of_dvd_coprimes hm.2.2 hpu hpv
    exact hp.ne_one hone
  have hip : p ∈ pairDivisors N m.val.1.val m.val.2.val := by
    simp only [pairDivisors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.one_lt, Or.inl hpu⟩
  have hiq : q ∈ pairDivisors N m.val.1.val m.val.2.val := by
    simp only [pairDivisors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hq.one_lt, Or.inr hqv⟩
  simp only [family, map_prod]
  rcases hx p q hp hq hne with hxp | hxq
  · apply Finset.prod_eq_zero (i := p) hip
    simp [hxp]
  · apply Finset.prod_eq_zero (i := q) hiq
    simp [hxq]

theorem family_iff_nearFullPrimeSelection {N : ℕ} (x : Fin (N + 1) → ℚ) :
    (∀ m, eval x (family N m) = 0) ↔ NearFullPrimeSelection N x :=
  ⟨family_implies_nearFullPrimeSelection x, nearFullPrimeSelection_implies_family x⟩

theorem family_iff_at_most_one_omitted_prime {N : ℕ} (x : Fin (N + 1) → ℚ) :
    (∀ m, eval x (family N m) = 0) ↔ (omittedPrimes N x).card ≤ 1 :=
  (family_iff_nearFullPrimeSelection x).trans
    (nearFullPrimeSelection_iff_omitted_card_le_one x)

theorem primePoint_family (N : ℕ) (m : Index N) :
    eval (primePoint N ℚ) (family N m) = 0 := by
  apply nearFullPrimeSelection_implies_family
  intro p q hp hq hne
  exact Or.inl (by simp [primePoint, hp])

theorem onePoint_family (N : ℕ) (m : Index N) :
    eval (ProperBertrand.onePoint N) (family N m) = 0 := by
  apply nearFullPrimeSelection_implies_family
  intro p q hp hq hne
  exact Or.inl rfl

theorem exceptPoint_family (N : ℕ) (target : Fin (N + 1)) (m : Index N) :
    eval (ProperBertrand.exceptPoint N target) (family N m) = 0 := by
  apply nearFullPrimeSelection_implies_family
  intro p q hp hq hne
  by_cases hpt : p = target
  · right
    have hqt : q ≠ target := by intro he; exact hne (hpt.trans he.symm)
    simp [ProperBertrand.exceptPoint, hqt]
  · left
    simp [ProperBertrand.exceptPoint, hpt]

theorem family_does_not_pin_any_coordinate (N : ℕ) (target : Fin (N + 1)) :
    (∀ m, eval (ProperBertrand.exceptPoint N target) (family N m) = 0) ∧
    (∀ i, eval (ProperBertrand.exceptPoint N target) (booleanConstraint i) = 0) ∧
    ProperBertrand.exceptPoint N target target = 0 ∧
    (∀ m, eval (ProperBertrand.onePoint N) (family N m) = 0) ∧
    (∀ i, eval (ProperBertrand.onePoint N) (booleanConstraint i) = 0) ∧
    ProperBertrand.onePoint N target = 1 := by
  exact ⟨exceptPoint_family N target, ProperBertrand.exceptPoint_boolean N target,
    by simp [ProperBertrand.exceptPoint], onePoint_family N,
    ProperBertrand.onePoint_boolean N, rfl⟩

theorem family_has_second_boolean_solution (N : ℕ) :
    (∀ m, eval (primePoint N ℚ) (family N m) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ m, eval (ProperBertrand.onePoint N) (family N m) = 0) ∧
    (∀ i, eval (ProperBertrand.onePoint N) (booleanConstraint i) = 0) ∧
    ProperBertrand.onePoint N ≠ primePoint N ℚ :=
  ⟨primePoint_family N, primePoint_boolean, onePoint_family N,
    ProperBertrand.onePoint_boolean N, ProperBertrand.onePoint_differs_from_primePoint N⟩

end
end AlgebraicGoldbach.CoprimeDivisor
