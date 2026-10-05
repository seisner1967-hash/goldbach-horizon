import AlgebraicGoldbach.BertrandFamily
import Mathlib.Tactic.Linarith

namespace AlgebraicGoldbach.FactorCoverage

noncomputable section

open scoped BigOperators
open MvPolynomial

def properDivisors (N m : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun i => 1 < i.val ∧ i.val ∣ m ∧ i.val < m)

def factorPolynomial (N m : ℕ) : R N ℚ :=
  ∏ i ∈ properDivisors N m, (1 - X i)

def Coverage (N M : ℕ) (x : Fin (N + 1) → ℚ) : Prop :=
  ∀ m, 1 < m → m ≤ M → ¬ Nat.Prime m → eval x (factorPolynomial N m) = 0

def PrimePins (N M : ℕ) (x : Fin (N + 1) → ℚ) : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (hpN : p ≤ N), p ^ 2 ≤ M →
    x ⟨p, by omega⟩ = 1

theorem minFac_le_horizon (N M m : ℕ) (hm : 1 < m) (hmc : ¬ Nat.Prime m)
    (hmM : m ≤ M) (hMN : M ≤ N ^ 2) : Nat.minFac m ≤ N := by
  have hs := Nat.minFac_sq_le_self (by omega : 0 < m) hmc
  nlinarith

theorem primePoint_factorPolynomial (N M m : ℕ) (hMN : M ≤ N ^ 2)
    (hm : 1 < m) (hmM : m ≤ M) (hmc : ¬ Nat.Prime m) :
    eval (primePoint N ℚ) (factorPolynomial N m) = 0 := by
  let p := Nat.minFac m
  have hp : Nat.Prime p := Nat.minFac_prime (by omega : m ≠ 1)
  have hpN : p ≤ N := minFac_le_horizon N M m hm hmc hmM hMN
  let i : Fin (N + 1) := ⟨p, by omega⟩
  have hi : i ∈ properDivisors N m := by
    simp only [properDivisors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.one_lt, Nat.minFac_dvd m,
      (Nat.not_prime_iff_minFac_lt (by omega : 2 ≤ m)).mp hmc⟩
  simp only [factorPolynomial, map_prod]
  apply Finset.prod_eq_zero (i := i) hi
  simp [primePoint, i, hp]

theorem primePoint_coverage (N M : ℕ) (hMN : M ≤ N ^ 2) :
    Coverage N M (primePoint N ℚ) := by
  intro m hm hmM hmc
  exact primePoint_factorPolynomial N M m hMN hm hmM hmc

theorem properDivisors_prime_square (N p : ℕ) (hp : Nat.Prime p) (hpN : p ≤ N) :
    properDivisors N (p ^ 2) = {⟨p, by omega⟩} := by
  ext i
  simp only [properDivisors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hi1, hid, hi2⟩
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp hid
    have hc : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hc with h0 | h1 | h2
    · simp [h0] at he
      omega
    · apply Fin.ext
      simpa [h1] using he
    · simp [h2] at he
      omega
  · rintro rfl
    refine ⟨hp.one_lt, ?_, ?_⟩
    · exact ⟨p, by simp [pow_two]⟩
    · have hp2 := hp.two_le
      nlinarith

theorem coverage_implies_primePins (N M : ℕ) (x : Fin (N + 1) → ℚ)
    (hcov : Coverage N M x) : PrimePins N M x := by
  intro p hp hpN hpM
  have hp2 := hp.two_le
  have h := hcov (p ^ 2) (by nlinarith) hpM (Nat.Prime.not_prime_pow (by decide))
  rw [factorPolynomial, properDivisors_prime_square N p hp hpN] at h
  have hh : 1 - x ⟨p, by omega⟩ = 0 := by simpa using h
  exact (sub_eq_zero.mp hh).symm

theorem primePins_implies_coverage (N M : ℕ) (hMN : M ≤ N ^ 2)
    (x : Fin (N + 1) → ℚ) (hpins : PrimePins N M x) : Coverage N M x := by
  intro m hm hmM hmc
  let p := Nat.minFac m
  have hp : Nat.Prime p := Nat.minFac_prime (by omega : m ≠ 1)
  have hpN : p ≤ N := minFac_le_horizon N M m hm hmc hmM hMN
  have hpM : p ^ 2 ≤ M := (Nat.minFac_sq_le_self (by omega : 0 < m) hmc).trans hmM
  let i : Fin (N + 1) := ⟨p, by omega⟩
  have hi : i ∈ properDivisors N m := by
    simp only [properDivisors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.one_lt, Nat.minFac_dvd m,
      (Nat.not_prime_iff_minFac_lt (by omega : 2 ≤ m)).mp hmc⟩
  simp only [factorPolynomial, map_prod]
  apply Finset.prod_eq_zero (i := i) hi
  simp only [map_sub, map_one, eval_X]
  exact sub_eq_zero.mpr (hpins p hp hpN hpM).symm

theorem coverage_iff_primePins (N M : ℕ) (hMN : M ≤ N ^ 2)
    (x : Fin (N + 1) → ℚ) : Coverage N M x ↔ PrimePins N M x :=
  ⟨coverage_implies_primePins N M x, primePins_implies_coverage N M hMN x⟩

theorem square_horizon_pins_prime_coordinates (N : ℕ) (x : Fin (N + 1) → ℚ)
    (hcov : Coverage N (N ^ 2) x) (i : Fin (N + 1)) (hi : Nat.Prime i.val) :
    x i = 1 := by
  have h := coverage_implies_primePins N (N ^ 2) x hcov i.val hi (by omega)
  have hsq : i.val ^ 2 ≤ N ^ 2 := by nlinarith [i.isLt]
  exact h hsq

theorem square_horizon_and_sieve_pin_vector (N : ℕ) (x : Fin (N + 1) → ℚ)
    (hcov : Coverage N (N ^ 2) x)
    (hsieve : ∀ i, ¬ Nat.Prime i.val → x i = 0) : x = primePoint N ℚ := by
  funext i
  by_cases hi : Nat.Prime i.val
  · simpa [primePoint, hi] using square_horizon_pins_prime_coordinates N x hcov i hi
  · simpa [primePoint, hi] using hsieve i hi

theorem modelPoint_small_prime (N p : ℕ) (hp : Nat.Prime p)
    (hpN : p ≤ N) (hpH : p ≤ N / 2 - 3) : modelPoint N ⟨p, by omega⟩ = 1 := by
  have hb := high_bounds N
  have hp2 := hp.two_le
  have hs : selected N p := by
    rcases hp.eq_two_or_odd with htwo | hodd
    · exact Or.inl htwo
    · exact Or.inr (Or.inl ⟨by omega, by omega, hodd, by omega⟩)
  simp [modelPoint, bit, hs]

theorem modelPoint_coverage (N M : ℕ) (hM : M ≤ (N / 2 - 3) ^ 2) :
    Coverage N M (modelPoint N) := by
  have hh : N / 2 - 3 ≤ N := by omega
  have hMN : M ≤ N ^ 2 := by nlinarith
  apply primePins_implies_coverage N M hMN (modelPoint N)
  intro p hp hpN hpM
  have hpH : p ≤ N / 2 - 3 := by nlinarith
  exact modelPoint_small_prime N p hp hpN hpH

abbrev FactorIndex (M : ℕ) := {m : Fin (M + 1) // 1 < m.val ∧ ¬ Nat.Prime m.val}

abbrev HorizonFamilyIndex (N M : ℕ) := BertrandFamilyIndex N ⊕ FactorIndex M

def horizonFamily (N M : ℕ) : HorizonFamilyIndex N M → R N ℚ
  | .inl j => bertrandFamily N j
  | .inr m => factorPolynomial N m.val.val

theorem primePoint_horizonFamily (N M : ℕ) (hMN : M ≤ N ^ 2)
    (j : HorizonFamilyIndex N M) : eval (primePoint N ℚ) (horizonFamily N M j) = 0 := by
  rcases j with j | m
  · exact primePoint_bertrandFamily N j
  · exact primePoint_factorPolynomial N M m.val.val hMN m.property.1 (by omega) m.property.2

theorem modelPoint_horizonFamily (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) (j : HorizonFamilyIndex N M) :
    eval (modelPoint N) (horizonFamily N M j) = 0 := by
  rcases j with j | m
  · exact modelPoint_bertrandFamily N hN j
  · exact modelPoint_coverage N M hM m.val.val m.property.1 (by omega) m.property.2

theorem horizonFamily_common_zero (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) :
    (∀ j, eval (modelPoint N) (horizonFamily N M j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    eval (modelPoint N) (g N ℚ) = 0 :=
  ⟨modelPoint_horizonFamily N M hN hM, modelPoint_boolean N, modelPoint_g_zero N hN⟩

theorem horizonFamily_no_certificate (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) (A : HorizonFamilyIndex N M → R N ℚ)
    (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) : ¬ Certificate (horizonFamily N M) A U B := by
  intro cert
  exact certificate_excludes_common_zero (horizonFamily N M) A U B cert (modelPoint N)
    (modelPoint_horizonFamily N M hN hM) (modelPoint_boolean N) (modelPoint_g_zero N hN)

theorem horizonFamily_has_second_boolean_solution (N M : ℕ) (hN : 24 ≤ N)
    (hM : M ≤ (N / 2 - 3) ^ 2) :
    (∀ j, eval (primePoint N ℚ) (horizonFamily N M j) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ j, eval (modelPoint N) (horizonFamily N M j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    modelPoint N ≠ primePoint N ℚ := by
  have hh : N / 2 - 3 ≤ N := by omega
  have hMN : M ≤ N ^ 2 := by nlinarith
  exact ⟨primePoint_horizonFamily N M hMN, primePoint_boolean,
    modelPoint_horizonFamily N M hN hM, modelPoint_boolean N,
    modelPoint_differs_from_primePoint N hN⟩

end
end AlgebraicGoldbach.FactorCoverage
