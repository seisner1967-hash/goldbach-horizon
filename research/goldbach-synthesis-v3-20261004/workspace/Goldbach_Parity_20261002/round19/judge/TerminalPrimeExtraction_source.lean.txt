import Mathlib

/-! Terminal extraction uses the actual prime factor multiset.  Repetition is
retained by omega; no coprimality between the terminal prime and cofactor is
assumed.  This is an arithmetic reduction, not an estimate of D_N. -/
namespace GoldbachRound19.Terminal

noncomputable section

def omega (n : ℕ) : ℕ := n.primeFactorsList.length
def terminalPrime (n : ℕ) : ℕ := n.primeFactors.sup id
def largestPrime (n : ℕ) : ℕ := max 1 (terminalPrime n)
def cofactor (n : ℕ) : ℕ := n / terminalPrime n

theorem terminalPrime_mem {n : ℕ} (hn : 2 ≤ n) :
    terminalPrime n ∈ n.primeFactors := by
  have hs : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup n.primeFactors hs id
  change n.primeFactors.sup id ∈ n.primeFactors
  simpa only [he, id_eq] using hp

theorem terminalPrime_prime {n : ℕ} (hn : 2 ≤ n) :
    (terminalPrime n).Prime := Nat.prime_of_mem_primeFactors (terminalPrime_mem hn)

theorem terminalPrime_dvd {n : ℕ} (hn : 2 ≤ n) :
    terminalPrime n ∣ n := Nat.dvd_of_mem_primeFactors (terminalPrime_mem hn)

theorem primeFactor_le_terminal {n p : ℕ} (hp : p ∈ n.primeFactors) :
    p ≤ terminalPrime n := by
  simpa only [terminalPrime, id_eq] using (Finset.le_sup (f := id) hp)

theorem largestPrime_eq_terminal {n : ℕ} (hn : 2 ≤ n) :
    largestPrime n = terminalPrime n := by
  exact max_eq_right (by have := (terminalPrime_prime hn).two_le; omega)

theorem largestPrime_one : largestPrime 1 = 1 := by
  simp [largestPrime, terminalPrime]

theorem terminal_factorization {n : ℕ} (hn : 2 ≤ n) :
    cofactor n * terminalPrime n = n := by
  exact Nat.div_mul_cancel (terminalPrime_dvd hn)

theorem cofactor_pos {n : ℕ} (hn : 2 ≤ n) : 0 < cofactor n := by
  have hf := terminal_factorization hn
  by_contra hc
  have hz : cofactor n = 0 := by omega
  rw [hz, zero_mul] at hf
  omega

theorem cofactor_dvd {n : ℕ} (hn : 2 ≤ n) : cofactor n ∣ n := by
  exact ⟨terminalPrime n, (terminal_factorization hn).symm⟩

theorem cofactor_prime_order {n p : ℕ} (hn : 2 ≤ n)
    (hp : p ∈ (cofactor n).primeFactorsList) : p ≤ terminalPrime n := by
  apply primeFactor_le_terminal
  apply Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr
  exact (Nat.primeFactorsList_subset_of_dvd (cofactor_dvd hn) (by omega)) hp

theorem omega_terminal {n : ℕ} (hn : 2 ≤ n) :
    omega n = omega (cofactor n) + 1 := by
  have hh := (cofactor_pos hn).ne'
  have hr := (terminalPrime_prime hn).ne_zero
  have hp := Nat.perm_primeFactorsList_mul hh hr
  rw [terminal_factorization hn] at hp
  have hl := hp.length_eq
  simpa [omega, List.length_append, Nat.primeFactorsList_prime (terminalPrime_prime hn)] using hl

theorem terminalPrime_of_prime {n : ℕ} (hn : n.Prime) : terminalPrime n = n := by
  simp [terminalPrime, hn.primeFactors]

theorem cofactor_of_prime {n : ℕ} (hn : n.Prime) : cofactor n = 1 := by
  unfold cofactor
  rw [terminalPrime_of_prime hn]
  exact Nat.div_self hn.pos

theorem composite_iff_cofactor_two {n : ℕ} (hn : 2 ≤ n) :
    ¬ n.Prime ↔ 2 ≤ cofactor n := by
  constructor
  · intro hnp
    have hp := cofactor_pos hn
    by_contra hc
    have hh : cofactor n = 1 := by omega
    have hf := terminal_factorization hn
    rw [hh, one_mul] at hf
    exact hnp (hf ▸ terminalPrime_prime hn)
  · intro hh hp
    rw [cofactor_of_prime hp] at hh
    omega

/-- The order guard gives uniqueness even when r divides h. -/
theorem largestPrimeExtraction_unique {n h r : ℕ} (hn : 2 ≤ n)
    (hr : r.Prime) (hprod : h * r = n)
    (horder : ∀ p ∈ h.primeFactorsList, p ≤ r) :
    r = terminalPrime n ∧ h = cofactor n := by
  have hh : h ≠ 0 := by intro hz; rw [hz, zero_mul] at hprod; omega
  have hd : r ∣ n := hprod ▸ dvd_mul_left r h
  have hle : r ≤ terminalPrime n :=
    primeFactor_le_terminal (Nat.mem_primeFactors.mpr ⟨hr, hd, by omega⟩)
  have hge : terminalPrime n ≤ r := by
    apply Finset.sup_le
    intro p hp
    have hp' : p ∈ (h * r).primeFactorsList := by
      simpa [hprod] using (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)
    rcases (Nat.mem_primeFactorsList_mul hh hr.ne_zero).mp hp' with hpH | hpR
    · exact horder p hpH
    · have he : p = r := by simpa [Nat.primeFactorsList_prime hr] using hpR
      exact he.le
  have he : r = terminalPrime n := le_antisymm hle hge
  refine ⟨he, ?_⟩
  unfold cofactor
  rw [← he, ← hprod, Nat.mul_div_cancel h hr.pos]

theorem terminalPrime_prime_power {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    terminalPrime (p ^ k) = p := by
  simp [terminalPrime, Nat.primeFactors_prime_pow hk.ne' hp]

theorem omega_prime_power {p k : ℕ} (hp : p.Prime) : omega (p ^ k) = k := by
  simp [omega, hp.primeFactorsList_pow]

theorem repeated_terminal_example :
    terminalPrime (3 ^ 3) = 3 ∧ cofactor (3 ^ 3) = 3 ^ 2 ∧
      ¬ (cofactor (3 ^ 3)).Coprime (terminalPrime (3 ^ 3)) := by
  have hr : terminalPrime (3 ^ 3) = 3 :=
    terminalPrime_prime_power Nat.prime_three (by decide)
  have hh : cofactor (3 ^ 3) = 3 ^ 2 := by
    unfold cofactor
    rw [hr]
    norm_num
  exact ⟨hr, hh, by rw [hr, hh]; decide⟩

#print axioms omega
#print axioms terminalPrime
#print axioms largestPrime
#print axioms cofactor
#print axioms terminalPrime_mem
#print axioms terminalPrime_prime
#print axioms terminalPrime_dvd
#print axioms primeFactor_le_terminal
#print axioms largestPrime_eq_terminal
#print axioms largestPrime_one
#print axioms terminal_factorization
#print axioms cofactor_pos
#print axioms cofactor_dvd
#print axioms cofactor_prime_order
#print axioms omega_terminal
#print axioms terminalPrime_of_prime
#print axioms cofactor_of_prime
#print axioms composite_iff_cofactor_two
#print axioms largestPrimeExtraction_unique
#print axioms terminalPrime_prime_power
#print axioms omega_prime_power
#print axioms repeated_terminal_example

end
end GoldbachRound19.Terminal
