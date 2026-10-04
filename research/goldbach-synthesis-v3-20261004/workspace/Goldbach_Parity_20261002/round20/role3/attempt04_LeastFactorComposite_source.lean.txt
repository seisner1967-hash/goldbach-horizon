import OddBonferroniArithmetic

/-! Round20 / 13.12. Least-factor arithmetic includes p² and repeated factors.
No roughness quality, prime-pair availability, or small remainder is assumed. -/
namespace GoldbachRound20.SwitchedComposite

open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

def leastPrimeQuotient (j : ℕ) : ℕ := j / j.minFac

def compositeLeastFactor (j : ℕ) : Prop := 2 ≤ j ∧ ¬ j.Prime

theorem leastPrimeQuotient_reconstruct (j : ℕ) :
    j.minFac * leastPrimeQuotient j = j := by
  simpa [leastPrimeQuotient, Nat.mul_comm] using Nat.div_mul_cancel (Nat.minFac_dvd j)

theorem leastPrimeCompositeWitness {j : ℕ} (hj : compositeLeastFactor j) :
    j.minFac.Prime ∧ j.minFac ∣ j ∧ j.minFac ^ 2 ≤ j ∧
      j.minFac ≤ leastPrimeQuotient j := by
  have htwo : 2 ≤ j := hj.1
  have hpos : 0 < j := by omega
  exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd j,
    Nat.minFac_sq_le_self hpos hj.2, Nat.minFac_le_div hpos hj.2⟩

theorem prime_divisor_unit {N t j l : ℕ} (hunit : Nat.Coprime j (t * N))
    (hl : l.Prime) (hd : l ∣ j) : ¬ l ∣ t * N := by
  exact hl.coprime_iff_not_dvd.mp (hunit.coprime_dvd_left hd)

theorem minFac_rough_quotient {N t j : ℕ} (hj : compositeLeastFactor j) :
    metSievePrimes N t j.minFac (leastPrimeQuotient j) = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro l hl
  obtain ⟨hlp, hlprime, _, hldiv⟩ := mem_metSievePrimes.mp hl
  have hdj : l ∣ j := by
    rw [← leastPrimeQuotient_reconstruct j]
    exact dvd_mul_of_dvd_right hldiv _
  have hle := Nat.minFac_le_of_dvd hlprime.two_le hdj
  omega

theorem minFac_roughIndicator {N t j : ℕ} (hj : compositeLeastFactor j) :
    roughIndicator N t j.minFac (leastPrimeQuotient j) = 1 := by
  simp [roughIndicator, minFac_rough_quotient hj]

theorem minFac_oddBonferroni {N t j K : ℕ} (hj : compositeLeastFactor j) :
    oddBonferroniWeight N t j.minFac K (leastPrimeQuotient j) = 1 := by
  rw [oddBonferroni_eq_binomial, minFac_rough_quotient hj]
  simp

theorem nonminimal_prime_met {N t j p : ℕ}
    (hj : compositeLeastFactor j) (hunit : Nat.Coprime j (t * N))
    (hp : p.Prime) (hpd : p ∣ j) (hneq : p ≠ j.minFac) :
    j.minFac ∈ metSievePrimes N t p (j / p) := by
  have hl := (leastPrimeCompositeWitness hj).1
  have hld : j.minFac ∣ j := Nat.minFac_dvd j
  have hlp : j.minFac < p := by
    have hle := Nat.minFac_le_of_dvd hp.two_le hpd
    omega
  have hrec : p * (j / p) = j := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hpd
  have hlq : j.minFac ∣ j / p := by
    have hld' : j.minFac ∣ p * (j / p) := by rw [hrec]; exact hld
    rcases hl.dvd_mul.mp hld' with h | h
    · have he := (Nat.prime_dvd_prime_iff_eq hl hp).mp h
      omega
    · exact h
  exact mem_metSievePrimes.mpr
    ⟨hlp, hl, prime_divisor_unit hunit hl (Nat.minFac_dvd j), hlq⟩

theorem nonminimal_prime_roughIndicator_zero {N t j p : ℕ}
    (hj : compositeLeastFactor j) (hunit : Nat.Coprime j (t * N))
    (hp : p.Prime) (hpd : p ∣ j) (hneq : p ≠ j.minFac) :
    roughIndicator N t p (j / p) = 0 := by
  have hmem := nonminimal_prime_met hj hunit hp hpd hneq
  have hn : metSievePrimes N t p (j / p) ≠ ∅ := by
    intro he
    simpa [he] using hmem
  simp [roughIndicator, hn]

theorem nonminimal_prime_oddBonferroni_nonpos {N t j p K : ℕ}
    (hj : compositeLeastFactor j) (hunit : Nat.Coprime j (t * N))
    (hp : p.Prime) (hpd : p ∣ j) (hneq : p ≠ j.minFac) :
    oddBonferroniWeight N t p K (j / p) ≤ 0 := by
  have hle := oddBonferroni_le_roughIndicator N t p K (j / p)
  rwa [nonminimal_prime_roughIndicator_zero hj hunit hp hpd hneq] at hle

theorem rough_prime_divisor_is_minFac {N t j p : ℕ}
    (hj : compositeLeastFactor j) (hunit : Nat.Coprime j (t * N))
    (hp : p.Prime) (hpd : p ∣ j)
    (hrough : metSievePrimes N t p (j / p) = ∅) : p = j.minFac := by
  by_contra hn
  have hm := nonminimal_prime_met hj hunit hp hpd hn
  simpa [hrough] using hm

theorem square_is_composite {p : ℕ} (hp : p.Prime) :
    compositeLeastFactor (p ^ 2) := by
  constructor
  · have := hp.two_le; nlinarith
  · intro hpp
    have hd : p ∣ p ^ 2 := by simp [pow_two]
    have he := (Nat.prime_dvd_prime_iff_eq hp hpp).mp hd
    have := hp.two_le
    nlinarith

theorem square_minFac {p : ℕ} (hp : p.Prime) : (p ^ 2).minFac = p := by
  exact hp.pow_minFac (by norm_num : 2 ≠ 0)

theorem square_quotient {p : ℕ} (hp : p.Prime) :
    leastPrimeQuotient (p ^ 2) = p := by
  rw [leastPrimeQuotient, square_minFac hp, pow_two, Nat.mul_div_left _ hp.pos]

theorem square_oddBonferroni (N t K : ℕ) {p : ℕ} (hp : p.Prime) :
    oddBonferroniWeight N t p K p = 1 := by
  have h := minFac_oddBonferroni (N := N) (t := t) (K := K) (square_is_composite hp)
  simpa [square_minFac hp, square_quotient hp] using h

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound20.SwitchedComposite.leastPrimeQuotient
#print axioms GoldbachRound20.SwitchedComposite.compositeLeastFactor
#print axioms GoldbachRound20.SwitchedComposite.leastPrimeQuotient_reconstruct
#print axioms GoldbachRound20.SwitchedComposite.leastPrimeCompositeWitness
#print axioms GoldbachRound20.SwitchedComposite.prime_divisor_unit
#print axioms GoldbachRound20.SwitchedComposite.minFac_rough_quotient
#print axioms GoldbachRound20.SwitchedComposite.minFac_roughIndicator
#print axioms GoldbachRound20.SwitchedComposite.minFac_oddBonferroni
#print axioms GoldbachRound20.SwitchedComposite.nonminimal_prime_met
#print axioms GoldbachRound20.SwitchedComposite.nonminimal_prime_roughIndicator_zero
#print axioms GoldbachRound20.SwitchedComposite.nonminimal_prime_oddBonferroni_nonpos
#print axioms GoldbachRound20.SwitchedComposite.rough_prime_divisor_is_minFac
#print axioms GoldbachRound20.SwitchedComposite.square_is_composite
#print axioms GoldbachRound20.SwitchedComposite.square_minFac
#print axioms GoldbachRound20.SwitchedComposite.square_quotient
#print axioms GoldbachRound20.SwitchedComposite.square_oddBonferroni

end
end GoldbachRound20.SwitchedComposite
