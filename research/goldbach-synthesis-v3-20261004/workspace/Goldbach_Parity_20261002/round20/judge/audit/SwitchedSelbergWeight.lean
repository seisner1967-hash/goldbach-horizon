import OddBonferroniArithmetic
import SelbergFourForms
import EulerAnchor

/-! Round20 / 13.12. Specialize acquired finite Selberg weights to the true
unit support t*N*p0 and the real totient density. No acquired module is rebuilt.
The optimum is a finite identity, with no uniform asymptotic or incidence claim. -/
namespace GoldbachRound20.SwitchedComposite

open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000


def switchedPrimeSupport (N t z : ℕ) : Finset ℕ :=
  (range (z + 1)).filter fun p => p.Prime ∧ Nat.Coprime p (N * t * GoldbachRound16.Anchor.leastMissingOddPrime N)

def totientDensity (p : ℕ) : ℝ := 1 / (Nat.totient p : ℝ)

def switchedG (N t z : ℕ) : ℝ := GoldbachRound17.Selberg.G (switchedPrimeSupport N t z) z totientDensity

def switchedLambda (N t z : ℕ) (s : Finset ℕ) : ℝ :=
  GoldbachRound17.Selberg.weight (switchedPrimeSupport N t z) z totientDensity s

def switchedDivisorSum (N t z j : ℕ) : ℝ :=
  ∑ s ∈ (switchedPrimeSupport N t z).powerset,
    if primeProduct s ∣ j then switchedLambda N t z s else 0

def switchedWeight (N t z j : ℕ) : ℝ :=
  Real.log (j : ℝ) * (switchedDivisorSum N t z j) ^ 2

def switchedPrincipal (N t z : ℕ) : ℝ :=
  GoldbachRound17.Selberg.principal (switchedPrimeSupport N t z) totientDensity (switchedLambda N t z)

theorem mem_switchedPrimeSupport {N t z p : ℕ} :
    p ∈ switchedPrimeSupport N t z ↔
      p ≤ z ∧ p.Prime ∧ Nat.Coprime p (N * t * GoldbachRound16.Anchor.leastMissingOddPrime N) := by
  simp [switchedPrimeSupport, Nat.lt_succ_iff]

theorem switchedSupport_prime {N t z p : ℕ} (hp : p ∈ switchedPrimeSupport N t z) :
    p.Prime := (mem_switchedPrimeSupport.mp hp).2.1

theorem switchedSupport_three_le {N t z p : ℕ} (heven : Even N)
    (hp : p ∈ switchedPrimeSupport N t z) : 3 ≤ p := by
  obtain ⟨_, hprime, hu⟩ := mem_switchedPrimeSupport.mp hp
  have hup : Nat.Coprime p N := hu.coprime_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_right N t) (GoldbachRound16.Anchor.leastMissingOddPrime N))
  have hn : ¬ p ∣ N := hprime.coprime_iff_not_dvd.mp hup
  have hp2 : p ≠ 2 := by intro he; exact hn (he.symm ▸ heven.two_dvd)
  have := hprime.two_le
  omega

theorem totientDensity_properties {N t z : ℕ} (heven : Even N) :
    ∀ p ∈ switchedPrimeSupport N t z, 0 < totientDensity p ∧ totientDensity p < 1 := by
  intro p hp
  have hprime := switchedSupport_prime hp
  have h3 := switchedSupport_three_le heven hp
  have hphi : 2 ≤ Nat.totient p := by rw [Nat.totient_prime hprime]; omega
  have hreal : (2 : ℝ) ≤ (Nat.totient p : ℝ) := by exact_mod_cast hphi
  unfold totientDensity
  constructor
  · positivity
  · exact (div_lt_one (by linarith)).mpr (by linarith)

theorem switchedG_pos {N t z : ℕ} (heven : Even N) (hz : 1 ≤ z) :
    0 < switchedG N t z := GoldbachRound17.Selberg.G_pos hz (totientDensity_properties heven)

theorem switchedLambda_empty {N t z : ℕ} (heven : Even N) (hz : 1 ≤ z) :
    switchedLambda N t z ∅ = 1 := GoldbachRound17.Selberg.weight_empty hz (totientDensity_properties heven)

theorem switchedPrincipal_optimum {N t z : ℕ} (heven : Even N) (hz : 1 ≤ z) :
    switchedPrincipal N t z = 1 / switchedG N t z :=
  GoldbachRound17.Selberg.principal_optimum hz (totientDensity_properties heven)

theorem switchedLambda_zero_large {N t z : ℕ} {s : Finset ℕ}
    (hlarge : z < primeProduct s) : switchedLambda N t z s = 0 := by
  apply GoldbachRound17.Selberg.product_exceeds_weight_zero
  · exact fun p hp => switchedSupport_prime hp
  · exact hlarge

theorem switchedLambda_moebius_formula {N t z : ℕ} (heven : Even N)
    {s : Finset ℕ} (hs : s ⊆ switchedPrimeSupport N t z) :
    switchedLambda N t z s = (ArithmeticFunction.moebius (primeProduct s) : ℝ) *
      (∑ r ∈ (GoldbachRound17.Selberg.support (switchedPrimeSupport N t z) z).filter (fun r => s ⊆ r),
        GoldbachRound17.Selberg.hprod totientDensity r) /
      (switchedG N t z * GoldbachRound17.Selberg.gprod totientDensity s) := by
  rw [switchedLambda, GoldbachRound17.Selberg.explicit_weight,
    GoldbachRound17.Selberg.sign_eq_moebius (fun p hp => switchedSupport_prime (hs hp))]
  rfl

theorem switchedDivisorSum_prime {N t z j : ℕ} (heven : Even N) (hz : 1 ≤ z)
    (hj : j.Prime) (hzj : z < j) : switchedDivisorSum N t z j = 1 := by
  unfold switchedDivisorSum
  rw [sum_eq_single ∅]
  · simp [primeProduct, switchedLambda_empty heven hz]
  · intro s hs hn
    have hsP := mem_powerset.mp hs
    have hd : ¬ primeProduct s ∣ j := by
      intro hd
      obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr hn
      have hpd : p ∣ j := dvd_trans (dvd_prod_of_mem (fun k : ℕ => k) hp) hd
      have he := (Nat.prime_dvd_prime_iff_eq (switchedSupport_prime (hsP hp)) hj).mp hpd
      have hle := (mem_switchedPrimeSupport.mp (hsP hp)).1
      omega
    simp [hd]
  · simp

theorem switchedWeight_prime {N t z j : ℕ} (heven : Even N) (hz : 1 ≤ z)
    (hj : j.Prime) (hzj : z < j) : switchedWeight N t z j = Real.log (j : ℝ) := by
  simp [switchedWeight, switchedDivisorSum_prime heven hz hj hzj]

theorem switchedWeight_nonneg (N t z : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ switchedWeight N t z j := by
  unfold switchedWeight
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hj)) (sq_nonneg _)

theorem switchedWeight_doubleExpansion (N t z j : ℕ) :
    switchedWeight N t z j =
      ∑ d ∈ (switchedPrimeSupport N t z).powerset,
        ∑ e ∈ (switchedPrimeSupport N t z).powerset,
          if primeProduct d ∣ j ∧ primeProduct e ∣ j
          then Real.log (j : ℝ) * switchedLambda N t z d * switchedLambda N t z e else 0 := by
  unfold switchedWeight switchedDivisorSum
  rw [pow_two, sum_mul, mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro e he
  by_cases hdd : primeProduct d ∣ j <;> by_cases hed : primeProduct e ∣ j
  all_goals simp [hdd, hed] <;> ring

theorem canonical_p0_sieve_empty {N t : ℕ} (hN : N ≠ 0) (heven : Even N) :
    smallSievePrimes N t (GoldbachRound16.Anchor.leastMissingOddPrime N) = ∅ := by
  obtain ⟨_, _, _, hforced⟩ := GoldbachRound16.Anchor.leastMissingOddPrime_spec hN heven
  apply eq_empty_iff_forall_not_mem.mpr
  intro l hl
  obtain ⟨hlp, hlprime, hlnot⟩ := mem_smallSievePrimes.mp hl
  exact hlnot (dvd_mul_of_dvd_right (hforced l hlprime hlp) t)

theorem canonical_p0_Bonferroni {N t K v : ℕ} (hN : N ≠ 0) (heven : Even N) :
    oddBonferroniWeight N t (GoldbachRound16.Anchor.leastMissingOddPrime N) K v = 1 := by
  rw [oddBonferroni_eq_binomial]
  have hm : metSievePrimes N t (GoldbachRound16.Anchor.leastMissingOddPrime N) v = ∅ := by
    simp [metSievePrimes, canonical_p0_sieve_empty hN heven]
  simp [hm]

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound20.SwitchedComposite.switchedPrimeSupport
#print axioms GoldbachRound20.SwitchedComposite.totientDensity
#print axioms GoldbachRound20.SwitchedComposite.switchedG
#print axioms GoldbachRound20.SwitchedComposite.switchedLambda
#print axioms GoldbachRound20.SwitchedComposite.switchedDivisorSum
#print axioms GoldbachRound20.SwitchedComposite.switchedWeight
#print axioms GoldbachRound20.SwitchedComposite.switchedPrincipal
#print axioms GoldbachRound20.SwitchedComposite.mem_switchedPrimeSupport
#print axioms GoldbachRound20.SwitchedComposite.switchedSupport_prime
#print axioms GoldbachRound20.SwitchedComposite.switchedSupport_three_le
#print axioms GoldbachRound20.SwitchedComposite.totientDensity_properties
#print axioms GoldbachRound20.SwitchedComposite.switchedG_pos
#print axioms GoldbachRound20.SwitchedComposite.switchedLambda_empty
#print axioms GoldbachRound20.SwitchedComposite.switchedPrincipal_optimum
#print axioms GoldbachRound20.SwitchedComposite.switchedLambda_zero_large
#print axioms GoldbachRound20.SwitchedComposite.switchedLambda_moebius_formula
#print axioms GoldbachRound20.SwitchedComposite.switchedDivisorSum_prime
#print axioms GoldbachRound20.SwitchedComposite.switchedWeight_prime
#print axioms GoldbachRound20.SwitchedComposite.switchedWeight_nonneg
#print axioms GoldbachRound20.SwitchedComposite.switchedWeight_doubleExpansion
#print axioms GoldbachRound20.SwitchedComposite.canonical_p0_sieve_empty
#print axioms GoldbachRound20.SwitchedComposite.canonical_p0_Bonferroni

end
end GoldbachRound20.SwitchedComposite
