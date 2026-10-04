import GoldbachArithmetic
import Mathlib.Tactic

/-!
Exact parity-sensitive bilinear projectors, using the existing actual Moebius
coefficient. These identities distinguish even and odd squarefree products.
They do not bound the positive composite contribution at the moving boundary.
-/

namespace GoldbachResearch.ParityWeights

open ActualArithmetic

noncomputable def oddWeight (n : ℕ) : ℝ :=
  (muReal n ^ 2 - muReal n) / 2

noncomputable def evenWeight (n : ℕ) : ℝ :=
  (muReal n ^ 2 + muReal n) / 2

theorem weights_sum (n : ℕ) :
    oddWeight n + evenWeight n = muReal n ^ 2 := by
  unfold oddWeight evenWeight
  ring

theorem weights_difference (n : ℕ) :
    evenWeight n - oddWeight n = muReal n := by
  unfold oddWeight evenWeight
  ring

theorem muReal_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) :
    muReal (a * b) = muReal a * muReal b := by
  unfold muReal
  exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab

theorem odd_bilinear_identity {a b : ℕ} (hab : a.Coprime b) :
    oddWeight (a * b) =
      oddWeight a * evenWeight b + evenWeight a * oddWeight b := by
  unfold oddWeight evenWeight
  rw [muReal_mul_of_coprime hab]
  ring

theorem even_bilinear_identity {a b : ℕ} (hab : a.Coprime b) :
    evenWeight (a * b) =
      evenWeight a * evenWeight b + oddWeight a * oddWeight b := by
  unfold oddWeight evenWeight
  rw [muReal_mul_of_coprime hab]
  ring

theorem muReal_prime {p : ℕ} (hp : p.Prime) : muReal p = -1 := by
  unfold muReal
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

theorem prime_weights {p : ℕ} (hp : p.Prime) :
    oddWeight p = 1 ∧ evenWeight p = 0 := by
  unfold oddWeight evenWeight
  rw [muReal_prime hp]
  norm_num

theorem semiprime_weights {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    oddWeight (p * q) = 0 ∧ evenWeight (p * q) = 1 := by
  unfold oddWeight evenWeight
  rw [muReal_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hpq),
    muReal_prime hp, muReal_prime hq]
  norm_num

theorem triprime_weights {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    oddWeight (p * q * r) = 1 ∧ evenWeight (p * q * r) = 0 := by
  have hpqr : (p * q).Coprime r := by
    exact Nat.Coprime.mul
      ((Nat.coprime_primes hp hr).mpr hpr)
      ((Nat.coprime_primes hq hr).mpr hqr)
  unfold oddWeight evenWeight
  rw [muReal_mul_of_coprime hpqr,
    muReal_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hpq),
    muReal_prime hp, muReal_prime hq, muReal_prime hr]
  norm_num

theorem oddWeight_nonneg (n : ℕ) : 0 ≤ oddWeight n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  all_goals unfold oddWeight muReal
  all_goals rw [h]
  all_goals norm_num

theorem evenWeight_nonneg (n : ℕ) : 0 ≤ evenWeight n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  all_goals unfold evenWeight muReal
  all_goals rw [h]
  all_goals norm_num

theorem oddWeight_idempotent (n : ℕ) : oddWeight n ^ 2 = oddWeight n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  all_goals unfold oddWeight muReal
  all_goals rw [h]
  all_goals norm_num

theorem weights_orthogonal (n : ℕ) : oddWeight n * evenWeight n = 0 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  all_goals unfold oddWeight evenWeight muReal
  all_goals rw [h]
  all_goals norm_num

theorem triprime_nonprime {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    ¬ (p * q * r).Prime := by
  intro h
  have hd : p ∣ p * q * r := dvd_trans (dvd_mul_right p q) (dvd_mul_right (p*q) r)
  rcases h.eq_one_or_self_of_dvd p hd with h1 | hprod
  · exact hp.ne_one h1
  · have hlt : p < p * q * r := by
      have hpq : p < p * q := by nlinarith [hp.two_le, hq.two_le]
      have hmult := Nat.mul_le_mul_left (p * q) hr.one_lt.le
      simp only [Nat.mul_one] at hmult
      exact lt_of_lt_of_le hpq hmult
    omega

theorem parity_detector_retains_composite {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    oddWeight (p * q * r) = 1 ∧ ¬ (p * q * r).Prime :=
  ⟨(triprime_weights hp hq hr hpq hpr hqr).1, triprime_nonprime hp hq hr⟩

theorem vonMangoldt_zero_of_moebius_nezero_nonprime {m : ℕ}
    (hm : ArithmeticFunction.moebius m ≠ 0) (hnp : ¬ m.Prime) :
    ArithmeticFunction.vonMangoldt m = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpow
  exact hm (ArithmeticFunction.moebius_apply_isPrimePow_not_prime hpow hnp)

theorem triprime_vonMangoldt_zero {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ArithmeticFunction.vonMangoldt (p * q * r) = 0 := by
  apply vonMangoldt_zero_of_moebius_nezero_nonprime ?_ (triprime_nonprime hp hq hr)
  intro hm
  have hw := (triprime_weights hp hq hr hpq hpr hqr).1
  simp [oddWeight, muReal, hm] at hw

theorem prime_divisor_bound_triprime {alpha p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hap : alpha < p) (haq : alpha < q) (har : alpha < r) :
    ∀ t : ℕ, t.Prime → t ∣ p * q * r → alpha < t := by
  intro t ht hd
  rcases ht.dvd_mul.mp hd with hpq | htr
  · rcases ht.dvd_mul.mp hpq with htp | htq
    · have he := (Nat.prime_dvd_prime_iff_eq ht hp).mp htp
      simpa [he] using hap
    · have he := (Nat.prime_dvd_prime_iff_eq ht hq).mp htq
      simpa [he] using haq
  · have he := (Nat.prime_dvd_prime_iff_eq ht hr).mp htr
    simpa [he] using har

theorem concrete_prime_triprime_same_parity :
    oddWeight 101 = 1 ∧ oddWeight (101 * 103 * 107) = 1 ∧
    ¬ (101 * 103 * 107).Prime ∧
    100 < 101 * 103 * 107 ∧ 101 * 103 * 107 < 100000000 ∧
    (∀ t : ℕ, t.Prime → t ∣ 101 * 103 * 107 → 100 < t) := by
  have hp : Nat.Prime 101 := by norm_num
  have hq : Nat.Prime 103 := by norm_num
  have hr : Nat.Prime 107 := by norm_num
  refine ⟨(prime_weights hp).1,
    (triprime_weights hp hq hr (by norm_num) (by norm_num) (by norm_num)).1,
    triprime_nonprime hp hq hr, by norm_num, by norm_num, ?_⟩
  exact prime_divisor_bound_triprime hp hq hr (by norm_num) (by norm_num) (by norm_num)

#print axioms weights_sum
#print axioms weights_difference
#print axioms muReal_mul_of_coprime
#print axioms odd_bilinear_identity
#print axioms even_bilinear_identity
#print axioms muReal_prime
#print axioms prime_weights
#print axioms semiprime_weights
#print axioms triprime_weights
#print axioms oddWeight_nonneg
#print axioms evenWeight_nonneg
#print axioms oddWeight_idempotent
#print axioms weights_orthogonal
#print axioms triprime_nonprime
#print axioms parity_detector_retains_composite
#print axioms vonMangoldt_zero_of_moebius_nezero_nonprime
#print axioms triprime_vonMangoldt_zero
#print axioms prime_divisor_bound_triprime
#print axioms concrete_prime_triprime_same_parity

end GoldbachResearch.ParityWeights
