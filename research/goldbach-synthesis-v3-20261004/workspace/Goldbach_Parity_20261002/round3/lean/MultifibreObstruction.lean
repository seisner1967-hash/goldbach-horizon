import ParityWeights
import Mathlib.Tactic

/-!
Finite obstruction to a favorable four-site argument at N=100000000,
alpha=100 and Q=999999. After an independent exact numerical filter, this
module certifies the actual first-axis Mangoldt weights and evaluates the
literal D/W prefix sums, including their moving face and harmonic unit mask.
No asymptotic estimate is asserted.
-/

namespace GoldbachResearch.MultifibreObstruction

open GoldbachResearch.ParityWeights GoldbachResearch.ActualArithmetic

noncomputable def firstAxis (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n - Real.log (n : ℝ)

theorem firstAxis_nonpos (n : ℕ) : firstAxis n ≤ 0 := by
  unfold firstAxis
  exact sub_nonpos.mpr ArithmeticFunction.vonMangoldt_le_log

theorem shifted_product_identity (f₁ fₚ fᵩ fₚᵩ B₁ Bₚ Bᵩ Bₚᵩ : ℝ) :
    f₁ * B₁ - fₚ * Bₚ - fᵩ * Bᵩ + fₚᵩ * Bₚᵩ =
      B₁ * (f₁ - fₚ - fᵩ + fₚᵩ) +
      fₚᵩ * (B₁ - Bₚ - Bᵩ + Bₚᵩ) +
      (fₚᵩ - fₚ) * (Bₚ - B₁) + (fₚᵩ - fᵩ) * (Bᵩ - B₁) := by
  ring

theorem archimedean_curvature_identity (N b p q : ℝ) :
    (N - p * b) * (N - q * b) - (N - b) * (N - p * q * b) =
      N * b * (p - 1) * (q - 1) := by
  ring

theorem logarithmic_shift_identity {x₁ xₚ xᵩ xₚᵩ : ℝ}
    (h₁ : 0 < x₁) (hₚ : 0 < xₚ) (hᵩ : 0 < xᵩ) (hₚᵩ : 0 < xₚᵩ) :
    -Real.log x₁ + Real.log xₚ + Real.log xᵩ - Real.log xₚᵩ =
      Real.log (xₚ * xᵩ / (x₁ * xₚᵩ)) := by
  rw [Real.log_div (mul_ne_zero hₚ.ne' hᵩ.ne') (mul_ne_zero h₁.ne' hₚᵩ.ne'),
    Real.log_mul hₚ.ne' hᵩ.ne', Real.log_mul h₁.ne' hₚᵩ.ne']
  ring

theorem logarithmic_curvature_pos {N b p q : ℝ}
    (hN : 0 < N) (hb : 0 < b) (hp : 1 < p) (hq : 1 < q)
    (h₁ : 0 < N - b) (hₚ : 0 < N - p * b)
    (hᵩ : 0 < N - q * b) (hₚᵩ : 0 < N - p * q * b) :
    0 < -Real.log (N - b) + Real.log (N - p * b) +
      Real.log (N - q * b) - Real.log (N - p * q * b) := by
  rw [logarithmic_shift_identity h₁ hₚ hᵩ hₚᵩ]
  apply Real.log_pos
  apply (lt_div_iff₀ (mul_pos h₁ hₚᵩ)).mpr
  have hid := archimedean_curvature_identity N b p q
  have hpositive : 0 < N * b * (p - 1) * (q - 1) :=
    mul_pos (mul_pos (mul_pos hN hb) (sub_pos.mpr hp)) (sub_pos.mpr hq)
  linarith

theorem semiprime_nonprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ¬ (p * q).Prime := by
  intro h
  rcases h.eq_one_or_self_of_dvd p (dvd_mul_right p q) with h1 | hprod
  · exact hp.ne_one h1
  · have hlt : p < p * q := by nlinarith [hp.two_le, hq.two_le]
    omega

theorem semiprime_firstAxis {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    firstAxis (p * q) = -Real.log ((p * q : ℕ) : ℝ) := by
  have hmu : ArithmeticFunction.moebius (p * q) ≠ 0 := by
    intro hzero
    have hw := (semiprime_weights hp hq hpq).2
    simp [evenWeight, muReal, hzero] at hw
  have hvm := vonMangoldt_zero_of_moebius_nezero_nonprime hmu
    (semiprime_nonprime hp hq)
  simp [firstAxis, hvm]

theorem concrete_first_axis_sites :
    firstAxis 99999899 = -Real.log (99999899 : ℝ) ∧
    firstAxis 99999697 = -Real.log (99999697 : ℝ) ∧
    firstAxis 99999293 = -Real.log (99999293 : ℝ) ∧
    firstAxis 99997879 = 0 := by
  have hp17 : Nat.Prime 17 := by norm_num
  have hp5882347 : Nat.Prime 5882347 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp41 : Nat.Prime 41 := by norm_num
  have hp348431 : Nat.Prime 348431 := by norm_num
  have hp577 : Nat.Prime 577 := by norm_num
  have hp173309 : Nat.Prime 173309 := by norm_num
  have hp99997879 : Nat.Prime 99997879 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert semiprime_firstAxis hp17 hp5882347 (by norm_num) using 1
  · have hvm := triprime_vonMangoldt_zero hp7 hp41 hp348431
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at hvm
    simp [firstAxis, hvm]
  · convert semiprime_firstAxis hp577 hp173309 (by norm_num) using 1
  · unfold firstAxis
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp99997879, sub_self]

noncomputable def kernel303 : ℝ := Real.log 101 / 2

noncomputable def kernel707 : ℝ :=
  Real.log 101 / 3 - Real.log 7 / 2 + Real.log 3 / 2

theorem kernel303_pos : 0 < kernel303 := by
  unfold kernel303
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem kernel707_pos : 0 < kernel707 := by
  have hlog : 0 < Real.log (((101 : ℝ) ^ 2 * 3 ^ 3) / 7 ^ 3) :=
    Real.log_pos (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  unfold kernel707
  linarith

noncomputable def closedFourSiteBlock (kernel2121 : ℝ) : ℝ :=
  firstAxis 99999899 * 0 + firstAxis 99999697 * kernel303 +
    firstAxis 99999293 * kernel707 + firstAxis 99997879 * kernel2121

theorem closedFourSiteBlock_identity (kernel2121 : ℝ) :
    closedFourSiteBlock kernel2121 =
      -(Real.log (99999697 : ℝ) * (Real.log 101 / 2)) -
        Real.log (99999293 : ℝ) *
          (Real.log 101 / 3 - Real.log 7 / 2 + Real.log 3 / 2) := by
  rcases concrete_first_axis_sites with ⟨h101, h303, h707, h2121⟩
  unfold closedFourSiteBlock kernel303 kernel707
  rw [h101, h303, h707, h2121]
  ring

theorem closedFourSiteBlock_neg (kernel2121 : ℝ) :
    closedFourSiteBlock kernel2121 < 0 := by
  rcases concrete_first_axis_sites with ⟨h101, h303, h707, h2121⟩
  unfold closedFourSiteBlock
  rw [h101, h303, h707, h2121]
  have h303 : 0 < Real.log (99999697 : ℝ) * kernel303 :=
    mul_pos (Real.log_pos (by norm_num)) kernel303_pos
  have h707 : 0 < Real.log (99999293 : ℝ) * kernel707 :=
    mul_pos (Real.log_pos (by norm_num)) kernel707_pos
  nlinarith

open scoped BigOperators

def literalPrefix (m : ℕ) : ℕ := min 999999 ((m - 1) / 100)

theorem literal_prefix_cut_iff {m k : ℕ} (hm : 0 < m) :
    (1 ≤ k ∧ k ≤ 999999 ∧ 100 * k < m) ↔
      k ∈ Finset.Icc 1 (literalPrefix m) := by
  rw [Finset.mem_Icc, literalPrefix, le_min_iff,
    Nat.le_div_iff_mul_le (by norm_num : 0 < 100)]
  omega

theorem concrete_prefix_and_unit_support :
    literalPrefix 101 = 1 ∧ literalPrefix 303 = 3 ∧
    literalPrefix 707 = 7 ∧ literalPrefix 2121 = 21 ∧
    (∀ m ∈ ({101,303,707,2121} : Finset ℕ),
      0 < m ∧ m < 100000000 ∧
        (100000000 - m).Coprime 100000000) := by
  decide

noncomputable def literalDivisor (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (literalPrefix m),
    if k ∣ m then muReal k * Real.log ((k : ℝ) / (m : ℝ)) else 0

noncomputable def literalHarmonic (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (literalPrefix m),
    if k.Coprime ((100000000 - m) * 100000000) then
      muReal k / (Nat.totient k : ℝ) * Real.log ((k : ℝ) / (m : ℝ)) else 0

noncomputable def literalKernel (m : ℕ) : ℝ :=
  muReal m * (literalDivisor m - literalHarmonic m)

theorem small_moebius_values :
    muReal 1 = 1 ∧ muReal 3 = -1 ∧ muReal 7 = -1 ∧
    muReal 303 = 1 ∧ muReal 707 = 1 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp101 : Nat.Prime 101 := by norm_num
  have hm303 := muReal_mul_of_coprime ((Nat.coprime_primes hp3 hp101).mpr (by norm_num))
  have hm707 := muReal_mul_of_coprime ((Nat.coprime_primes hp7 hp101).mpr (by norm_num))
  rw [muReal_prime hp3, muReal_prime hp101] at hm303
  rw [muReal_prime hp7, muReal_prime hp101] at hm707
  norm_num at hm303 hm707
  refine ⟨?_, muReal_prime hp3, muReal_prime hp7, ?_, ?_⟩
  · simp [muReal, ArithmeticFunction.moebius_apply_one]
  · exact hm303
  · exact hm707

theorem literal_kernel101 : literalKernel 101 = 0 := by
  have hpref : literalPrefix 101 = 1 := by decide
  have hset : Finset.Icc 1 1 = {1} := by decide
  have hphi1 : Nat.totient 1 = 1 := by decide
  unfold literalKernel literalDivisor literalHarmonic
  rw [hpref, hset]
  simp [hphi1]

theorem literal_kernel303 : literalKernel 303 = kernel303 := by
  rcases small_moebius_values with ⟨hm1, hm3, hm7, hm303, hm707⟩
  have hset : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hphi1 : Nat.totient 1 = 1 := by decide
  have hphi3 : Nat.totient 3 = 2 := by decide
  have hcop2 : ¬ Nat.Coprime 2 ((100000000 - 303) * 100000000) := by decide
  have hcop3 : Nat.Coprime 3 ((100000000 - 303) * 100000000) := by decide
  have hdiv2 : ¬ 2 ∣ 303 := by decide
  have hdiv3 : 3 ∣ 303 := by decide
  have hpref : literalPrefix 303 = 3 := by decide
  unfold literalKernel literalDivisor literalHarmonic
  rw [hpref, hset]
  norm_num [hm1, hm3, hm303, hdiv2, hdiv3, hcop2, hcop3, hphi1, hphi3]
  unfold kernel303
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (101 : ℝ) ≠ 0),
    Real.log_one]
  ring

theorem literal_kernel707 : literalKernel 707 = kernel707 := by
  rcases small_moebius_values with ⟨hm1, hm3, hm7, hm303, hm707⟩
  have hset : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hphi1 : Nat.totient 1 = 1 := by decide
  have hphi3 : Nat.totient 3 = 2 := by decide
  have hphi7 : Nat.totient 7 = 6 := by decide
  have hcop2 : ¬ Nat.Coprime 2 ((100000000 - 707) * 100000000) := by decide
  have hcop3 : Nat.Coprime 3 ((100000000 - 707) * 100000000) := by decide
  have hcop4 : ¬ Nat.Coprime 4 ((100000000 - 707) * 100000000) := by decide
  have hcop5 : ¬ Nat.Coprime 5 ((100000000 - 707) * 100000000) := by decide
  have hcop6 : ¬ Nat.Coprime 6 ((100000000 - 707) * 100000000) := by decide
  have hcop7 : Nat.Coprime 7 ((100000000 - 707) * 100000000) := by decide
  have hdiv2 : ¬ 2 ∣ 707 := by decide
  have hdiv3 : ¬ 3 ∣ 707 := by decide
  have hdiv4 : ¬ 4 ∣ 707 := by decide
  have hdiv5 : ¬ 5 ∣ 707 := by decide
  have hdiv6 : ¬ 6 ∣ 707 := by decide
  have hdiv7 : 7 ∣ 707 := by decide
  have hpref : literalPrefix 707 = 7 := by decide
  unfold literalKernel literalDivisor literalHarmonic
  rw [hpref, hset]
  norm_num [hm1, hm3, hm7, hm707, hdiv2, hdiv3, hdiv4, hdiv5, hdiv6, hdiv7,
    hcop2, hcop3, hcop4, hcop5, hcop6, hcop7, hphi1, hphi3, hphi7]
  unfold kernel707
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (101 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (707 : ℝ) ≠ 0)]
  have hlog : Real.log (707 : ℝ) = Real.log 7 + Real.log 101 := by
    have he : (707 : ℝ) = 7 * 101 := by norm_num
    rw [he, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog, Real.log_one]
  ring

noncomputable def literalFourSiteBlock : ℝ :=
  firstAxis 99999899 * literalKernel 101 + firstAxis 99999697 * literalKernel 303 +
    firstAxis 99999293 * literalKernel 707 + firstAxis 99997879 * literalKernel 2121

theorem literalFourSiteBlock_eq_closed :
    literalFourSiteBlock = closedFourSiteBlock (literalKernel 2121) := by
  unfold literalFourSiteBlock closedFourSiteBlock
  rw [literal_kernel101, literal_kernel303, literal_kernel707]

theorem literalFourSiteBlock_neg : literalFourSiteBlock < 0 := by
  rw [literalFourSiteBlock_eq_closed]
  exact closedFourSiteBlock_neg (literalKernel 2121)

#print axioms firstAxis_nonpos
#print axioms shifted_product_identity
#print axioms archimedean_curvature_identity
#print axioms logarithmic_shift_identity
#print axioms logarithmic_curvature_pos
#print axioms semiprime_nonprime
#print axioms semiprime_firstAxis
#print axioms concrete_first_axis_sites
#print axioms kernel303_pos
#print axioms kernel707_pos
#print axioms closedFourSiteBlock_identity
#print axioms closedFourSiteBlock_neg
#print axioms small_moebius_values
#print axioms literal_prefix_cut_iff
#print axioms concrete_prefix_and_unit_support
#print axioms literal_kernel101
#print axioms literal_kernel303
#print axioms literal_kernel707
#print axioms literalFourSiteBlock_eq_closed
#print axioms literalFourSiteBlock_neg

end GoldbachResearch.MultifibreObstruction
