import FriableEulerRankin
import Mathlib.NumberTheory.Harmonic.Bounds

namespace GoldbachRound20.Friable

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
open GoldbachRound10.ShortDivisorComplement GoldbachRound11
noncomputable section
attribute [local instance] Classical.propDecidable

theorem short_filter_one_prime {a e q : ℕ} (he : 0 < e) (hea : e ≤ a)
    (hq : q.Prime) (haq : a < q) :
    ((e * q).divisors.filter (fun r => r ≤ a)) = e.divisors := by
  have hm0 : e * q ≠ 0 := mul_ne_zero (Nat.ne_of_gt he) hq.ne_zero
  ext r
  constructor
  · intro hr
    obtain ⟨hrm, hra⟩ := Finset.mem_filter.mp hr
    have hrpos := Nat.pos_of_mem_divisors hrm
    have hrcq : r.Coprime q :=
      (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hrpos
        (lt_of_le_of_lt hra haq))).symm
    have hdiv := (Nat.mem_divisors.mp hrm).1
    exact Nat.mem_divisors.mpr ⟨hrcq.dvd_mul_right.mp hdiv, Nat.ne_of_gt he⟩
  · intro hr
    have hdiv := (Nat.mem_divisors.mp hr).1
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨dvd_mul_of_dvd_left hdiv q, hm0⟩, (Nat.divisor_le hr).trans hea⟩

theorem complete_short_one_prime {a e q : ℕ} (he : 0 < e) (hea : e ≤ a)
    (hq : q.Prime) (haq : a < q) :
    shortDivisorSum a (e * q) = -ArithmeticFunction.vonMangoldt e := by
  unfold shortDivisorSum
  rw [← Finset.sum_filter, short_filter_one_prime he hea hq haq]
  simpa [mu] using (ArithmeticFunction.sum_moebius_mul_log_eq (n := e))

theorem one_prime_cofactor_arithmetic {a e q : ℕ} (he : 1 < e)
    (hea : e ≤ a) (hse : Squarefree e) (hq : q.Prime) (haq : a < q) :
    Squarefree (e * q) ∧ mu (e * q) = -mu e ∧
      ArithmeticFunction.vonMangoldt (e * q) = 0 := by
  have hc : e.Coprime q :=
    (Nat.coprime_of_lt_prime (by omega) (hea.trans_lt haq) hq).symm
  have hsf : Squarefree (e * q) := (Nat.squarefree_mul hc).mpr ⟨hse, hq.squarefree⟩
  have hm : mu (e * q) = -mu e := by
    rw [mu_mul_of_coprime hc]
    simp [mu, ArithmeticFunction.moebius_apply_prime hq]
  have hnp : ¬ (e * q).Prime := by
    intro hpq
    rcases Nat.prime_mul_iff.mp hpq with ⟨_, hq1⟩ | ⟨_, he1⟩
    · exact hq.ne_one hq1
    · exact (ne_of_gt he) he1
  have hv : ArithmeticFunction.vonMangoldt (e * q) = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro hpow
    exact hnp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf, hpow⟩)
  exact ⟨hsf, hm, hv⟩

/-- The acquired physical short complement yields the genuine coefficient. -/
theorem physical_coefficient_cofactor {alpha a N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) (halpha : 0 < alpha)
    (haa : alpha ≤ a) (hea : e ≤ a) (haq : a < q) :
    physicalCoefficient alpha a N e q = ArithmeticFunction.vonMangoldt e -
      mu e * harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q) := by
  have hp := anchor_three h.1
  have hanchor := h.2.2.2.1
  have he : 1 < e := by omega
  have har := one_prime_cofactor_arithmetic he hea h.2.2.2.2.1 h.2.1 haq
  have hmpos : 0 < e * q := Nat.mul_pos (by omega) h.1.q_pos
  have hmN : e * q < N := by
    have hc := h.2.2.2.2.2.2.1
    have hfront : e * q + 1 ≤ N :=
      (Nat.add_le_add_right (Nat.le_add_right (e * q) ((N - 1) / alpha)) 1).trans hc
    exact Nat.lt_of_succ_le hfront
  have hunitm : (e * q).Coprime N :=
    Nat.coprime_mul_iff_left.mpr ⟨h.2.2.2.2.2.1, h.1.q_unit⟩
  have hunit : (N - e * q).Coprime N :=
    (Nat.coprime_self_sub_left hmN.le).mpr hunitm
  have hk := physical_short_divisor_complement_source (Nat.ne_of_gt hmpos)
    (Nat.add_sub_of_le hmN.le) (Nat.sub_pos_of_lt hmN) hunit halpha haa
  rw [mu_square_of_squarefree har.1, har.2.2,
    complete_short_one_prime (by omega) hea h.2.1 haq] at hk
  simp only [neg_zero, neg_neg, zero_add, one_mul] at hk
  unfold physicalCoefficient
  rw [mul_sub, hk, har.2.1]
  ring

theorem actual_theta_cofactor {alpha a N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) (halpha : 0 < alpha)
    (haa : alpha ≤ a) (hea : e ≤ a) (haq : a < q) :
    thetaBracket alpha a N e q = primeIncidence N q * theta N (N - e * q) *
      (ArithmeticFunction.vonMangoldt e -
        mu e * harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q)) := by
  rw [thetaBracket_actual, physical_coefficient_cofactor h halpha haa hea haq]

/-- Raw von Mangoldt retains its genuine proper-power first axis. -/
theorem actual_raw_cofactor {alpha a N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) (halpha : 0 < alpha)
    (haa : alpha ≤ a) (hea : e ≤ a) (haq : a < q) :
    rawBracket alpha a N e q = primeIncidence N q * rawLambda N (N - e * q) *
      (ArithmeticFunction.vonMangoldt e -
        mu e * harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q)) := by
  unfold rawBracket
  rw [physical_coefficient_cofactor h halpha haa hea haq]

theorem mu_abs_le_one (k : ℕ) : |mu k| ≤ 1 := by
  unfold mu
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))

theorem log_ratio_abs_le_log {k m N : ℕ} (hk : 1 ≤ k)
    (hkm : k ≤ m) (hmN : m ≤ N) :
    |Real.log ((k : ℝ) / (m : ℝ))| ≤ Real.log (N : ℝ) := by
  have hm : 1 ≤ m := hk.trans hkm
  have hn : 1 ≤ N := hm.trans hmN
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogs : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hkR (by exact_mod_cast hkm)
  have hlogN : Real.log (m : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hmR (by exact_mod_cast hmN)
  rw [Real.log_div hkR.ne' hmR.ne', abs_of_nonpos (sub_nonpos.mpr hlogs)]
  linarith

def totientInverseSum (X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, (Nat.totient k : ℝ)⁻¹

/-- Independent elementary TK input, explicitly provisional until separately derived. -/
def TotientSumBound (X : ℕ) : Prop :=
  totientInverseSum X ≤ 3 * (1 + Real.log (X : ℝ))

theorem actual_harmonicKernel_abs_bound {Q a N n m : ℕ}
    (ha : 1 ≤ a) (hm : 0 < m) (hmN : m ≤ N) :
    |harmonicKernel Q a N n m| ≤ Real.log (N : ℝ) * totientInverseSum Q := by
  have hN : 1 ≤ N := by omega
  have hu : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  unfold harmonicKernel totientInverseSum
  apply le_trans (abs_sum_le_sum_abs _ _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk1 := (mem_Icc.mp hk).1
  have hphi : 0 < (Nat.totient k : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < k by omega)
  by_cases hg : a * k < m ∧ k.Coprime (n * N)
  · rw [if_pos hg, abs_div, abs_mul, abs_of_pos hphi]
    have hkm : k ≤ m := by nlinarith [hg.1]
    have hl := log_ratio_abs_le_log hk1 hkm hmN
    have hc : |mu k| * |Real.log ((k : ℝ) / (m : ℝ))| ≤ Real.log (N : ℝ) := by
      calc
        _ ≤ 1 * |Real.log ((k : ℝ) / (m : ℝ))| :=
          mul_le_mul_of_nonneg_right (mu_abs_le_one k) (abs_nonneg _)
        _ ≤ _ := by simpa using hl
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hc hphi.le
  · rw [if_neg hg, abs_zero]
    exact mul_nonneg hu (inv_nonneg.mpr hphi.le)

theorem totientInverseSum_mono {Q N : ℕ} (hQN : Q ≤ N) :
    totientInverseSum Q ≤ totientInverseSum N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hQN⟩
  · intro k _ _
    positivity

/-- This envelope is conditional under the named TK, not a source payment. -/
theorem actual_harmonicKernel_abs_of_TotientSumBound {Q a N n m : ℕ}
    (ha : 1 ≤ a) (hm : 0 < m) (hmN : m ≤ N) (hQN : Q ≤ N)
    (hTK : TotientSumBound N) :
    |harmonicKernel Q a N n m| ≤
      3 * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hN : 1 ≤ N := by omega
  have hu : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ Real.log (N : ℝ) * totientInverseSum Q :=
      actual_harmonicKernel_abs_bound ha hm hmN
    _ ≤ Real.log (N : ℝ) * (3 * (1 + Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left ((totientInverseSum_mono hQN).trans hTK) hu
    _ = _ := by ring

#print axioms short_filter_one_prime
#print axioms complete_short_one_prime
#print axioms one_prime_cofactor_arithmetic
#print axioms physical_coefficient_cofactor
#print axioms actual_theta_cofactor
#print axioms actual_raw_cofactor
#print axioms mu_abs_le_one
#print axioms log_ratio_abs_le_log
#print axioms totientInverseSum
#print axioms TotientSumBound
#print axioms actual_harmonicKernel_abs_bound
#print axioms totientInverseSum_mono
#print axioms actual_harmonicKernel_abs_of_TotientSumBound

end
end GoldbachRound20.Friable
