import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace GoldbachRound16.Margin

theorem log_two_lt_three_quarters : Real.log (2 : ℝ) < 3 / 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) 4)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

theorem log_three_lt_nine_eighths : Real.log (3 : ℝ) < 9 / 8 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 8) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

theorem log_five_lt_two : Real.log (5 : ℝ) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

theorem log_seven_lt_two : Real.log (7 : ℝ) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

theorem log_eleven_lt_five_halves : Real.log (11 : ℝ) < 5 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 11)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

theorem log_thirteen_lt_eight_thirds : Real.log (13 : ℝ) < 8 / 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 13)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 3) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

/-- The actual rational harmonic number has a uniform positive gap above log(n+1). -/
theorem harmonic_log_gap {n : ℕ} (hn : 1 ≤ n) :
    1 / 4 ≤ (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) := by
  have hmono := Real.strictMono_eulerMascheroniSeq.monotone hn
  have hbase : Real.eulerMascheroniSeq 1 = 1 - Real.log (2 : ℝ) := by
    norm_num [Real.eulerMascheroniSeq, harmonic]
  rw [hbase, Real.eulerMascheroniSeq] at hmono
  have hlog := log_two_lt_three_quarters
  linarith

/-- Tangent bound at 13; this avoids any assumption on a singular-series parameter. -/
theorem log_large_tangent {x : ℝ} (hx : 13 ≤ x) :
    Real.log x ≤ 8 / 3 + (x - 13) / 13 := by
  have hxpos : 0 < x := by linarith
  have hdiv := Real.log_le_sub_one_of_pos (div_pos hxpos (by norm_num : (0 : ℝ) < 13))
  rw [Real.log_div hxpos.ne' (by norm_num : (13 : ℝ) ≠ 0)] at hdiv
  have hlog := log_thirteen_lt_eight_thirds
  linarith

/-- The large-prime part of the Euler/harmonic anchor, valid even without primality. -/
theorem large_prime_margin {p : ℕ} (hp : 13 ≤ p) :
    1 / 144 ≤ (harmonic (p - 1) : ℝ) *
      (((p : ℝ) - 2) / ((p : ℝ) - 1)) - Real.log (p : ℝ) := by
  have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp
  have hpone : 0 < (p : ℝ) - 1 := by linarith
  have hptwo : 0 ≤ (p : ℝ) - 2 := by linarith
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    norm_cast
    omega
  have hH := harmonic_log_gap (n := p - 1) (by omega)
  rw [hcast] at hH
  have hlog := log_large_tangent hpR
  have hcalc :
      (1 / 144 : ℝ) ≤ (1 / 4 * ((p : ℝ) - 2) - Real.log (p : ℝ)) / ((p : ℝ) - 1) := by
    apply (le_div_iff₀ hpone).mpr
    linarith
  have heq :
      (harmonic (p - 1) : ℝ) * (((p : ℝ) - 2) / ((p : ℝ) - 1)) -
        Real.log (p : ℝ) =
      (((harmonic (p - 1) : ℝ) - Real.log (p : ℝ)) * ((p : ℝ) - 2) -
        Real.log (p : ℝ)) / ((p : ℝ) - 1) := by
    field_simp [ne_of_gt hpone]
    ring
  rw [heq]
  exact le_trans hcalc (by
    apply (div_le_div_iff₀ hpone hpone).mpr
    nlinarith [mul_le_mul_of_nonneg_right hH hptwo])

end GoldbachRound16.Margin

#print axioms GoldbachRound16.Margin.log_two_lt_three_quarters
#print axioms GoldbachRound16.Margin.log_three_lt_nine_eighths
#print axioms GoldbachRound16.Margin.log_five_lt_two
#print axioms GoldbachRound16.Margin.log_seven_lt_two
#print axioms GoldbachRound16.Margin.log_eleven_lt_five_halves
#print axioms GoldbachRound16.Margin.log_thirteen_lt_eight_thirds
#print axioms GoldbachRound16.Margin.harmonic_log_gap
#print axioms GoldbachRound16.Margin.log_large_tangent
#print axioms GoldbachRound16.Margin.large_prime_margin
