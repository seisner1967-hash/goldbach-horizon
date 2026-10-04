import FriablePhysicalPayment

namespace GoldbachRound20.Friable

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
open GoldbachRound10.ShortDivisorComplement GoldbachRound11
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The true cap and q >= M give the actual rank cutoff. -/
theorem actual_cofactor_rank_le {alpha N Z M e q : ℕ}
    (hM : 0 < M) (h : StructuralSupport alpha N Z M e q) : e ≤ N / M := by
  have hcap : e * q ≤ N :=
    (Nat.le_add_right (e * q) ((N - 1) / alpha)).trans
      ((Nat.le_add_right _ 1).trans h.2.2.2.2.2.2.1)
  have hm : e * M ≤ N := (Nat.mul_le_mul_left e h.2.2.1).trans hcap
  exact (Nat.le_div_iff_mul_le hM).mpr (by simpa [mul_comm] using hm)

theorem actual_physicalCoefficient_abs_le_seven_log_sq {alpha a N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) (halpha : 0 < alpha)
    (haa : alpha ≤ a) (hea : e ≤ a) (haq : a < q)
    (hu : 1 ≤ Real.log (N : ℝ)) :
    |physicalCoefficient alpha a N e q| ≤ 7 * Real.log (N : ℝ) ^ 2 := by
  have hp := anchor_three h.1
  have hanchor := h.2.2.2.1
  have hepos : 0 < e := by omega
  have hmpos : 0 < e * q := Nat.mul_pos hepos h.1.q_pos
  have hcap : e * q ≤ N :=
    (Nat.le_add_right (e * q) ((N - 1) / alpha)).trans
      ((Nat.le_add_right _ 1).trans h.2.2.2.2.2.2.1)
  have heN : e ≤ N := (Nat.le_mul_of_pos_right e h.1.q_pos).trans hcap
  have hLambda : |ArithmeticFunction.vonMangoldt e| ≤ Real.log (N : ℝ) := by
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hepos) (by exact_mod_cast heN))
  have ha : 1 ≤ a := (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt halpha)).trans haa
  have hQ : (N - 1) / alpha ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N 1)
  have hW := actual_harmonicKernel_abs_unconditional (n := N - e * q)
    ha hmpos hcap hQ
  have hW' : |harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q)| ≤
      6 * Real.log (N : ℝ) ^ 2 := by
    exact hW.trans (by nlinarith)
  rw [physical_coefficient_cofactor h halpha haa hea haq]
  calc
    _ ≤ |ArithmeticFunction.vonMangoldt e| +
        |mu e * harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add
        (ArithmeticFunction.vonMangoldt e)
        (-(mu e * harmonicKernel ((N - 1) / alpha) a N (N - e * q) (e * q)))
    _ ≤ Real.log (N : ℝ) + 6 * Real.log (N : ℝ) ^ 2 := by
      rw [abs_mul]
      exact add_le_add hLambda
        ((mul_le_mul_of_nonneg_right (mu_abs_le_one e) (abs_nonneg _)).trans
          (by simpa using hW'))
    _ ≤ _ := by nlinarith

theorem actual_theta_demand_abs_le_seven_log_cube {alpha a N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) (halpha : 0 < alpha)
    (haa : alpha ≤ a) (hea : e ≤ a) (haq : a < q)
    (hu : 1 ≤ Real.log (N : ℝ)) :
    |thetaBracket alpha a N e q| ≤ 7 * Real.log (N : ℝ) ^ 3 := by
  rw [thetaBracket_actual, abs_mul, abs_mul]
  have hc := actual_physicalCoefficient_abs_le_seven_log_sq h halpha haa hea haq hu
  have hf := mul_le_mul (primeIncidence_abs_le_one N q)
    (theta_abs_le_log (Nat.sub_le N (e * q))) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_mul] at hf
  calc
    _ ≤ Real.log (N : ℝ) * (7 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul hf hc (abs_nonneg _) (by linarith)
    _ = _ := by ring

/-- Raw proper powers remain on the first axis of this alternative bound. -/
theorem actual_raw_demand_abs_le_seven_log_cube {alpha a N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) (halpha : 0 < alpha)
    (haa : alpha ≤ a) (hea : e ≤ a) (haq : a < q)
    (hu : 1 ≤ Real.log (N : ℝ)) :
    |rawBracket alpha a N e q| ≤ 7 * Real.log (N : ℝ) ^ 3 := by
  unfold rawBracket
  rw [abs_mul, abs_mul]
  have hc := actual_physicalCoefficient_abs_le_seven_log_sq h halpha haa hea haq hu
  have hf := mul_le_mul (primeIncidence_abs_le_one N q)
    (rawLambda_abs_le_log (Nat.sub_le N (e * q))) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_mul] at hf
  calc
    _ ≤ Real.log (N : ℝ) * (7 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul hf hc (abs_nonneg _) (by linarith)
    _ = _ := by ring

/-- F2 on a physical rank: the small mass is the actual divisor sum, not a hypothesis. -/
theorem actual_friable_rank_theta_demand_le {S : Finset ℕ} {alpha a N Z M e D Y : ℕ}
    (he : 0 < e) (hD : 1 < D) (hDM : D ≤ M) (hY : 0 < Y)
    (halpha : 0 < alpha) (haa : alpha ≤ a) (hea : e ≤ a)
    (hu : 1 ≤ Real.log (N : ℝ))
    (hH : ∀ q ∈ S, StructuralSupport alpha N Z M e q)
    (haq : ∀ q ∈ S, a < q)
    (hF : ∀ q ∈ S, Smooth Y (resource0 N q) ∨ Smooth Y (resource1 N q)) :
    (∑ q ∈ S, |thetaBracket alpha a N e q|) ≤
      14 * Real.log (N : ℝ) ^ 3 * ((N : ℝ) / (e : ℝ) *
        (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) + ((divisorBand D Y).card : ℝ)) := by
  have hpoint : (∑ q ∈ S, |thetaBracket alpha a N e q|) ≤
      (S.card : ℝ) * (7 * Real.log (N : ℝ) ^ 3) := by
    calc
      _ ≤ ∑ q ∈ S, 7 * Real.log (N : ℝ) ^ 3 := Finset.sum_le_sum
        (fun q hq => actual_theta_demand_abs_le_seven_log_cube (hH q hq)
          halpha haa hea (haq q hq) hu)
      _ = _ := by simp
  have hcard := actual_friable_union_card_le_mass he hD hDM hY hH hF
  calc
    _ ≤ (S.card : ℝ) * (7 * Real.log (N : ℝ) ^ 3) := hpoint
    _ ≤ (2 * ((N : ℝ) / (e : ℝ) *
        (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) + ((divisorBand D Y).card : ℝ))) *
        (7 * Real.log (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

#print axioms actual_cofactor_rank_le
#print axioms actual_physicalCoefficient_abs_le_seven_log_sq
#print axioms actual_theta_demand_abs_le_seven_log_cube
#print axioms actual_raw_demand_abs_le_seven_log_cube
#print axioms actual_friable_rank_theta_demand_le

end
end GoldbachRound20.Friable
