import NonfriableReciprocalProjection

namespace GoldbachRound21.NonfriableReciprocal

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
open GoldbachRound20.Friable GoldbachRound20.Friable.SourceGeometry
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

def uniqueF0notF1Cost (alpha a N Z M Y : ℕ) : ℝ :=
  ∑ q ∈ q0not1 alpha N Z M Y,
    |GoldbachRound11.sourceBracket alpha a N q (resource1 N q)|

def sourceUniqueF0notF1Cost (N : ℕ) : ℝ :=
  uniqueF0notF1Cost (sourceAlpha N) (sourceA N) N (sourceZ N) (sourceM N) (sourceY N)

def sourceExtendedFriableCost (N : ℕ) : ℝ :=
  sourceFriableAbsoluteCost N + sourceUniqueF0notF1Cost N

theorem actual_source_q0not1_tau_sum_le_five {N : ℕ} (h : SourceOnset N) :
    (∑ q ∈ q0not1 (sourceAlpha N) N (sourceZ N) (sourceM N) (sourceY N),
      tau (resource1 N q)) ≤ 5 * (N : ℝ) * sourceU N ^ (-17 : ℝ) := by
  let S := q0not1 (sourceAlpha N) N (sourceZ N) (sourceM N) (sourceY N)
  let T : ℝ := ∑ q ∈ S, tau (resource1 N q)
  let B : ℝ := 5 * (N : ℝ) * sourceU N ^ (-17 : ℝ)
  have g := source_geometry h
  have hT : 0 ≤ T := sum_nonneg (fun q _ => tau_nonneg _)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
    (fun q => tau (resource1 N q))
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  have hc := actual_source_q0not1_card_le_three h
  have hm2 : (∑ q ∈ S, tau (resource1 N q) ^ 2) ≤
      8 * (N : ℝ) * sourceU N ^ 3 :=
    (actual_q0not1_tau_square_sum_le_global (sourceAlpha N) N
      (sourceZ N) (sourceM N) (sourceY N)).trans
      (actual_tau_second_moment_le_eight g.u_one)
  have hp : sourceU N ^ (-37 : ℝ) * sourceU N ^ 3 = sourceU N ^ (-34 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add g.u_pos]
    norm_num
  have hsq : T ^ 2 ≤ 24 * (N : ℝ) ^ 2 * sourceU N ^ (-34 : ℝ) := by
    calc
      T ^ 2 ≤ (S.card : ℝ) * ∑ q ∈ S, tau (resource1 N q) ^ 2 := hcs
      _ ≤ (3 * (N : ℝ) * sourceU N ^ (-37 : ℝ)) *
          (8 * (N : ℝ) * sourceU N ^ 3) :=
        mul_le_mul hc hm2 (sum_nonneg (fun q _ => sq_nonneg _)) (by positivity)
      _ = 24 * (N : ℝ) ^ 2 *
          (sourceU N ^ (-37 : ℝ) * sourceU N ^ 3) := by ring
      _ = _ := by rw [hp]
  have hpow : (sourceU N ^ (-17 : ℝ)) ^ 2 = sourceU N ^ (-34 : ℝ) := by
    rw [pow_two, ← Real.rpow_add g.u_pos]
    norm_num
  have hBsq : B ^ 2 = 25 * (N : ℝ) ^ 2 * sourceU N ^ (-34 : ℝ) := by
    dsimp only [B]
    calc
      _ = 25 * (N : ℝ) ^ 2 * (sourceU N ^ (-17 : ℝ)) ^ 2 := by ring
      _ = _ := by rw [hpow]
  have hsqB : T ^ 2 ≤ B ^ 2 := by
    rw [hBsq]
    exact hsq.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (24 : ℝ) ≤ 25) (sq_nonneg (N : ℝ)))
      (Real.rpow_nonneg g.u_pos.le _))
  have hTB : T ≤ B := by nlinarith
  exact hTB

theorem actual_unique_F0notF1_cost_le_tau {alpha a N Z M Y : ℕ}
    (ha : 1 ≤ a) (hu : 1 ≤ Real.log (N : ℝ)) :
    uniqueF0notF1Cost alpha a N Z M Y ≤
      7 * Real.log (N : ℝ) ^ 3 * ∑ q ∈ q0not1 alpha N Z M Y, tau (resource1 N q) := by
  unfold uniqueF0notF1Cost
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  obtain ⟨e, hs, _, _⟩ := q0not1_witness hq
  exact actual_sourceBracket_abs_le_seven_tau ha
    (by have hh := hs.1.resource1_two; omega) (Nat.sub_le N q) (q_lt_N hs.1).le hu

theorem actual_source_F0notF1_reciprocal_le_thirty_five {N : ℕ} (h : SourceOnset N) :
    sourceUniqueF0notF1Cost N ≤ 35 * (N : ℝ) * sourceU N ^ (-14 : ℝ) := by
  have g := source_geometry h
  have hp : sourceU N ^ 3 * sourceU N ^ (-17 : ℝ) = sourceU N ^ (-14 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add g.u_pos]
    norm_num
  calc
    _ ≤ 7 * sourceU N ^ 3 *
        ∑ q ∈ q0not1 (sourceAlpha N) N (sourceZ N) (sourceM N) (sourceY N),
          tau (resource1 N q) := actual_unique_F0notF1_cost_le_tau g.a_one g.u_one
    _ ≤ 7 * sourceU N ^ 3 * (5 * (N : ℝ) * sourceU N ^ (-17 : ℝ)) :=
      mul_le_mul_of_nonneg_left (actual_source_q0not1_tau_sum_le_five h) (by positivity)
    _ = 35 * (N : ℝ) * (sourceU N ^ 3 * sourceU N ^ (-17 : ℝ)) := by ring
    _ = _ := by rw [hp]

theorem actual_source_extended_cost_le_forty_four {N : ℕ} (h : SourceOnset N) :
    sourceExtendedFriableCost N ≤ 44 * (N : ℝ) * sourceU N ^ (-14 : ℝ) := by
  have g := source_geometry h
  have hp : sourceU N ^ (-33 : ℝ) ≤ sourceU N ^ (-14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le g.u_one (by norm_num)
  have hfirst := (actual_source_absolute_cost_le_nine h).trans
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 9 * (N : ℝ)))
  unfold sourceExtendedFriableCost
  have hh := add_le_add hfirst (actual_source_F0notF1_reciprocal_le_thirty_five h)
  exact hh.trans_eq (by ring)

theorem source_extended_loglog_absorption {N : ℕ} (h : SourceOnset N) :
    360448 * sourceEll N ≤ sourceU N ^ 13 := by
  have g := source_geometry h
  have hlarge : (360448 : ℝ) ≤ sourceU N := by
    have hh := source_u_large h
    norm_num at hh
    linarith
  have hpow := hlarge.trans (base_le_nat_pow g.u_one (by norm_num : (0 : ℕ) < 12))
  have hell : sourceEll N ≤ sourceU N := by
    have hh := Real.log_le_sub_one_of_pos g.u_pos
    unfold sourceEll
    linarith
  calc
    _ ≤ 360448 * sourceU N := mul_le_mul_of_nonneg_left hell (by norm_num)
    _ ≤ sourceU N ^ 13 := by
      simpa only [pow_succ] using mul_le_mul_of_nonneg_right hpow g.u_pos.le

theorem actual_source_extended_friable_cost_budget {N : ℕ} (h : SourceOnset N) :
    sourceExtendedFriableCost N ≤ (N : ℝ) / (8192 * sourceU N * sourceEll N) := by
  have g := source_geometry h
  have hell : 0 < sourceEll N := by linarith [g.ell_six]
  have hden : 0 < 8192 * sourceU N * sourceEll N :=
    mul_pos (mul_pos (by norm_num) g.u_pos) hell
  have habs := source_extended_loglog_absorption h
  have hp : sourceU N ^ 13 * sourceU N ^ (-13 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add g.u_pos]
    norm_num
  have hs : 360448 * sourceEll N * sourceU N ^ (-13 : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg g.u_pos.le _)).trans_eq hp
  have he : sourceU N ^ (-14 : ℝ) * sourceU N = sourceU N ^ (-13 : ℝ) := by
    have hh := (Real.rpow_add g.u_pos (-14) 1).symm
    norm_num at hh
    exact hh
  calc
    _ ≤ 44 * (N : ℝ) * sourceU N ^ (-14 : ℝ) := actual_source_extended_cost_le_forty_four h
    _ ≤ (N : ℝ) / (8192 * sourceU N * sourceEll N) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ = (N : ℝ) * (360448 * sourceEll N * (sourceU N ^ (-14 : ℝ) * sourceU N)) := by ring
        _ = (N : ℝ) * (360448 * sourceEll N * sourceU N ^ (-13 : ℝ)) := by rw [he]
        _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
        _ = _ := mul_one _

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.NonfriableReciprocal.uniqueF0notF1Cost
#print axioms GoldbachRound21.NonfriableReciprocal.sourceUniqueF0notF1Cost
#print axioms GoldbachRound21.NonfriableReciprocal.sourceExtendedFriableCost
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_q0not1_tau_sum_le_five
#print axioms GoldbachRound21.NonfriableReciprocal.actual_unique_F0notF1_cost_le_tau
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_F0notF1_reciprocal_le_thirty_five
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_extended_cost_le_forty_four
#print axioms GoldbachRound21.NonfriableReciprocal.source_extended_loglog_absorption
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_extended_friable_cost_budget

end
end GoldbachRound21.NonfriableReciprocal
