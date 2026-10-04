import FriableDemandAggregation
import FriableSourceGeometry

namespace GoldbachRound20.Friable.SourceGeometry

open Finset
noncomputable section

/-- These are the two actual costs paid here; F0\F1 reciprocals are excluded. -/
def sourceFriableAbsoluteCost (N : ℕ) : ℝ :=
  friableThetaDemand (sourceAlpha N) (sourceA N) N (sourceZ N) (sourceM N) (sourceY N) +
    uniqueReciprocalCost1 (sourceAlpha N) (sourceA N) N (sourceZ N) (sourceM N) (sourceY N)

theorem source_onset_u_twenty_eight {N : ℕ} (h : SourceOnset N) : 28 ≤ sourceU N := by
  have hh := source_u_large h
  norm_num at hh
  linarith

theorem base_le_nat_pow {u : ℝ} (hu : 1 ≤ u) {k : ℕ} (hk : 0 < k) : u ≤ u ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_pow₀ hu : (1 : ℝ) ≤ u ^ j) (by linarith : 0 ≤ u)

theorem source_rank_front_le_two_N {N : ℕ} (h : SourceOnset N) :
    (sourceEupper N : ℝ) * ((sourceD N : ℝ) * (sourceY N : ℝ)) ≤ 2 * (N : ℝ) := by
  have g := source_geometry h
  have hN1 := source_N_real_one h
  have hNpos : 0 < (N : ℝ) := by linarith
  have hDY : (sourceD N : ℝ) * (sourceY N : ℝ) ≤
      (2 * Real.sqrt (N : ℝ)) * (N : ℝ) ^ (1 / 128 : ℝ) :=
    mul_le_mul g.D_le_two_sqrt g.Y_le_small_power (Nat.cast_nonneg _) (by positivity)
  have hEDY := mul_le_mul g.Eupper_le_quarter hDY
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have he : (N : ℝ) ^ (1 / 4 : ℝ) *
      ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 128 : ℝ)) =
      (N : ℝ) ^ (97 / 128 : ℝ) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1 <;> norm_num
  have hr : (N : ℝ) ^ (97 / 128 : ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1.le
      (show (97 / 128 : ℝ) ≤ 1 by norm_num)
  calc
    _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) *
        ((2 * Real.sqrt (N : ℝ)) * (N : ℝ) ^ (1 / 128 : ℝ)) := hEDY
    _ = 2 * (N : ℝ) ^ (97 / 128 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ = 2 * ((N : ℝ) ^ (1 / 4 : ℝ) *
            ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 128 : ℝ))) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by norm_num)

/-- The source guards are derived from the single original onset, not assumed. -/
theorem actual_source_friable_demand_le_eight {N : ℕ} (h : SourceOnset N) :
    friableThetaDemand (sourceAlpha N) (sourceA N) N (sourceZ N) (sourceM N) (sourceY N) ≤
      8 * (N : ℝ) * sourceU N ^ (-33 : ℝ) := by
  have g := source_geometry h
  have hf := actual_friable_demand_payment_local (Z := sourceZ N)
    g.M_pos g.D_one g.D_le_M g.Y_pos g.alpha_pos g.alpha_le_a
    g.Eupper_le_a g.a_lt_M g.u_one g.logY_four g.one_add_logY g.D_log g.scale
  have hfront := source_rank_front_le_two_N h
  have hu28 := source_onset_u_twenty_eight h
  have hNu : 28 * (N : ℝ) ≤ (N : ℝ) * sourceU N := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu28 (Nat.cast_nonneg N)
  have hbracket : (N : ℝ) * (harmonic (sourceEupper N) : ℝ) +
      (sourceEupper N : ℝ) * ((sourceD N : ℝ) * (sourceY N : ℝ)) ≤
      (4 / 7 : ℝ) * (N : ℝ) * sourceU N := by
    have hh := mul_le_mul_of_nonneg_left g.harmonic_Eupper (Nat.cast_nonneg N)
    nlinarith
  have hpow : sourceU N ^ (-34 : ℝ) * sourceU N = sourceU N ^ (-33 : ℝ) := by
    have hh := (Real.rpow_add g.u_pos (-34) 1).symm
    norm_num at hh
    exact hh
  change _ ≤ 14 * sourceU N ^ (-34 : ℝ) *
    ((N : ℝ) * (harmonic (sourceEupper N) : ℝ) +
      (sourceEupper N : ℝ) * ((sourceD N : ℝ) * (sourceY N : ℝ))) at hf
  calc
    _ ≤ 14 * sourceU N ^ (-34 : ℝ) *
        ((N : ℝ) * (harmonic (sourceEupper N) : ℝ) +
          (sourceEupper N : ℝ) * ((sourceD N : ℝ) * (sourceY N : ℝ))) := hf
    _ ≤ 14 * sourceU N ^ (-34 : ℝ) * ((4 / 7 : ℝ) * (N : ℝ) * sourceU N) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by
      calc
        _ = 8 * (N : ℝ) * (sourceU N ^ (-34 : ℝ) * sourceU N) := by ring
        _ = _ := by rw [hpow]

theorem actual_source_unique_F1_reciprocal_le_one {N : ℕ} (h : SourceOnset N) :
    uniqueReciprocalCost1 (sourceAlpha N) (sourceA N) N (sourceZ N) (sourceM N) (sourceY N) ≤
      (N : ℝ) * sourceU N ^ (-33 : ℝ) := by
  have g := source_geometry h
  have hu7 : 7 ≤ sourceU N := (by norm_num : (7 : ℝ) ≤ 28).trans (source_onset_u_twenty_eight h)
  have hp6 : 7 ≤ sourceU N ^ 6 := hu7.trans (base_le_nat_pow g.u_one (by norm_num))
  have hpow : sourceU N ^ 6 * sourceU N ^ (-39 : ℝ) = sourceU N ^ (-33 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add g.u_pos]
    norm_num
  calc
    _ ≤ 7 * (N : ℝ) * sourceU N ^ (-39 : ℝ) := actual_source_unique_F1_reciprocal h
    _ = (N : ℝ) * (7 * sourceU N ^ (-39 : ℝ)) := by ring
    _ ≤ (N : ℝ) * (sourceU N ^ 6 * sourceU N ^ (-39 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp6 (Real.rpow_nonneg g.u_pos.le _)) (Nat.cast_nonneg N)
    _ = _ := by rw [hpow]

theorem actual_source_absolute_cost_le_nine {N : ℕ} (h : SourceOnset N) :
    sourceFriableAbsoluteCost N ≤ 9 * (N : ℝ) * sourceU N ^ (-33 : ℝ) := by
  unfold sourceFriableAbsoluteCost
  have hh := add_le_add (actual_source_friable_demand_le_eight h)
    (actual_source_unique_F1_reciprocal_le_one h)
  exact hh.trans_eq (by ring)

theorem source_loglog_absorption {N : ℕ} (h : SourceOnset N) :
    73728 * sourceEll N ≤ sourceU N ^ 32 := by
  have g := source_geometry h
  have hlarge : 73728 ≤ sourceU N := by
    have hh := source_u_large h
    norm_num at hh
    linarith
  have hpow31 := hlarge.trans (base_le_nat_pow g.u_one (by norm_num : (0 : ℕ) < 31))
  have hell : sourceEll N ≤ sourceU N := by
    have hh := Real.log_le_sub_one_of_pos g.u_pos
    unfold sourceEll
    linarith
  calc
    _ ≤ 73728 * sourceU N := mul_le_mul_of_nonneg_left hell (by norm_num)
    _ ≤ sourceU N ^ 32 := by
      simpa only [pow_succ] using mul_le_mul_of_nonneg_right hpow31 g.u_pos.le

/-- F4 for the two stated physical costs; no whole ledger or F0\F1 claim. -/
theorem actual_source_friable_absolute_cost_budget {N : ℕ} (h : SourceOnset N) :
    sourceFriableAbsoluteCost N ≤
      (N : ℝ) / (8192 * sourceU N * sourceEll N) := by
  have g := source_geometry h
  have hell : 0 < sourceEll N := by linarith [g.ell_six]
  have hden : 0 < 8192 * sourceU N * sourceEll N :=
    mul_pos (mul_pos (by norm_num) g.u_pos) hell
  have habs := source_loglog_absorption h
  have hpow : sourceU N ^ 32 * sourceU N ^ (-32 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add g.u_pos]
    norm_num
  have hs : 73728 * sourceEll N * sourceU N ^ (-32 : ℝ) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg g.u_pos.le _)).trans_eq hpow
  have he : sourceU N ^ (-33 : ℝ) * sourceU N = sourceU N ^ (-32 : ℝ) := by
    have hh := (Real.rpow_add g.u_pos (-33) 1).symm
    norm_num at hh
    exact hh
  calc
    _ ≤ 9 * (N : ℝ) * sourceU N ^ (-33 : ℝ) := actual_source_absolute_cost_le_nine h
    _ ≤ (N : ℝ) / (8192 * sourceU N * sourceEll N) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ = (N : ℝ) * (73728 * sourceEll N *
            (sourceU N ^ (-33 : ℝ) * sourceU N)) := by ring
        _ = (N : ℝ) * (73728 * sourceEll N * sourceU N ^ (-32 : ℝ)) := by rw [he]
        _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
        _ = _ := mul_one _

#print axioms sourceFriableAbsoluteCost
#print axioms source_onset_u_twenty_eight
#print axioms base_le_nat_pow
#print axioms source_rank_front_le_two_N
#print axioms actual_source_friable_demand_le_eight
#print axioms actual_source_unique_F1_reciprocal_le_one
#print axioms actual_source_absolute_cost_le_nine
#print axioms source_loglog_absorption
#print axioms actual_source_friable_absolute_cost_budget

end
end GoldbachRound20.Friable.SourceGeometry
