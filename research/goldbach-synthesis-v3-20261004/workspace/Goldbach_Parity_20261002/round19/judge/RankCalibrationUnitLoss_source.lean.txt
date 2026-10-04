import RankCalibrationArithmetic

/-!
The discarded large conductor factors are paid by actual lost integers.
Every interval endpoint retains the +1 front. No prime AP estimate is used
for these exclusions. The mass constraint in the final theorem is derived
from the actual canonical physical support.
-/
namespace GoldbachRound19.RankCalibration

open scoped BigOperators
open Finset
open GoldbachRound18.SeparatedTypeII
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

def largeMultiples (I : Finset ℕ) (p R : ℕ) : Finset ℕ :=
  I.filter fun b => R < p ∧ p ∣ b

theorem small_conductor_dvd (c r R : ℕ) : smallConductor c r R ∣ c * r := by
  have hsub : smallSelector c r R ⊆ ({c, r} : Finset ℕ) := filter_subset _ _
  rcases selector_cases hsub with e | e | e | e
  · simp [smallConductor, e]
  · simpa [smallConductor, e] using dvd_mul_right c r
  · simpa [smallConductor, e] using dvd_mul_left r c
  · by_cases hne : c = r
    · subst r
      simpa [smallConductor, e] using dvd_mul_right c c
    · simp [smallConductor, e, hne]

theorem small_prime_dvd_small_conductor {c r R p : ℕ}
    (hp : p = c ∨ p = r) (hR : p ≤ R) : p ∣ smallConductor c r R := by
  apply dvd_prod_of_mem (fun n : ℕ => n)
  apply mem_filter.mpr
  refine ⟨?_, hR⟩
  simpa only [mem_insert, mem_singleton] using hp

theorem full_rank_units_subset_small (F : Parameters) (I : Finset ℕ) (h P R : ℕ) :
    rankUnits F I (F.N * conductor F * h) P ⊆
      rankUnits F I (F.N * smallConductor F.c F.r R * h) P := by
  intro b hb
  obtain ⟨hbU, hbF⟩ := mem_filter.mp hb
  obtain ⟨hbI, hbC⟩ := mem_filter.mp hbU
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hbI, ?_⟩, hbF⟩
  apply hbC.coprime_dvd_right
  exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left F.N (small_conductor_dvd F.c F.r R)) h

theorem lost_rank_unit_large_factor (F : Parameters) (I : Finset ℕ) (h P R : ℕ)
    (hc : F.c.Prime) (hr : F.r.Prime) :
    (rankUnits F I (F.N * smallConductor F.c F.r R * h) P \
      rankUnits F I (F.N * conductor F * h) P) ⊆
      largeMultiples I F.c R ∪ largeMultiples I F.r R := by
  intro b hb
  obtain ⟨hbS, hbNot⟩ := mem_sdiff.mp hb
  obtain ⟨hbUS, hbF⟩ := mem_filter.mp hbS
  obtain ⟨hbI, hbCop⟩ := mem_filter.mp hbUS
  have hbN : Nat.Coprime b F.N := hbCop.coprime_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_right F.N (smallConductor F.c F.r R)) h)
  have hbh : Nat.Coprime b h := hbCop.coprime_dvd_right
    (dvd_mul_left h (F.N * smallConductor F.c F.r R))
  have hn : ¬ Nat.Coprime b (conductor F) := by
    intro hbd
    apply hbNot
    apply mem_filter.mpr
    exact ⟨mem_filter.mpr ⟨hbI, (hbN.mul_right hbd).mul_right hbh⟩, hbF⟩
  obtain ⟨p, hp, hpb, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have he := prime_dvd_conductor hc hr hp hpd
  have hpR : R < p := by
    by_contra hh
    have hdSmall := small_prime_dvd_small_conductor he (show p ≤ R by omega)
    have hdWhole : p ∣ F.N * smallConductor F.c F.r R * h :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdSmall F.N) h
    have hu := hbCop.coprime_dvd_right hdWhole
    exact (hp.coprime_iff_not_dvd.mp hu.symm) hpb
  rcases he with e | e
  · apply mem_union.mpr
    left
    apply mem_filter.mpr
    exact ⟨hbI, by simpa [e] using And.intro hpR hpb⟩
  · apply mem_union.mpr
    right
    apply mem_filter.mpr
    exact ⟨hbI, by simpa [e] using And.intro hpR hpb⟩

theorem interval_large_multiples_bound {A B p R : ℕ} (hAB : A ≤ B)
    (hR : 0 < R) :
    ((largeMultiples (Ioc A B) p R).card : ℝ) ≤ ((B : ℝ) - A) / R + 1 := by
  by_cases hRp : R < p
  · have hp : 0 < p := by omega
    have hEq : largeMultiples (Ioc A B) p R =
        (Ioc A B).filter fun b => Nat.ModEq p b 0 := by
      ext b
      simp [largeMultiples, hRp, Nat.modEq_zero_iff_dvd]
    rw [hEq]
    have hcq := residue_front (r := 0) hAB hp
    have hcr : |(((Ioc A B).filter fun b => Nat.ModEq p b 0).card : ℝ) -
        ((B : ℝ) - A) / p| ≤ 1 := by
      simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr hcq
    have hdiv : ((B : ℝ) - A) / p ≤ ((B : ℝ) - A) / R := by
      apply div_le_div_of_nonneg_left
      · exact sub_nonneg.mpr (by exact_mod_cast hAB)
      · exact_mod_cast hR
      · exact_mod_cast le_of_lt hRp
    have hc := (abs_le.mp hcr).2
    linarith
  · have hz : largeMultiples (Ioc A B) p R = ∅ := by simp [largeMultiples, hRp]
    rw [hz]
    simp only [card_empty, Nat.cast_zero]
    have hn : 0 ≤ ((B : ℝ) - A) / R := by
      apply div_nonneg
      · exact sub_nonneg.mpr (by exact_mod_cast hAB)
      · positivity
    linarith

theorem lost_rank_unit_card_bound (F : Parameters) {A B : ℕ} (h P R : ℕ)
    (hc : F.c.Prime) (hr : F.r.Prime) (hAB : A ≤ B) (hR : 0 < R) :
    ((rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P \
      rankUnits F (Ioc A B) (F.N * conductor F * h) P).card : ℝ) ≤
      2 * (((B : ℝ) - A) / R + 1) := by
  have hcard := card_le_card (lost_rank_unit_large_factor F (Ioc A B) h P R hc hr)
  have hunion := card_union_le (largeMultiples (Ioc A B) F.c R)
    (largeMultiples (Ioc A B) F.r R)
  have hcr : ((rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P \
      rankUnits F (Ioc A B) (F.N * conductor F * h) P).card : ℝ) ≤
      (largeMultiples (Ioc A B) F.c R).card +
        (largeMultiples (Ioc A B) F.r R).card := by exact_mod_cast le_trans hcard hunion
  have h₁ := interval_large_multiples_bound (p := F.c) hAB hR
  have h₂ := interval_large_multiples_bound (p := F.r) hAB hR
  linarith

theorem large_conductor_unit_price_bound (F : Parameters) {A B : ℕ}
    (U₀ : Finset ℕ) (h P R : ℕ) (hc : F.c.Prime) (hr : F.r.Prime)
    (hAB : A ≤ B) (hR : 0 < R)
    (hMass : structureCount F (Ioc A B) ≤
      (rankUnits F (Ioc A B) (F.N * conductor F * h) P).card)
    {u : ℝ} (hu : 0 ≤ u) (w : ℕ → ℝ)
    (hw : ∀ b ∈ rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P,
      0 ≤ w (candidate F b) ∧ w (candidate F b) ≤ u) :
    |supportPrice F (Ioc A B) U₀
        (rankUnits F (Ioc A B) (F.N * conductor F * h) P) w -
      supportPrice F (Ioc A B) U₀
        (rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P) w| ≤
      2 * u * (((B : ℝ) - A) / R + 1) := by
  have hs := normalized_reference_change_bound_card (structureCount F (Ioc A B))
    (rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P)
    (rankUnits F (Ioc A B) (F.N * conductor F * h) P)
    (fun b => w (candidate F b)) (full_rank_units_subset_small F (Ioc A B) h P R)
    hMass hu hw
  have hl := lost_rank_unit_card_bound F h P R hc hr hAB hR
  have he : supportPrice F (Ioc A B) U₀
      (rankUnits F (Ioc A B) (F.N * conductor F * h) P) w -
      supportPrice F (Ioc A B) U₀
      (rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P) w =
    referenceMass (structureCount F (Ioc A B))
      (rankUnits F (Ioc A B) (F.N * conductor F * h) P) (fun b => w (candidate F b)) -
    referenceMass (structureCount F (Ioc A B))
      (rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) P)
      (fun b => w (candidate F b)) := by unfold supportPrice; ring
  rw [he]
  apply le_trans hs
  nlinarith

theorem physical_large_conductor_theta_price_bound (F : Parameters) {A B : ℕ}
    (U₀ : Finset ℕ) (h R : ℕ) (hc : F.c.Prime) (hr : F.r.Prime)
    (hAB : A ≤ B) (hR : 0 < R) (hN : 1 ≤ F.N) (ha : 529 ≤ F.a)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ h → p * p ≤ F.a) :
    |supportPrice F (Ioc A B) U₀
        (rankUnits F (Ioc A B) (F.N * conductor F * h) 1771) (theta F.N) -
      supportPrice F (Ioc A B) U₀
        (rankUnits F (Ioc A B) (F.N * smallConductor F.c F.r R * h) 1771)
        (theta F.N)| ≤
      2 * Real.log (F.N : ℝ) * (((B : ℝ) - A) / R + 1) := by
  apply large_conductor_unit_price_bound F U₀ h 1771 R hc hr hAB hR
  · have hs := rank_structure_le_card F (Ioc A B) hsmall
      (by norm_num : Nat.Prime 7) (by norm_num : Nat.Prime 11) (by norm_num : Nat.Prime 23)
      (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega)
    simpa [fixed_rank_product] using hs
  · exact Real.log_nonneg (by exact_mod_cast hN)
  · intro b hb
    exact theta_candidate_bound F rfl hN b

end
end GoldbachRound19.RankCalibration

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound19.RankCalibration.largeMultiples
#print axioms GoldbachRound19.RankCalibration.small_conductor_dvd
#print axioms GoldbachRound19.RankCalibration.small_prime_dvd_small_conductor
#print axioms GoldbachRound19.RankCalibration.full_rank_units_subset_small
#print axioms GoldbachRound19.RankCalibration.lost_rank_unit_large_factor
#print axioms GoldbachRound19.RankCalibration.interval_large_multiples_bound
#print axioms GoldbachRound19.RankCalibration.lost_rank_unit_card_bound
#print axioms GoldbachRound19.RankCalibration.large_conductor_unit_price_bound
#print axioms GoldbachRound19.RankCalibration.physical_large_conductor_theta_price_bound
