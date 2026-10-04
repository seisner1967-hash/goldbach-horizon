import PhysicalAPPrices21

namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset MeasureTheory
open GoldbachRound18.SeparatedTypeII
open GoldbachRound20.SwitchedComposite
open GoldbachRound20.Friable.SourceGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

/-- The original source sieve cutoff; distinct from friable sourceZ20. -/
def sourceSieveCutoff21 (N : ℕ) : ℕ := Nat.ceil ((N : ℝ) ^ (1 / 64 : ℝ))

theorem source_N_ge_twenty {N : ℕ} (h : SourceOnset N) : (20 : ℝ) ≤ N := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast source_N_pos h
  have hl := Real.log_le_sub_one_of_pos hn
  have hu := source_u_large h
  norm_num at hu
  dsimp [sourceU] at hu
  linarith

theorem source_sieve_cutoff_le_N_div_ten {N : ℕ} (h : SourceOnset N) :
    (sourceSieveCutoff21 N : ℝ) ≤ (N : ℝ) / 10 := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast source_N_pos h
  have hu := source_u_large h
  norm_num at hu
  have hbig : (20 : ℝ) ≤ (N : ℝ) ^ (63 / 64 : ℝ) := by
    have hexp := Real.add_one_le_exp ((63 / 64 : ℝ) * sourceU N)
    have hexp20 : (20 : ℝ) ≤ Real.exp ((63 / 64 : ℝ) * sourceU N) := by linarith
    simpa [Real.rpow_def_of_pos hn, sourceU, mul_comm] using hexp20
  have hp : 0 < (N : ℝ) ^ (1 / 64 : ℝ) := Real.rpow_pos_of_pos hn _
  have hone : 1 ≤ (N : ℝ) ^ (1 / 64 : ℝ) :=
    Real.one_le_rpow (source_N_real_one h).le (by norm_num)
  have hceil : (sourceSieveCutoff21 N : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 64 : ℝ) :=
    Nat.ceil_le_two_mul (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hbig hp.le
  have hproduct : (N : ℝ) ^ (1 / 64 : ℝ) * (N : ℝ) ^ (63 / 64 : ℝ) = N := by
    rw [← Real.rpow_add hn]
    norm_num
  rw [hproduct] at hmul
  linarith

theorem source_frame_front_guards {F : Parameters} {x : ℕ}
    (h : SourceOnset F.N)
    (hxL : (F.N : ℝ) / 5 ≤ (x : ℝ)) (hxU : (x : ℝ) ≤ (F.N : ℝ) / 4) :
    x ≤ F.N ∧ 2 ≤ x / 2 ∧ max 1 (sourceSieveCutoff21 F.N) < x / 2 + 1 := by
  have hN20 := source_N_ge_twenty h
  have hx4 : 4 ≤ x := by
    have hxr : (4 : ℝ) ≤ x := by linarith
    exact_mod_cast hxr
  have hx2 : 2 ≤ x / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hz := source_sieve_cutoff_le_N_div_ten h
  have hzx : 2 * sourceSieveCutoff21 F.N ≤ x := by
    have hr : (2 : ℝ) * sourceSieveCutoff21 F.N ≤ x := by linarith
    exact_mod_cast hr
  have hz2 : sourceSieveCutoff21 F.N ≤ x / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa [Nat.mul_comm] using hzx)
  have hxN : x ≤ F.N := by
    have hr : (x : ℝ) ≤ F.N := by nlinarith [Nat.cast_nonneg F.N]
    exact_mod_cast hr
  exact ⟨hxN, hx2, by omega⟩

theorem source_sieve_cutoff_one {N : ℕ} (h : SourceOnset N) : 1 ≤ sourceSieveCutoff21 N := by
  exact Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by exact_mod_cast source_N_pos h) _)

theorem source_actualPrimeAP_B6 {F : Parameters} {s x nu : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N) (haxes : StaticAxes F s)
    (hxL : (F.N : ℝ) / 5 ≤ (x : ℝ)) (hxU : (x : ℝ) ≤ (F.N : ℝ) / 4) :
    |actualPrimeAP F s (sourceSieveCutoff21 F.N) nu (frameInterval F s x) - actualAPMain F s x nu| ≤
      primeAPPrice F s x nu := by
  obtain ⟨hxN, hx2, hfront⟩ := source_frame_front_guards h hxL hxU
  exact actualPrimeAP_price_bound h ha haxes hxN hx2 hfront

theorem source_actualCompositeAP_B6 {F : Parameters} {s x k l h p : ℕ}
    (hs : SourceOnset F.N) (ha : F.a = sourceA F.N) (haxes : StaticAxes F s)
    (hxL : (F.N : ℝ) / 5 ≤ (x : ℝ)) (hxU : (x : ℝ) ≤ (F.N : ℝ) / 4) :
    |actualCompositeAP F s (sourceSieveCutoff21 F.N) k l h p (frameInterval F s x) -
      compatibleAPMain F s (compositeAPConductor k l h p) (compositeAPIntegral F s x p)| ≤
        compositeAPPrice F s x k l h p := by
  obtain ⟨hxN, hx2, hfront⟩ := source_frame_front_guards hs hxL hxU
  exact actualCompositeAP_B6 hs ha haxes hxN hx2 hfront

theorem source_switchedIncidenceEstimator_APprices {F : Parameters} {s x P K : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N) (haxes : StaticAxes F s)
    (hxL : (F.N : ℝ) / 5 ≤ (x : ℝ)) (hxU : (x : ℝ) ≤ (F.N : ℝ) / 4)
    (heven : Even F.N) :
    physicalPrimeMass F s (sourceSieveCutoff21 F.N) (frameInterval F s x) ≤
      constructedSelbergMain F s (sourceSieveCutoff21 F.N) x -
        constructedCompositeMain F s (sourceSieveCutoff21 F.N) x P K +
          selbergAPPrice F s (sourceSieveCutoff21 F.N) x +
            compositeSignedAPPrice F s (sourceSieveCutoff21 F.N) x P K -
              physicalLargeCompositeMass F s (sourceSieveCutoff21 F.N) P (frameInterval F s x) := by
  obtain ⟨hxN, hx2, hfront⟩ := source_frame_front_guards h hxL hxU
  exact switchedIncidenceEstimator_APprices h ha haxes hxN hx2 hfront heven (source_sieve_cutoff_one h)

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.sourceSieveCutoff21
#print axioms GoldbachRound21.PhysicalAP.source_N_ge_twenty
#print axioms GoldbachRound21.PhysicalAP.source_sieve_cutoff_le_N_div_ten
#print axioms GoldbachRound21.PhysicalAP.source_frame_front_guards
#print axioms GoldbachRound21.PhysicalAP.source_sieve_cutoff_one
#print axioms GoldbachRound21.PhysicalAP.source_actualPrimeAP_B6
#print axioms GoldbachRound21.PhysicalAP.source_actualCompositeAP_B6
#print axioms GoldbachRound21.PhysicalAP.source_switchedIncidenceEstimator_APprices

end
end GoldbachRound21.PhysicalAP
