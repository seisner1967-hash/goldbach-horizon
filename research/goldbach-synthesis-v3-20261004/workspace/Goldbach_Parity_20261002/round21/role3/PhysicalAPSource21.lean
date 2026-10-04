import PhysicalAPAbel21

namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset MeasureTheory
open GoldbachRound18.SeparatedTypeII
open GoldbachRound20.SwitchedComposite
open GoldbachRound20.Friable.SourceGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

theorem radical_log_sum_le {N : ℕ} (hN : N ≠ 0) :
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ)) ≤ Real.log (N : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ N.primeFactors, Real.log (p : ℝ)) ≤
    ∑ p ∈ N.factorization.support, (N.factorization p : ℝ) * Real.log (p : ℝ)
  rw [Nat.support_factorization]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have he : (1 : ℝ) ≤ N.factorization p := by
    exact_mod_cast (Nat.succ_le_of_lt (hpp.factorization_pos_of_dvd hN hpd))
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  simpa using mul_le_mul_of_nonneg_right he hlog

theorem physicalLogWeight_prime_product {N t nu q : ℕ}
    (hp : q.Prime) (hc : Nat.ModEq nu (t * q) N)
    (hj : 1 < (N : ℝ) - (t : ℝ) * q) :
    physicalLogWeight N t q * Real.log (q : ℝ) =
      Real.log ((N - t * q : ℕ) : ℝ) := by
  have h := ordinaryWeightedAP_eq_unmasked (N := N) (t := t) (nu := nu)
    (L := q) (U := q) hp.two_le hj
  simpa [ordinaryWeightedAP, ordinaryPrimeCoefficient, unmaskedAPMass, hp, hc] using h

theorem retiredAPMass_source_bounds {N t nu L U : ℕ}
    (h : SourceOnset N) (hLU : L ≤ U)
    (hAa : (sourceA N : ℝ) ≤ (L : ℝ) - 1)
    (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    0 ≤ retiredAPMass N t nu L U ∧
      retiredAPMass N t nu L U ≤ (16 / 7 : ℝ) * sourceU N := by
  let S := (Icc L U).filter (fun q => q.Prime ∧ q ∣ N ∧ Nat.ModEq nu (t * q) N)
  have hS : S ⊆ N.primeFactors := by
    intro q hq
    obtain ⟨_, hp, hd, _⟩ := mem_filter.mp hq
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, (source_N_pos h).ne'⟩
  have hmass : retiredAPMass N t nu L U = ∑ q ∈ S, Real.log ((N - t * q : ℕ) : ℝ) := by
    dsimp [S]
    rw [sum_filter]
    rfl
  have hpoint (q : ℕ) (hq : q ∈ S) :
      0 ≤ Real.log ((N - t * q : ℕ) : ℝ) ∧
        Real.log ((N - t * q : ℕ) : ℝ) ≤ (16 / 7 : ℝ) * Real.log (q : ℝ) := by
    obtain ⟨hI, hp, _, hc⟩ := mem_filter.mp hq
    obtain ⟨hl, hu⟩ := mem_Icc.mp hI
    have hqU : (q : ℝ) ≤ U := by exact_mod_cast hu
    have hLq : (L : ℝ) ≤ q := by exact_mod_cast hl
    have hAq : (L : ℝ) - 1 ≤ q := by linarith
    have hj : 1 < (N : ℝ) - (t : ℝ) * q := by
      nlinarith [Nat.cast_nonneg t]
    have hf := source_physicalLogWeight_le h hAa hAq hj
    have hq1 : 1 < (q : ℝ) := by exact_mod_cast hp.one_lt
    have hf0 := physicalLogWeight_nonneg hq1 hj
    have hl0 : 0 ≤ Real.log (q : ℝ) := (Real.log_pos hq1).le
    rw [← physicalLogWeight_prime_product hp hc hj]
    exact ⟨mul_nonneg hf0 hl0, mul_le_mul_of_nonneg_right hf hl0⟩
  have hlogs : (∑ q ∈ S, Real.log (q : ℝ)) ≤ Real.log (N : ℝ) := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg hS ?_) (radical_log_sum_le (source_N_pos h).ne')
    intro q hq _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
  rw [hmass]
  constructor
  · exact sum_nonneg fun q hq => (hpoint q hq).1
  · calc
      _ ≤ ∑ q ∈ S, (16 / 7 : ℝ) * Real.log (q : ℝ) :=
        sum_le_sum fun q hq => (hpoint q hq).2
      _ = (16 / 7 : ℝ) * ∑ q ∈ S, Real.log (q : ℝ) := (mul_sum _ _ _).symm
      _ ≤ (16 / 7 : ℝ) * sourceU N := mul_le_mul_of_nonneg_left hlogs (by norm_num)

theorem primeUnitAP_source_bound {N t nu L U : ℕ}
    (h : SourceOnset N) (hnu : 0 < nu) (hLU : L ≤ U)
    (hAa : (sourceA N : ℝ) ≤ (L : ℝ) - 1)
    (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    |primeUnitAPMass N t nu L U -
      (∫ y in ((L : ℝ) - 1)..(U : ℝ), physicalLogWeight N t y) / (Nat.totient nu : ℝ)| ≤
        (32 / 7 : ℝ) * physicalAPEnvelope N t nu U + (16 / 7 : ℝ) * sourceU N := by
  have hA : 1 < (L : ℝ) - 1 := (source_a_real_one h).trans_le hAa
  have hL : 2 < L := by
    have hLc : (2 : ℝ) < L := by linarith
    exact_mod_cast hLc
  have hjA : 1 < (N : ℝ) - (t : ℝ) * ((L : ℝ) - 1) := by
    have hLc : (L : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith [Nat.cast_nonneg t]
  have hw := weightedAP_error_bound hnu hLU hL hU
  have hf := source_physicalLogWeight_le h hAa le_rfl hjA
  have hE := physicalAPEnvelope_nonneg N t nu U
  obtain ⟨hC0, hC⟩ := retiredAPMass_source_bounds h hLU hAa hU
  rw [primeUnitAPMass_retirement,
    ← ordinaryWeightedAP_eq_unmasked (by omega) hU]
  have htriangle := abs_sub
    (ordinaryWeightedAP N t nu L U -
      (∫ y in ((L : ℝ) - 1)..(U : ℝ), physicalLogWeight N t y) / (Nat.totient nu : ℝ))
    (retiredAPMass N t nu L U)
  rw [abs_of_nonneg hC0] at htriangle
  have hprod := mul_le_mul_of_nonneg_right hf hE
  convert htriangle.trans (add_le_add hw hC) |>.trans ?_ using 1
  · congr 1; ring
  · nlinarith

theorem frame_source_guards {F : Parameters} {s x : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hLU : frameLower F s x ≤ frameUpper F s x) :
    (sourceA F.N : ℝ) ≤ (frameLower F s x : ℝ) - 1 ∧
      1 < (F.N : ℝ) - (switchedConductor F s : ℝ) * frameUpper F s x := by
  have hL : F.a + 1 ≤ frameLower F s x := le_max_left _ _
  have hAa : (sourceA F.N : ℝ) ≤ (frameLower F s x : ℝ) - 1 := by
    rw [ha] at hL
    have hc : (sourceA F.N : ℝ) + 1 ≤ frameLower F s x := by exact_mod_cast hL
    linarith
  have hUpos : 0 < frameUpper F s x := by
    have ha1 := source_a_one h
    rw [← ha] at ha1
    omega
  have hUm : frameUpper F s x ∈ frameInterval F s x := mem_Icc.mpr ⟨hLU, le_rfl⟩
  obtain ⟨hj, _, hf⟩ := frameCandidate_bounds haxes.conductor_pos hUpos hx hUm
  have htN : switchedConductor F s * frameUpper F s x ≤ F.N := by omega
  have hcast : (switchedCandidate F s (frameUpper F s x) : ℝ) =
      (F.N : ℝ) - (switchedConductor F s : ℝ) * frameUpper F s x := by
    unfold switchedCandidate
    rw [Nat.cast_sub htN, Nat.cast_mul]
  have hj1 : 1 < switchedCandidate F s (frameUpper F s x) := by omega
  exact ⟨hAa, by rw [← hcast]; exact_mod_cast hj1⟩

theorem compatible_source_modulus_pos {F : Parameters} {s nu : ℕ}
    (h : SourceOnset F.N) (haxes : StaticAxes F s)
    (hn : Nat.Coprime nu (switchedConductor F s * F.N)) : 0 < nu := by
  by_contra hnu
  have hz : nu = 0 := Nat.eq_zero_of_not_pos hnu
  rw [hz] at hn
  have he : switchedConductor F s * F.N = 1 := hn.coprime_zero_left.mp (by rfl)
  have hN : 1 < F.N := by exact_mod_cast source_N_real_one h
  have ht := haxes.conductor_pos
  nlinarith

theorem actualPrimeAP_B6 {F : Parameters} {s z x nu : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hfront : max 1 z < x / 2 + 1) :
    |actualPrimeAP F s z nu (frameInterval F s x) - actualAPMain F s x nu| ≤
      if Nat.Coprime nu (switchedConductor F s * F.N) then
        (32 / 7 : ℝ) * physicalAPEnvelope F.N (switchedConductor F s) nu (frameUpper F s x) +
          (16 / 7 : ℝ) * sourceU F.N else 0 := by
  by_cases hn : Nat.Coprime nu (switchedConductor F s * F.N)
  · rw [if_pos hn, actualPrimeAP_frame_reindex haxes hx hfront]
    unfold actualAPMain compatibleAPMain logarithmicAPIntegral
    rw [if_pos hn]
    by_cases hLU : frameLower F s x ≤ frameUpper F s x
    · rw [if_pos hLU]
      obtain ⟨hAa, hU⟩ := frame_source_guards h ha haxes hx hx2 hLU
      exact primeUnitAP_source_bound h (compatible_source_modulus_pos h haxes hn) hLU hAa hU
    · rw [if_neg hLU]
      simp only [primeUnitAPMass, Icc_eq_empty_of_lt (Nat.lt_of_not_ge hLU), filter_empty,
        sum_empty, zero_div, sub_zero, abs_zero]
      exact add_nonneg (mul_nonneg (by norm_num) (physicalAPEnvelope_nonneg _ _ _ _))
        (mul_nonneg (by norm_num) (source_u_pos h).le)
  · rw [if_neg hn, actualPrimeAP_nonunit_zero F s z nu _ hn]
    simp [actualAPMain, compatibleAPMain, hn]

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.radical_log_sum_le
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_prime_product
#print axioms GoldbachRound21.PhysicalAP.retiredAPMass_source_bounds
#print axioms GoldbachRound21.PhysicalAP.primeUnitAP_source_bound
#print axioms GoldbachRound21.PhysicalAP.frame_source_guards
#print axioms GoldbachRound21.PhysicalAP.compatible_source_modulus_pos
#print axioms GoldbachRound21.PhysicalAP.actualPrimeAP_B6

end
end GoldbachRound21.PhysicalAP
