import PhysicalAPSource21

namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset MeasureTheory
open GoldbachRound18.SeparatedTypeII
open GoldbachRound20.SwitchedComposite
open GoldbachRound20.Friable.SourceGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

def primeAPPrice (F : Parameters) (s x nu : ℕ) : ℝ :=
  if Nat.Coprime nu (switchedConductor F s * F.N) ∧ frameLower F s x ≤ frameUpper F s x then
    (32 / 7 : ℝ) * physicalAPEnvelope F.N (switchedConductor F s) nu (frameUpper F s x) +
      (16 / 7 : ℝ) * sourceU F.N else 0

def compositeAPPrice (F : Parameters) (s x k l h p : ℕ) : ℝ :=
  let nu := compositeAPConductor k l h p
  let U := min (frameUpper F s x) ((F.N - p ^ 2) / switchedConductor F s)
  if Nat.Coprime nu (switchedConductor F s * F.N) ∧ p ^ 2 ≤ F.N ∧ frameLower F s x ≤ U then
    (32 / 7 : ℝ) * physicalAPEnvelope F.N (switchedConductor F s) nu U +
      (16 / 7 : ℝ) * sourceU F.N else 0

def selbergAPPrice (F : Parameters) (s z x : ℕ) : ℝ :=
  ∑ d ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
    ∑ e ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
      |switchedLambda F.N (switchedConductor F s) z d *
        switchedLambda F.N (switchedConductor F s) z e| *
          primeAPPrice F s x (Nat.lcm (primeProduct d) (primeProduct e))

def compositeSignedAPPrice (F : Parameters) (s z x P K : ℕ) : ℝ :=
  ∑ p ∈ compositePrimeCatalogue F.N (switchedConductor F s) P,
    ∑ d ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
      ∑ e ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
        ∑ h ∈ (smallSievePrimes F.N (switchedConductor F s) p).powerset,
          if h.card ≤ 2 * K + 1 then
            |switchedLambda F.N (switchedConductor F s) z d *
              switchedLambda F.N (switchedConductor F s) z e *
                (ArithmeticFunction.moebius (primeProduct h) : ℝ)| *
                  compositeAPPrice F s x (primeProduct d) (primeProduct e) (primeProduct h) p
          else 0

theorem actualCompositeAP_nonunit_zero (F : Parameters) (s z k l h p : ℕ) (J : Finset ℕ)
    (hn : ¬ Nat.Coprime (compositeAPConductor k l h p) (switchedConductor F s * F.N)) :
    actualCompositeAP F s z k l h p J = 0 := by
  unfold actualCompositeAP
  apply sum_eq_zero
  intro q hq
  have hbase : q ∈ physicalQDomain F s z J := (mem_filter.mp hq).1
  simp [physical_nonunit_conductor_zero hbase hn]

theorem actualPrimeAP_price_bound {F : Parameters} {s z x nu : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hfront : max 1 z < x / 2 + 1) :
    |actualPrimeAP F s z nu (frameInterval F s x) - actualAPMain F s x nu| ≤
      primeAPPrice F s x nu := by
  by_cases hn : Nat.Coprime nu (switchedConductor F s * F.N)
  · by_cases hLU : frameLower F s x ≤ frameUpper F s x
    · simpa [primeAPPrice, hn, hLU] using actualPrimeAP_B6 h ha haxes hx hx2 hfront
    · have he : frameInterval F s x = ∅ := Icc_eq_empty_of_lt (Nat.lt_of_not_ge hLU)
      simp [primeAPPrice, hLU, actualPrimeAP, physicalQDomain, he,
        actualAPMain, compatibleAPMain, logarithmicAPIntegral]
  · simp [primeAPPrice, hn, actualPrimeAP_nonunit_zero F s z nu _ hn,
      actualAPMain, compatibleAPMain]

theorem actualCompositeAP_B6 {F : Parameters} {s z x k l h p : ℕ}
    (hs : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hfront : max 1 z < x / 2 + 1) :
    |actualCompositeAP F s z k l h p (frameInterval F s x) -
      compatibleAPMain F s (compositeAPConductor k l h p) (compositeAPIntegral F s x p)| ≤
        compositeAPPrice F s x k l h p := by
  let nu := compositeAPConductor k l h p
  let U := min (frameUpper F s x) ((F.N - p ^ 2) / switchedConductor F s)
  by_cases hn : Nat.Coprime nu (switchedConductor F s * F.N)
  · by_cases hpN : p ^ 2 ≤ F.N
    · by_cases hLU : frameLower F s x ≤ U
      · have hLUfull : frameLower F s x ≤ frameUpper F s x := hLU.trans (min_le_left _ _)
        obtain ⟨hAa, hUfull⟩ := frame_source_guards hs ha haxes hx hx2 hLUfull
        have hU : 1 < (F.N : ℝ) - (switchedConductor F s : ℝ) * U := by
          have hc : (U : ℝ) ≤ frameUpper F s x := by exact_mod_cast min_le_left _ _
          nlinarith [Nat.cast_nonneg (switchedConductor F s)]
        rw [actualCompositeAP_frame_reindex haxes hx hfront, if_pos hpN]
        simpa only [compositeAPPrice, nu, U, hn, hpN, hLU, and_self, if_true,
          compatibleAPMain, compositeAPIntegral, logarithmicAPIntegral, physicalLogWeight]
          using primeUnitAP_source_bound hs (compatible_source_modulus_pos hs haxes hn) hLU hAa hU
      · rw [actualCompositeAP_frame_reindex haxes hx hfront, if_pos hpN]
        simp [compositeAPPrice, nu, U, hn, hpN, hLU, primeUnitAPMass,
          Icc_eq_empty_of_lt (Nat.lt_of_not_ge hLU), compatibleAPMain,
          compositeAPIntegral, logarithmicAPIntegral]
    · rw [actualCompositeAP_frame_reindex haxes hx hfront, if_neg hpN]
      simp [compositeAPPrice, nu, U, hpN, compatibleAPMain, compositeAPIntegral]
  · have hz := actualCompositeAP_nonunit_zero F s z k l h p (frameInterval F s x) hn
    simp [compositeAPPrice, nu, U, hn, hz, compatibleAPMain]

theorem actualSelbergRemainder_literal (F : Parameters) (s z x : ℕ) :
    actualSelbergRemainder F s z x =
      ∑ d ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
        ∑ e ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
          (switchedLambda F.N (switchedConductor F s) z d *
            switchedLambda F.N (switchedConductor F s) z e) *
              (actualPrimeAP F s z (Nat.lcm (primeProduct d) (primeProduct e)) (frameInterval F s x) -
                actualAPMain F s x (Nat.lcm (primeProduct d) (primeProduct e))) := by
  unfold actualSelbergRemainder
  rw [physicalSelbergMass_AP_expansion]
  unfold constructedSelbergMain
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  ring

theorem actualCompositeRemainder_literal (F : Parameters) (s z x P K : ℕ) :
    actualCompositeRemainder F s z x P K =
      ∑ p ∈ compositePrimeCatalogue F.N (switchedConductor F s) P,
        ∑ d ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
          ∑ e ∈ (switchedPrimeSupport F.N (switchedConductor F s) z).powerset,
            ∑ h ∈ (smallSievePrimes F.N (switchedConductor F s) p).powerset,
              if h.card ≤ 2 * K + 1 then
                (switchedLambda F.N (switchedConductor F s) z d *
                  switchedLambda F.N (switchedConductor F s) z e *
                    (ArithmeticFunction.moebius (primeProduct h) : ℝ)) *
                      (actualCompositeAP F s z (primeProduct d) (primeProduct e) (primeProduct h) p
                        (frameInterval F s x) - compatibleAPMain F s
                          (compositeAPConductor (primeProduct d) (primeProduct e) (primeProduct h) p)
                          (compositeAPIntegral F s x p))
              else 0 := by
  unfold actualCompositeRemainder
  rw [physicalLowerCompositeMass_AP_expansion]
  unfold constructedCompositeMain
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro h hh
  split_ifs <;> ring

theorem actualSelbergRemainder_le_price {F : Parameters} {s z x : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hfront : max 1 z < x / 2 + 1) :
    |actualSelbergRemainder F s z x| ≤ selbergAPPrice F s z x := by
  rw [actualSelbergRemainder_literal]
  unfold selbergAPPrice
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro d hd
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro e he
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (actualPrimeAP_price_bound h ha haxes hx hx2 hfront) (abs_nonneg _)

theorem actualCompositeRemainder_le_price {F : Parameters} {s z x P K : ℕ}
    (hs : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hfront : max 1 z < x / 2 + 1) :
    |actualCompositeRemainder F s z x P K| ≤ compositeSignedAPPrice F s z x P K := by
  rw [actualCompositeRemainder_literal]
  unfold compositeSignedAPPrice
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro p hp
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro d hd
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro e he
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro h hh
  by_cases hc : h.card ≤ 2 * K + 1
  · rw [if_pos hc, if_pos hc, abs_mul]
    exact mul_le_mul_of_nonneg_left (actualCompositeAP_B6 hs ha haxes hx hx2 hfront) (abs_nonneg _)
  · simp [hc]

theorem switchedIncidenceEstimator_APprices {F : Parameters} {s z x P K : ℕ}
    (h : SourceOnset F.N) (ha : F.a = sourceA F.N)
    (haxes : StaticAxes F s) (hx : x ≤ F.N) (hx2 : 2 ≤ x / 2)
    (hfront : max 1 z < x / 2 + 1) (heven : Even F.N) (hz : 1 ≤ z) :
    physicalPrimeMass F s z (frameInterval F s x) ≤
      constructedSelbergMain F s z x - constructedCompositeMain F s z x P K +
        selbergAPPrice F s z x + compositeSignedAPPrice F s z x P K -
          physicalLargeCompositeMass F s z P (frameInterval F s x) := by
  have he := switchedIncidenceEstimator F s z x P K heven hz
  have hQ := actualSelbergRemainder_le_price h ha haxes hx hx2 hfront
  have hC := actualCompositeRemainder_le_price h ha haxes hx hx2 hfront
  linarith

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.primeAPPrice
#print axioms GoldbachRound21.PhysicalAP.compositeAPPrice
#print axioms GoldbachRound21.PhysicalAP.selbergAPPrice
#print axioms GoldbachRound21.PhysicalAP.compositeSignedAPPrice
#print axioms GoldbachRound21.PhysicalAP.actualCompositeAP_nonunit_zero
#print axioms GoldbachRound21.PhysicalAP.actualPrimeAP_price_bound
#print axioms GoldbachRound21.PhysicalAP.actualCompositeAP_B6
#print axioms GoldbachRound21.PhysicalAP.actualSelbergRemainder_literal
#print axioms GoldbachRound21.PhysicalAP.actualCompositeRemainder_literal
#print axioms GoldbachRound21.PhysicalAP.actualSelbergRemainder_le_price
#print axioms GoldbachRound21.PhysicalAP.actualCompositeRemainder_le_price
#print axioms GoldbachRound21.PhysicalAP.switchedIncidenceEstimator_APprices

end
end GoldbachRound21.PhysicalAP
