import Mathlib

namespace GoldbachRound17.PowersetMoment
open Finset
open scoped BigOperators
noncomputable section

def subsetWeight (h : ℕ → ℝ) (s : Finset ℕ) : ℝ := ∏ p ∈ s, h p
def subsetLog (s : Finset ℕ) : ℝ := ∑ p ∈ s, Real.log p

theorem total_weight (P : Finset ℕ) (h : ℕ → ℝ) :
    (∑ s ∈ P.powerset, subsetWeight h s) = ∏ p ∈ P, (1+h p) := by
  exact (Finset.prod_one_add P).symm

theorem weighted_moment (P : Finset ℕ) (h L : ℕ → ℝ)
    (hh : ∀ p ∈ P, 0 ≤ h p) :
    (∑ s ∈ P.powerset, subsetWeight h s * (∑ p ∈ s, L p)) =
      (∏ p ∈ P, (1+h p)) * (∑ p ∈ P, h p/(1+h p)*L p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [subsetWeight]
  | @insert a P ha ih =>
    have hha : 0 ≤ h a := hh a (Finset.mem_insert_self a P)
    have hhP : ∀ p ∈ P, 0 ≤ h p := fun p hp => hh p (Finset.mem_insert_of_mem hp)
    have hne : 1+h a ≠ 0 := by linarith
    have hinsert : ∀ s ∈ P.powerset,
        subsetWeight h (insert a s) * (∑ p ∈ insert a s, L p) =
          h a * L a * subsetWeight h s + h a * (subsetWeight h s * (∑ p ∈ s, L p)) := by
      intro s hs
      have has : a ∉ s := fun hmem => ha ((Finset.mem_powerset.mp hs) hmem)
      rw [subsetWeight, Finset.prod_insert has, Finset.sum_insert has]
      dsimp [subsetWeight]
      ring
    rw [Finset.sum_powerset_insert ha]
    rw [Finset.sum_congr rfl hinsert]
    rw [Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
    rw [total_weight, ih hhP, Finset.prod_insert ha, Finset.sum_insert ha]
    field_simp
    ring

theorem subsetLog_nonneg (s : Finset ℕ) : 0 ≤ subsetLog s := by
  exact Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p

theorem log_primeProduct (s : Finset ℕ) (hp : ∀ p ∈ s, 0 < p) :
    Real.log (((∏ p ∈ s, p) : ℕ) : ℝ) = subsetLog s := by
  rw [Nat.cast_prod]
  exact Real.log_prod s (fun p => (p : ℝ)) (fun p hmem => by
    change (p : ℝ) ≠ 0
    exact_mod_cast (hp p hmem).ne')

theorem cutoff_markov (P : Finset ℕ) (h : ℕ → ℝ) (z : ℕ)
    (hh : ∀ p ∈ P, 0 ≤ h p) (hp : ∀ p ∈ P, 0 < p)
    (hz : 0 < (z : ℝ)) (hT : 0 < Real.log z)
    (hm : (∑ s ∈ P.powerset, subsetWeight h s * subsetLog s) ≤
      Real.log z / 2 * (∑ s ∈ P.powerset, subsetWeight h s)) :
    (∑ s ∈ P.powerset, subsetWeight h s) / 2 ≤
      ∑ s ∈ P.powerset.filter (fun s => (∏ p ∈ s, p) ≤ z), subsetWeight h s := by
  classical
  have hpoint : ∀ s ∈ P.powerset,
      Real.log z * subsetWeight h s ≤
        Real.log z * (if (∏ p ∈ s, p) ≤ z then subsetWeight h s else 0) +
          subsetWeight h s * subsetLog s := by
    intro s hs
    have hsub : s ⊆ P := Finset.mem_powerset.mp hs
    have hw : 0 ≤ subsetWeight h s := Finset.prod_nonneg fun p hmem => hh p (hsub hmem)
    by_cases hcut : (∏ p ∈ s, p) ≤ z
    · rw [if_pos hcut]
      nlinarith [mul_nonneg hw (subsetLog_nonneg s)]
    · rw [if_neg hcut, mul_zero, zero_add]
      have hpr : 0 < (∏ p ∈ s, p : ℕ) := Finset.prod_pos fun p hmem => hp p (hsub hmem)
      have hprR : 0 < ((∏ p ∈ s, p : ℕ) : ℝ) := by exact_mod_cast hpr
      have hlt : (z : ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by exact_mod_cast (lt_of_not_ge hcut)
      have hlog : Real.log z ≤ subsetLog s := by
        rw [← log_primeProduct s (fun p hmem => hp p (hsub hmem))]
        exact (Real.log_le_log hz hlt.le)
      nlinarith
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hfilter :
      (∑ s ∈ P.powerset, if (∏ p ∈ s, p) ≤ z then subsetWeight h s else 0) =
      ∑ s ∈ P.powerset.filter (fun s => (∏ p ∈ s, p) ≤ z), subsetWeight h s := by
    rw [Finset.sum_filter]
  rw [hfilter] at hs
  nlinarith

#print axioms subsetWeight
#print axioms subsetLog
#print axioms total_weight
#print axioms weighted_moment
#print axioms subsetLog_nonneg
#print axioms log_primeProduct
#print axioms cutoff_markov

end
end GoldbachRound17.PowersetMoment
