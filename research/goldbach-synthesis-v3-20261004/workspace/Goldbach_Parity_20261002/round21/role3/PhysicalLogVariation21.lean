import PhysicalAPEnvelope21
import FriableSourceGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-! The actual logarithmic weight and its source bound. The only source size
premise is the fixed onset, never a premise saying an AP remainder is small. -/
namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset MeasureTheory
open GoldbachRound20.Friable.SourceGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

def physicalLogWeight (N t : ℕ) (y : ℝ) : ℝ :=
  Real.log ((N : ℝ) - (t : ℝ) * y) / Real.log y

def physicalLogWeightDerivative (N t : ℕ) (y : ℝ) : ℝ :=
  -(t : ℝ) / (((N : ℝ) - (t : ℝ) * y) * Real.log y) -
    Real.log ((N : ℝ) - (t : ℝ) * y) / (y * (Real.log y) ^ 2)

theorem physicalLogWeight_hasDerivAt {N t : ℕ} {y : ℝ}
    (hy : 1 < y) (hj : 1 < (N : ℝ) - (t : ℝ) * y) :
    HasDerivAt (physicalLogWeight N t) (physicalLogWeightDerivative N t y) y := by
  have hy0 : y ≠ 0 := (zero_lt_one.trans hy).ne'
  have hj0 : (N : ℝ) - (t : ℝ) * y ≠ 0 := (zero_lt_one.trans hj).ne'
  have hlog : Real.log y ≠ 0 := (Real.log_pos hy).ne'
  have ha : HasDerivAt (fun x : ℝ => (N : ℝ) - (t : ℝ) * x) (-(t : ℝ)) y := by
    convert (hasDerivAt_const y (N : ℝ)).sub ((hasDerivAt_id y).const_mul (t : ℝ)) using 1 <;> simp
  have hd := (ha.log hj0).div (Real.hasDerivAt_log hy0) hlog
  convert hd using 1
  · rfl
  · unfold physicalLogWeightDerivative
    field_simp
    ring

theorem physicalLogWeight_range_guards {N t : ℕ} {A U y : ℝ}
    (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U)
    (hy : y ∈ Set.Icc A U) :
    1 < y ∧ 1 < (N : ℝ) - (t : ℝ) * y := by
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  constructor
  · exact hA.trans_le hy.1
  · nlinarith [hy.2]

theorem physicalLogWeight_nonneg {N t : ℕ} {y : ℝ}
    (hy : 1 < y) (hj : 1 < (N : ℝ) - (t : ℝ) * y) :
    0 ≤ physicalLogWeight N t y :=
  div_nonneg (Real.log_pos hj).le (Real.log_pos hy).le

theorem physicalLogWeightDerivative_nonpos {N t : ℕ} {y : ℝ}
    (hy : 1 < y) (hj : 1 < (N : ℝ) - (t : ℝ) * y) :
    physicalLogWeightDerivative N t y ≤ 0 := by
  unfold physicalLogWeightDerivative
  have hden1 : 0 < ((N : ℝ) - (t : ℝ) * y) * Real.log y :=
    mul_pos (zero_lt_one.trans hj) (Real.log_pos hy)
  have hden2 : 0 < y * (Real.log y) ^ 2 :=
    mul_pos (zero_lt_one.trans hy) (sq_pos_of_pos (Real.log_pos hy))
  have hfirst : -(t : ℝ) / (((N : ℝ) - (t : ℝ) * y) * Real.log y) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hden1.le
  have hsecond : 0 ≤ Real.log ((N : ℝ) - (t : ℝ) * y) / (y * (Real.log y) ^ 2) :=
    div_nonneg (Real.log_pos hj).le hden2.le
  linarith

theorem physicalLogWeight_continuousOn {N t : ℕ} {A U : ℝ}
    (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    ContinuousOn (physicalLogWeight N t) (Set.Icc A U) := by
  intro y hy
  obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hy
  exact (physicalLogWeight_hasDerivAt hy1 hj1).continuousAt.continuousWithinAt

theorem physicalLogWeightDerivative_continuousOn {N t : ℕ} {A U : ℝ}
    (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    ContinuousOn (physicalLogWeightDerivative N t) (Set.Icc A U) := by
  have hlin : ContinuousOn (fun y : ℝ => (N : ℝ) - (t : ℝ) * y) (Set.Icc A U) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  have hid : ContinuousOn (fun y : ℝ => y) (Set.Icc A U) := continuous_id.continuousOn
  have hlog : ContinuousOn Real.log (Set.Icc A U) := hid.log fun y hy => by
    exact (zero_lt_one.trans (physicalLogWeight_range_guards hA hU hy).1).ne'
  have hloglin := hlin.log fun y hy => by
    exact (zero_lt_one.trans (physicalLogWeight_range_guards hA hU hy).2).ne'
  unfold physicalLogWeightDerivative
  apply ContinuousOn.sub
  · apply continuous_const.continuousOn.div (hlin.mul hlog)
    intro y hy
    obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hy
    exact (mul_pos (zero_lt_one.trans hj1) (Real.log_pos hy1)).ne'
  · apply hloglin.div (hid.mul (hlog.pow 2))
    intro y hy
    obtain ⟨hy1, _⟩ := physicalLogWeight_range_guards hA hU hy
    exact (mul_pos (zero_lt_one.trans hy1) (sq_pos_of_pos (Real.log_pos hy1))).ne'

theorem physicalLogWeight_derivOn {N t : ℕ} {A U : ℝ}
    (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U)
    {y : ℝ} (hy : y ∈ Set.Icc A U) :
    deriv (physicalLogWeight N t) y = physicalLogWeightDerivative N t y := by
  obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hy
  exact (physicalLogWeight_hasDerivAt hy1 hj1).deriv

theorem physicalLogWeight_deriv_integrableOn {N t : ℕ} {A U : ℝ}
    (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    IntegrableOn (deriv (physicalLogWeight N t)) (Set.Icc A U) := by
  have hd := (physicalLogWeightDerivative_continuousOn hA hU).integrableOn_Icc
  apply hd.congr
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  exact ae_of_all _ fun y hy => (physicalLogWeight_derivOn hA hU hy).symm

theorem physicalLogWeight_antitoneOn {N t : ℕ} {A U : ℝ}
    (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    AntitoneOn (physicalLogWeight N t) (Set.Icc A U) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc A U)
    (physicalLogWeight_continuousOn hA hU)
  · intro y hy
    have hmem := interior_subset hy
    obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hmem
    exact (physicalLogWeight_hasDerivAt hy1 hj1).differentiableAt.differentiableWithinAt
  · intro y hy
    have hmem := interior_subset hy
    rw [physicalLogWeight_derivOn hA hU hmem]
    obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hmem
    exact physicalLogWeightDerivative_nonpos hy1 hj1

theorem physicalLogWeight_variation {N t : ℕ} {A U : ℝ}
    (hAU : A ≤ U) (hA : 1 < A) (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    (∫ y in A..U, |deriv (physicalLogWeight N t) y|) =
      physicalLogWeight N t A - physicalLogWeight N t U := by
  have hdiff : ∀ y ∈ Set.uIcc A U, DifferentiableAt ℝ (physicalLogWeight N t) y := by
    rw [Set.uIcc_of_le hAU]
    intro y hy
    obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hy
    exact (physicalLogWeight_hasDerivAt hy1 hj1).differentiableAt
  have hint : IntervalIntegrable (deriv (physicalLogWeight N t)) volume A U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAU).mpr
      (physicalLogWeight_deriv_integrableOn hA hU)
  have hsign : ∀ y ∈ Set.Icc A U, deriv (physicalLogWeight N t) y ≤ 0 := by
    intro y hy
    rw [physicalLogWeight_derivOn hA hU hy]
    obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hy
    exact physicalLogWeightDerivative_nonpos hy1 hj1
  calc
    (∫ y in A..U, |deriv (physicalLogWeight N t) y|) =
        ∫ y in A..U, -deriv (physicalLogWeight N t) y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hAU] at hy
      exact abs_of_nonpos (hsign y hy)
    _ = -(physicalLogWeight N t U - physicalLogWeight N t A) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub hdiff hint]
    _ = physicalLogWeight N t A - physicalLogWeight N t U := by ring

theorem source_a_log {N : ℕ} (h : SourceOnset N) :
    (7 / 16 : ℝ) * sourceU N ≤ Real.log (sourceA N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast source_N_pos h
  calc
    (7 / 16 : ℝ) * sourceU N = Real.log ((N : ℝ) ^ (7 / 16 : ℝ)) := by
      rw [Real.log_rpow hn]
      rfl
    _ ≤ Real.log (sourceA N : ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos hn _) (Nat.le_ceil _)

theorem source_a_real_one {N : ℕ} (h : SourceOnset N) :
    1 < (sourceA N : ℝ) := by
  have hlog := source_a_log h
  have hu := source_u_pos h
  have ha : 0 < (sourceA N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (source_a_one h))
  apply (Real.log_pos_iff ha).mp
  linarith

theorem source_physicalLogWeight_le {N t : ℕ} {A y : ℝ}
    (h : SourceOnset N) (hAa : (sourceA N : ℝ) ≤ A) (hAy : A ≤ y)
    (hj : 1 < (N : ℝ) - (t : ℝ) * y) :
    physicalLogWeight N t y ≤ 16 / 7 := by
  have hay := hAa.trans hAy
  have hy1 : 1 < y := (source_a_real_one h).trans_le hay
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hloga := (source_a_log h).trans
    (Real.log_le_log (zero_lt_one.trans (source_a_real_one h)) hay)
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hjN : (N : ℝ) - (t : ℝ) * y ≤ N := by
    nlinarith [zero_lt_one.trans hy1]
  have hnum : Real.log ((N : ℝ) - (t : ℝ) * y) ≤ sourceU N :=
    Real.log_le_log (zero_lt_one.trans hj) hjN
  unfold physicalLogWeight
  apply (div_le_iff₀ hlog).mpr
  linarith

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeightDerivative
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_hasDerivAt
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_range_guards
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_nonneg
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeightDerivative_nonpos
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_continuousOn
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeightDerivative_continuousOn
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_derivOn
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_deriv_integrableOn
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_antitoneOn
#print axioms GoldbachRound21.PhysicalAP.physicalLogWeight_variation
#print axioms GoldbachRound21.PhysicalAP.source_a_log
#print axioms GoldbachRound21.PhysicalAP.source_a_real_one
#print axioms GoldbachRound21.PhysicalAP.source_physicalLogWeight_le

end
end GoldbachRound21.PhysicalAP
