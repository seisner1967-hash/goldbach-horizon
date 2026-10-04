import EpsteinUnfold22

/-! The tail is derived from the exact endpoint formula and positive deficits.
No remainder estimate or target inequality is assumed as a premise. -/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Epstein22

def endpointDeficit (a : ℝ) (Q q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q,
    ((1 - boundary a ((Q : ℝ) + 1 + i)) +
      (1 + boundary a (-(Q : ℝ) + i)))

def truncationEnvelope (y : ℝ) (Q q : ℕ) : ℝ :=
  weight y / ((Q : ℝ) - q) ^ 2

theorem endpointSum_range (a : ℝ) (Q q : ℕ) :
    endpointSum a Q q = ∑ i ∈ Finset.range q,
      (boundary a ((Q : ℝ) + 1 + i) - boundary a (-(Q : ℝ) + i)) := by
  have ht : ((Q : ℤ) + (q : ℤ) + 1 - ((Q : ℤ) + 1)).toNat = q := by omega
  have hb : (-(Q : ℤ) + (q : ℤ) - 1 + 1 - (-(Q : ℤ))).toNat = q := by omega
  unfold endpointSum
  rw [sum_int_Icc, sum_int_Icc, ht, hb, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast, Int.cast_one]

theorem endpointDeficit_eq (a : ℝ) (Q q : ℕ) :
    endpointDeficit a Q q = 2 * (q : ℝ) - endpointSum a Q q := by
  rw [endpointSum_range]
  unfold endpointDeficit
  have ht : (∑ i ∈ Finset.range q,
      ((1 - boundary a ((Q : ℝ) + 1 + i)) +
        (1 + boundary a (-(Q : ℝ) + i)))) =
      ∑ i ∈ Finset.range q,
        (2 - (boundary a ((Q : ℝ) + 1 + i) -
          boundary a (-(Q : ℝ) + i))) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ht, Finset.sum_sub_distrib]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem boundary_deficit_uniform {a d u : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hdu : d ≤ u) :
    0 ≤ 1 - boundary a u ∧ 1 - boundary a u ≤ a ^ 2 / (2 * d ^ 2) := by
  have hu := lt_of_lt_of_le hd hdu
  have hb := boundary_deficit_bounds ha hu
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hsq : d ^ 2 ≤ u ^ 2 := by nlinarith [sq_nonneg (u - d)]
  exact div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) (by gcongr)

theorem endpointDeficit_bounds {a : ℝ} (ha : 0 < a) {Q q : ℕ} (hQ : q < Q) :
    0 ≤ endpointDeficit a Q q ∧
      endpointDeficit a Q q ≤ (q : ℝ) * a ^ 2 / ((Q : ℝ) - q) ^ 2 := by
  have hQreal : (q : ℝ) < Q := by exact_mod_cast hQ
  have hd : 0 < (Q : ℝ) - q := sub_pos.mpr hQreal
  have hc : ∀ i ∈ Finset.range q,
      0 ≤ (1 - boundary a ((Q : ℝ) + 1 + i)) +
          (1 + boundary a (-(Q : ℝ) + i)) ∧
        (1 - boundary a ((Q : ℝ) + 1 + i)) +
          (1 + boundary a (-(Q : ℝ) + i)) ≤
            a ^ 2 / ((Q : ℝ) - q) ^ 2 := by
    intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    have hiqR : (i : ℝ) < q := by exact_mod_cast hiq
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    have ht : (Q : ℝ) - q ≤ (Q : ℝ) + 1 + i := by linarith
    have hb : (Q : ℝ) - q ≤ (Q : ℝ) - i := by linarith
    have bt := boundary_deficit_uniform ha hd ht
    have bb := boundary_deficit_uniform ha hd hb
    have ho : boundary a (-(Q : ℝ) + i) = -boundary a ((Q : ℝ) - i) := by
      rw [show -(Q : ℝ) + i = -((Q : ℝ) - i) by ring, boundary_odd]
    rw [ho]
    constructor
    · linarith [bt.1, bb.1]
    · have hh : a ^ 2 / (2 * ((Q : ℝ) - q) ^ 2) +
          a ^ 2 / (2 * ((Q : ℝ) - q) ^ 2) =
            a ^ 2 / ((Q : ℝ) - q) ^ 2 := by
        field_simp [hd.ne'] <;> ring
      linarith [bt.2, bb.2]
  unfold endpointDeficit
  constructor
  · exact Finset.sum_nonneg (fun i hi => (hc i hi).1)
  · calc
      (∑ i ∈ Finset.range q,
          ((1 - boundary a ((Q : ℝ) + 1 + i)) +
            (1 + boundary a (-(Q : ℝ) + i)))) ≤
          ∑ i ∈ Finset.range q, a ^ 2 / ((Q : ℝ) - q) ^ 2 :=
        Finset.sum_le_sum (fun i hi => (hc i hi).2)
      _ = (q : ℝ) * a ^ 2 / ((Q : ℝ) - q) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem complete_mass_prefactor {y : ℝ} (hy : 0 < y) {q : ℕ} (hq : 0 < q) :
    2 / ((q : ℝ) ^ 2 * Real.sqrt y) =
      weight y / ((q : ℝ) * ((q : ℝ) * y) ^ 2) * (2 * (q : ℝ)) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let r := Real.sqrt y
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hr2 : r ^ 2 = y := Real.sq_sqrt hy.le
  change 2 / ((q : ℝ) ^ 2 * r) =
    y * r / ((q : ℝ) * ((q : ℝ) * y) ^ 2) * (2 * (q : ℝ))
  rw [← hr2]
  field_simp [hqR.ne', hr] <;> ring

theorem actual_error_eq_endpointDeficit {y : ℝ} (hy : 0 < y)
    {m : ℤ} (hm : m ≠ 0) (Q : ℕ) :
    infiniteShiftIntegral y m - finiteShiftIntegral y m Q =
      weight y / ((m.natAbs : ℝ) * ((m.natAbs : ℝ) * y) ^ 2) *
        endpointDeficit ((m.natAbs : ℝ) * y) Q m.natAbs := by
  rw [unfoldFullRealThreeHalves_natAbs hy hm, finiteShiftIntegral_formula hy hm,
    complete_mass_prefactor hy (Int.natAbs_pos.mpr hm), endpointDeficit_eq]
  ring

theorem actual_truncation_error_bounds {y : ℝ} (hy : 0 < y)
    {m : ℤ} (hm : m ≠ 0) {Q : ℕ} (hQ : m.natAbs < Q) :
    0 ≤ infiniteShiftIntegral y m - finiteShiftIntegral y m Q ∧
      infiniteShiftIntegral y m - finiteShiftIntegral y m Q ≤
        truncationEnvelope y Q m.natAbs := by
  have hq : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hqR : 0 < (m.natAbs : ℝ) := by exact_mod_cast hq
  have hQreal : (m.natAbs : ℝ) < Q := by exact_mod_cast hQ
  have hd : 0 < (Q : ℝ) - m.natAbs := sub_pos.mpr hQreal
  have ha : 0 < (m.natAbs : ℝ) * y := mul_pos hqR hy
  have hp : 0 ≤ weight y / ((m.natAbs : ℝ) * ((m.natAbs : ℝ) * y) ^ 2) :=
    (div_pos (weight_pos hy) (mul_pos hqR (sq_pos_of_pos ha))).le
  have hb := endpointDeficit_bounds ha hQ
  rw [actual_error_eq_endpointDeficit hy hm]
  refine ⟨mul_nonneg hp hb.1, ?_⟩
  calc
    weight y / ((m.natAbs : ℝ) * ((m.natAbs : ℝ) * y) ^ 2) *
        endpointDeficit ((m.natAbs : ℝ) * y) Q m.natAbs ≤
      weight y / ((m.natAbs : ℝ) * ((m.natAbs : ℝ) * y) ^ 2) *
        ((m.natAbs : ℝ) * ((m.natAbs : ℝ) * y) ^ 2 /
          ((Q : ℝ) - m.natAbs) ^ 2) := mul_le_mul_of_nonneg_left hb.2 hp
    _ = truncationEnvelope y Q m.natAbs := by
      unfold truncationEnvelope
      field_simp [hqR.ne', hy.ne', hd.ne'] <;> ring

theorem truncationEnvelope_eq_rpow {y : ℝ} (hy : 0 < y) (Q q : ℕ) :
    truncationEnvelope y Q q = y ^ (3 / 2 : ℝ) / ((Q : ℝ) - q) ^ 2 := by
  rw [truncationEnvelope, weight_eq_rpow hy]

theorem continuous_truncationEnvelope (Q q : ℕ) :
    Continuous (fun y : ℝ => truncationEnvelope y Q q) := by
  exact (continuous_id.mul continuous_id.sqrt).div_const _

end Epstein22

#print axioms Epstein22.endpointDeficit
#print axioms Epstein22.truncationEnvelope
#print axioms Epstein22.endpointSum_range
#print axioms Epstein22.endpointDeficit_eq
#print axioms Epstein22.boundary_deficit_uniform
#print axioms Epstein22.endpointDeficit_bounds
#print axioms Epstein22.complete_mass_prefactor
#print axioms Epstein22.actual_error_eq_endpointDeficit
#print axioms Epstein22.actual_truncation_error_bounds
#print axioms Epstein22.truncationEnvelope_eq_rpow
#print axioms Epstein22.continuous_truncationEnvelope
