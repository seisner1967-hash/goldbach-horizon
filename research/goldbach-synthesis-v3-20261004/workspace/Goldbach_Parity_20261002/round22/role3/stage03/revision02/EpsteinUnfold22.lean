import EpsteinFinite22
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set Filter MeasureTheory Function
open scoped BigOperators Topology

namespace Epstein22

def periodized (a v : ℝ) : ℝ := ∑' n : ℤ, kernel a (v + n)

def translateBound (a : ℝ) (R : ℕ) (n : ℤ) : ℝ :=
  (if n ∈ Finset.Icc (-(2 * R : ℤ)) (2 * R : ℤ) then 1 / a ^ 3 else 0) +
    8 * |(n : ℝ)| ^ (-3 : ℝ)

def infiniteShiftIntegral (y : ℝ) (m : ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∑' n : ℤ, shiftKernel y m n x

theorem kernel_upper_of_sq_le {a d u : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hsq : d ^ 2 ≤ radicand a u) : kernel a u ≤ 1 / d ^ 3 := by
  have hroot : d ≤ Real.sqrt (radicand a u) := Real.le_sqrt_of_sq_le hsq
  have hden : d ^ 3 ≤ radicand a u * Real.sqrt (radicand a u) := by
    calc
      d ^ 3 = d ^ 2 * d := by ring
      _ ≤ radicand a u * Real.sqrt (radicand a u) :=
        mul_le_mul hsq hroot hd.le (radicand_pos ha u).le
  unfold kernel
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hd 3) hden

theorem kernel_upper_a {a : ℝ} (ha : 0 < a) (u : ℝ) :
    kernel a u ≤ 1 / a ^ 3 := by
  apply kernel_upper_of_sq_le ha ha
  unfold radicand
  nlinarith [sq_nonneg u]

theorem summable_translateBound (a : ℝ) (R : ℕ) : Summable (translateBound a R) := by
  have hf : Summable (fun n : ℤ =>
      if n ∈ Finset.Icc (-(2 * R : ℤ)) (2 * R : ℤ) then 1 / a ^ 3 else 0) := by
    apply summable_of_ne_finset_zero
    intro n hn
    exact if_neg hn
  exact hf.add ((Real.summable_abs_int_rpow (b := 3) (by norm_num)).mul_left 8)

theorem translateBound_nonneg {a : ℝ} (ha : 0 < a) (R : ℕ) (n : ℤ) :
    0 ≤ translateBound a R n := by
  unfold translateBound
  split_ifs <;> positivity

theorem kernel_translate_bound {a : ℝ} (ha : 0 < a) (R : ℕ) (n : ℤ) (v : ℝ)
    (hv : |v| ≤ (R : ℝ)) : ‖kernel a (v + n)‖ ≤ translateBound a R n := by
  rw [Real.norm_of_nonneg (kernel_nonneg ha _)]
  classical
  by_cases hn : n ∈ Finset.Icc (-(2 * R : ℤ)) (2 * R : ℤ)
  · have h0 : 0 ≤ 8 * |(n : ℝ)| ^ (-3 : ℝ) := by positivity
    simp only [translateBound, if_pos hn]
    exact (kernel_upper_a ha _).trans (le_add_of_nonneg_right h0)
  · have hlarge : (2 * R : ℝ) < |(n : ℝ)| := by
      by_contra h
      have hle : |(n : ℝ)| ≤ (2 * R : ℝ) := le_of_not_gt h
      have hlo : -(2 * R : ℝ) ≤ (n : ℝ) := (abs_le.mp hle).1
      have hhi : (n : ℝ) ≤ (2 * R : ℝ) := (abs_le.mp hle).2
      have hi : -(2 * R : ℤ) ≤ n ∧ n ≤ (2 * R : ℤ) := by
        constructor
        · exact_mod_cast hlo
        · exact_mod_cast hhi
      exact hn (Finset.mem_Icc.mpr hi)
    have hnpos : 0 < |(n : ℝ)| := lt_of_le_of_lt (by positivity) hlarge
    have htri : |(n : ℝ)| ≤ |v + n| + |v| := by
      simpa [add_assoc, add_comm, add_left_comm] using abs_add (v + (n : ℝ)) (-v)
    have hvn : |(n : ℝ)| / 2 ≤ |v + n| := by linarith
    have hd : 0 < |(n : ℝ)| / 2 := by positivity
    have hsq : (|(n : ℝ)| / 2) ^ 2 ≤ radicand a (v + n) := by
      have hc : (|(n : ℝ)| / 2) ^ 2 ≤ |v + n| ^ 2 := by gcongr
      unfold radicand
      simpa only [sq_abs] using hc.trans (le_add_of_nonneg_right (sq_nonneg a))
    have hk := kernel_upper_of_sq_le ha hd hsq
    simp only [translateBound, if_neg hn, zero_add]
    convert hk using 1
    rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hnpos.le]
    field_simp [hnpos.ne'] <;> ring

theorem continuousOn_periodized {a : ℝ} (ha : 0 < a) (R : ℕ) :
    ContinuousOn (periodized a) (Icc (-(R : ℝ)) R) := by
  unfold periodized
  apply continuousOn_tsum
    (fun n : ℤ => ((continuous_kernel ha).comp
      (continuous_id.add continuous_const)).continuousOn)
    (summable_translateBound a R)
  intro n v hv
  exact kernel_translate_bound ha R n v (abs_le.mpr hv)

theorem continuous_periodized {a : ℝ} (ha : 0 < a) : Continuous (periodized a) := by
  rw [continuous_iff_continuousAt]
  intro v
  obtain ⟨R, hR⟩ := exists_nat_gt |v|
  have hv : v ∈ Ioo (-(R : ℝ)) R := abs_lt.mp hR
  exact (continuousOn_periodized ha R).continuousAt (Icc_mem_nhds hv.1 hv.2)

theorem periodic_periodized (a : ℝ) : Function.Periodic (periodized a) 1 := by
  intro v
  unfold periodized
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => kernel a (v + n))
  simpa [Int.cast_add, add_assoc, add_comm, add_left_comm] using h

theorem intervalIntegrable_periodized {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    IntervalIntegrable (periodized a) volume A B :=
  (continuous_periodized ha).intervalIntegrable _ _

theorem summable_integral_norm_cells {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => ∫ x in Ioc (0 : ℝ) 1, ‖kernel a (x + n)‖) := by
  have h := (integrable_kernel ha).hasSum_intervalIntegral_comp_add_int.summable
  apply h.congr
  intro n
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  exact (Real.norm_of_nonneg (kernel_nonneg ha (x + n))).symm

theorem integral_periodized_unit {a : ℝ} (ha : 0 < a) :
    (∫ x in (0 : ℝ)..1, periodized a x) = 2 / a ^ 2 := by
  have hf : ∀ n : ℤ, IntegrableOn (fun x : ℝ => kernel a (x + n)) (Ioc 0 1) := by
    intro n
    exact (((continuous_kernel ha).comp
      (continuous_id.add continuous_const)).intervalIntegrable 0 1).1
  have ht := integral_tsum_of_summable_integral_norm hf (summable_integral_norm_cells ha)
  have hc := (integrable_kernel ha).hasSum_intervalIntegral_comp_add_int.tsum_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  unfold periodized
  rw [← ht]
  convert hc.trans (integral_kernel ha) using 1
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

theorem summable_kernel_translate {a : ℝ} (ha : 0 < a) (v : ℝ) :
    Summable (fun n : ℤ => kernel a (v + n)) := by
  obtain ⟨R, hR⟩ := exists_nat_gt |v|
  exact (summable_translateBound a R).of_norm_bounded _
    (fun n => kernel_translate_bound ha R n v hR.le)

theorem infiniteSum_shiftKernel {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0)
    (x : ℝ) :
    (∑' n : ℤ, shiftKernel y m n x) =
      weight y * periodized (|(m : ℝ)| * y) ((m : ℝ) * x) := by
  unfold shiftKernel periodized
  rw [tsum_mul_left]

theorem unfoldFullRealThreeHalves {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0) :
    infiniteShiftIntegral y m = 2 / (|(m : ℝ)| ^ 2 * Real.sqrt y) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have ha := mul_pos (abs_cast_pos hm) hy
  have hs := (Real.sqrt_pos.mpr hy).ne'
  have hr := Real.sq_sqrt hy.le
  unfold infiniteShiftIntegral
  simp_rw [infiniteSum_shiftKernel hy hm]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (periodized (|(m : ℝ)| * y)) hmR]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have hp := (periodic_periodized (|(m : ℝ)| * y)).intervalIntegral_add_zsmul_eq
    m 0 (intervalIntegrable_periodized ha)
  simp only [zero_add, zsmul_eq_mul, mul_one] at hp
  rw [hp, integral_periodized_unit ha]
  unfold weight
  let r := Real.sqrt y
  have hr0 : r ≠ 0 := hs
  have hr2 : r ^ 2 = y := hr
  change y * r * ((m : ℝ)⁻¹ * ((m : ℝ) *
    (2 / (|(m : ℝ)| * y) ^ 2))) = 2 / (|(m : ℝ)| ^ 2 * r)
  rw [← hr2]
  field_simp [hmR, (abs_cast_pos hm).ne', hr0] <;> simp only [sq_abs] <;> ring

theorem abs_cast_eq_natAbs (m : ℤ) : |(m : ℝ)| = (m.natAbs : ℝ) := by
  cases m with
  | ofNat n =>
    change |(n : ℝ)| = (n : ℝ)
    exact abs_of_nonneg (by positivity)
  | negSucc n =>
    rw [Int.cast_negSucc, Int.natAbs_negSucc, abs_neg]
    exact abs_of_nonneg (by positivity)

theorem unfoldFullRealThreeHalves_natAbs {y : ℝ} (hy : 0 < y) {m : ℤ} (hm : m ≠ 0) :
    infiniteShiftIntegral y m = 2 / ((m.natAbs : ℝ) ^ 2 * Real.sqrt y) := by
  rw [unfoldFullRealThreeHalves hy hm, abs_cast_eq_natAbs]

end Epstein22

#print axioms Epstein22.periodized
#print axioms Epstein22.translateBound
#print axioms Epstein22.infiniteShiftIntegral
#print axioms Epstein22.kernel_upper_of_sq_le
#print axioms Epstein22.kernel_upper_a
#print axioms Epstein22.summable_translateBound
#print axioms Epstein22.translateBound_nonneg
#print axioms Epstein22.kernel_translate_bound
#print axioms Epstein22.continuousOn_periodized
#print axioms Epstein22.continuous_periodized
#print axioms Epstein22.periodic_periodized
#print axioms Epstein22.intervalIntegrable_periodized
#print axioms Epstein22.summable_integral_norm_cells
#print axioms Epstein22.integral_periodized_unit
#print axioms Epstein22.summable_kernel_translate
#print axioms Epstein22.infiniteSum_shiftKernel
#print axioms Epstein22.unfoldFullRealThreeHalves
#print axioms Epstein22.abs_cast_eq_natAbs
#print axioms Epstein22.unfoldFullRealThreeHalves_natAbs
