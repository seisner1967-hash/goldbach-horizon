import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-! A real geometric kernel. All integrability conclusions are derived here.
This file does not assert a scattering identity or a Goldbach estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Epstein22

def radicand (a u : ℝ) : ℝ := u ^ 2 + a ^ 2
def kernel (a u : ℝ) : ℝ := 1 / (radicand a u * Real.sqrt (radicand a u))
def boundary (a u : ℝ) : ℝ := u / Real.sqrt (radicand a u)
def primitive (a u : ℝ) : ℝ := boundary a u / a ^ 2
def weight (y : ℝ) : ℝ := y * Real.sqrt y

theorem radicand_pos {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 < radicand a u := by
  unfold radicand
  exact add_pos_of_nonneg_of_pos (sq_nonneg u) (sq_pos_of_pos ha)

theorem root_pos {a : ℝ} (ha : 0 < a) (u : ℝ) :
    0 < Real.sqrt (radicand a u) := Real.sqrt_pos.mpr (radicand_pos ha u)

theorem root_sq {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.sqrt (radicand a u) ^ 2 = radicand a u :=
  Real.sq_sqrt (radicand_pos ha u).le

theorem kernel_pos {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 < kernel a u := by
  unfold kernel
  exact one_div_pos.mpr (mul_pos (radicand_pos ha u) (root_pos ha u))

theorem kernel_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ kernel a u :=
  (kernel_pos ha u).le

theorem kernel_even (a u : ℝ) : kernel a (-u) = kernel a u := by
  simp [kernel, radicand]

theorem boundary_odd (a u : ℝ) : boundary a (-u) = -boundary a u := by
  simp [boundary, radicand, neg_div]

theorem primitive_odd (a u : ℝ) : primitive a (-u) = -primitive a u := by
  simp [primitive, boundary_odd, neg_div]

theorem weight_pos {y : ℝ} (hy : 0 < y) : 0 < weight y :=
  mul_pos hy (Real.sqrt_pos.mpr hy)

theorem weight_eq_rpow {y : ℝ} (hy : 0 < y) : weight y = y ^ (3 / 2 : ℝ) := by
  calc
    weight y = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by
      simp [weight, Real.sqrt_eq_rpow]
    _ = y ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hy _ _).symm
    _ = y ^ (3 / 2 : ℝ) := by congr 1; norm_num

theorem kernel_eq_rpow {a : ℝ} (ha : 0 < a) (u : ℝ) :
    kernel a u = (radicand a u) ^ (-3 / 2 : ℝ) := by
  have hp := radicand_pos ha u
  have hpow : (radicand a u) ^ (3 / 2 : ℝ) =
      radicand a u * Real.sqrt (radicand a u) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [kernel, ← hpow, show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
    Real.rpow_neg hp.le]
  simp only [one_div]

theorem continuous_kernel {a : ℝ} (ha : 0 < a) : Continuous (kernel a) := by
  unfold kernel radicand
  exact continuous_const.div
    (((continuous_id.pow 2).add continuous_const).mul
      ((continuous_id.pow 2).add continuous_const).sqrt)
    (fun u => (mul_pos (radicand_pos ha u) (root_pos ha u)).ne')

theorem continuous_boundary {a : ℝ} (ha : 0 < a) : Continuous (boundary a) := by
  unfold boundary radicand
  exact continuous_id.div (((continuous_id.pow 2).add continuous_const).sqrt)
    (fun u => (root_pos ha u).ne')

theorem continuous_primitive {a : ℝ} (ha : 0 < a) : Continuous (primitive a) := by
  exact (continuous_boundary ha).div_const _

theorem hasDerivAt_root {a : ℝ} (ha : 0 < a) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.sqrt (radicand a v))
      (u / Real.sqrt (radicand a u)) u := by
  have hp := radicand_pos ha u
  convert (((hasDerivAt_id u).pow 2).add_const (a ^ 2)).sqrt hp.ne' using 1
  simp only [id_eq, pow_one, Nat.cast_ofNat, radicand]
  field_simp [(root_pos ha u).ne'] <;> ring

theorem hasDerivAt_boundary {a : ℝ} (ha : 0 < a) (u : ℝ) :
    HasDerivAt (boundary a) (a ^ 2 * kernel a u) u := by
  have hs := root_pos ha u
  have hp := radicand_pos ha u
  have hsq := root_sq ha u
  convert (hasDerivAt_id u).div (hasDerivAt_root ha u) hs.ne' using 1
  let r := Real.sqrt (radicand a u)
  have hr : r ≠ 0 := hs.ne'
  have hr2 : r ^ 2 = u ^ 2 + a ^ 2 := hsq
  change a ^ 2 * (1 / ((u ^ 2 + a ^ 2) * r)) =
    (1 * r - u * (u / r)) / r ^ 2
  rw [← hr2]
  have hnum : r ^ 2 * a ^ 2 = r ^ 2 * (r ^ 2 - u ^ 2) := by
    congr 1
    nlinarith [hr2]
  field_simp [hr]
  nlinarith [hnum]

theorem hasDerivAt_primitive {a : ℝ} (ha : 0 < a) (u : ℝ) :
    HasDerivAt (primitive a) (kernel a u) u := by
  convert (hasDerivAt_boundary ha u).div_const (a ^ 2) using 1
  field_simp [ha.ne'] <;> ring

theorem intervalIntegrable_kernel {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    IntervalIntegrable (kernel a) volume A B := (continuous_kernel ha).intervalIntegrable _ _

theorem integral_kernel_interval {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    (∫ u in A..B, kernel a u) = primitive a B - primitive a A := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_primitive ha u) (intervalIntegrable_kernel ha A B)

theorem boundary_normalized {a u : ℝ} (hu : 0 < u) :
    boundary a u = (Real.sqrt (1 + (a / u) ^ 2))⁻¹ := by
  have hs : Real.sqrt (radicand a u) = u * Real.sqrt (1 + (a / u) ^ 2) := by
    calc
      Real.sqrt (radicand a u) = Real.sqrt (u ^ 2 * (1 + (a / u) ^ 2)) := by
        congr 1
        unfold radicand
        field_simp [hu.ne'] <;> ring
      _ = Real.sqrt (u ^ 2) * Real.sqrt (1 + (a / u) ^ 2) :=
        Real.sqrt_mul (sq_nonneg u) _
      _ = u * Real.sqrt (1 + (a / u) ^ 2) := by rw [Real.sqrt_sq hu.le]
  unfold boundary
  rw [hs]
  field_simp [hu.ne']

theorem tendsto_boundary_atTop (a : ℝ) :
    Tendsto (boundary a) atTop (𝓝 1) := by
  have h0 : Tendsto (fun u : ℝ => a / u) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).const_mul a
  have h1 : Tendsto (fun u : ℝ => 1 + (a / u) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (h0.pow 2)
  have h2 : Tendsto (fun u : ℝ => (Real.sqrt (1 + (a / u) ^ 2))⁻¹)
      atTop (𝓝 1) := by
    simpa using h1.sqrt.inv₀ (by norm_num : Real.sqrt (1 : ℝ) ≠ 0)
  apply h2.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (boundary_normalized hu).symm

theorem tendsto_primitive_atTop (a : ℝ) :
    Tendsto (primitive a) atTop (𝓝 (1 / a ^ 2)) :=
  (tendsto_boundary_atTop a).div_const _

theorem tendsto_primitive_atBot (a : ℝ) :
    Tendsto (primitive a) atBot (𝓝 (-1 / a ^ 2)) := by
  have h := ((tendsto_primitive_atTop a).comp tendsto_neg_atBot_atTop).neg
  simpa [Function.comp_def, primitive_odd, neg_div, one_div] using h

theorem integrable_kernel {a : ℝ} (ha : 0 < a) : Integrable (kernel a) := by
  have hr : IntegrableOn (kernel a) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg'
      (fun u _ => hasDerivAt_primitive ha u)
      (fun u _ => kernel_nonneg ha u) (tendsto_primitive_atTop a)
  have hn := (MeasurePreserving.integrableOn_comp_preimage
    (Measure.measurePreserving_neg (volume : Measure ℝ))
    (Homeomorph.neg ℝ).measurableEmbedding).2 hr
  have hl0 : IntegrableOn (kernel a) (Iio (0 : ℝ)) := by
    simpa [Function.comp_def, neg_preimage, kernel_even] using hn
  have hl : IntegrableOn (kernel a) (Iic (0 : ℝ)) :=
    integrableOn_Iic_iff_integrableOn_Iio.mpr hl0
  apply integrableOn_univ.mp
  simpa using hl.union hr

theorem integral_kernel {a : ℝ} (ha : 0 < a) :
    (∫ u : ℝ, kernel a u) = 2 / a ^ 2 := by
  rw [integral_of_hasDerivAt_of_tendsto
    (fun u => hasDerivAt_primitive ha u) (integrable_kernel ha)
    (tendsto_primitive_atBot a) (tendsto_primitive_atTop a)]
  ring

theorem boundary_le_one {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    boundary a u ≤ 1 := by
  unfold boundary
  apply (div_le_one (root_pos ha u)).mpr
  exact Real.le_sqrt_of_sq_le (by simp [radicand, sq_nonneg a])

theorem boundary_deficit {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    1 - boundary a u = a ^ 2 /
      (Real.sqrt (radicand a u) * (Real.sqrt (radicand a u) + u)) := by
  have hs := root_pos ha u
  let r := Real.sqrt (radicand a u)
  have hr : r ≠ 0 := hs.ne'
  have ht : r + u ≠ 0 := (add_pos hs hu).ne'
  have hsq : r ^ 2 = u ^ 2 + a ^ 2 := root_sq ha u
  have hfactor : (r - u) * (r + u) = a ^ 2 := by nlinarith [hsq]
  change 1 - u / r = a ^ 2 / (r * (r + u))
  rw [← hfactor]
  field_simp [hr, ht] <;> ring

theorem boundary_deficit_bounds {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    0 ≤ 1 - boundary a u ∧ 1 - boundary a u ≤ a ^ 2 / (2 * u ^ 2) := by
  refine ⟨sub_nonneg.mpr (boundary_le_one ha hu.le), ?_⟩
  rw [boundary_deficit ha hu]
  have hs := root_pos ha u
  have hsu : u ≤ Real.sqrt (radicand a u) :=
    Real.le_sqrt_of_sq_le (by simp [radicand, sq_nonneg a])
  have hd : 2 * u ^ 2 ≤ Real.sqrt (radicand a u) * (Real.sqrt (radicand a u) + u) := by
    calc
      2 * u ^ 2 = u * (u + u) := by ring
      _ ≤ Real.sqrt (radicand a u) * (Real.sqrt (radicand a u) + u) := by gcongr
  exact div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) hd

end Epstein22

#print axioms Epstein22.radicand
#print axioms Epstein22.kernel
#print axioms Epstein22.boundary
#print axioms Epstein22.primitive
#print axioms Epstein22.weight
#print axioms Epstein22.radicand_pos
#print axioms Epstein22.root_pos
#print axioms Epstein22.root_sq
#print axioms Epstein22.kernel_pos
#print axioms Epstein22.kernel_nonneg
#print axioms Epstein22.kernel_even
#print axioms Epstein22.boundary_odd
#print axioms Epstein22.primitive_odd
#print axioms Epstein22.weight_pos
#print axioms Epstein22.weight_eq_rpow
#print axioms Epstein22.kernel_eq_rpow
#print axioms Epstein22.continuous_kernel
#print axioms Epstein22.continuous_boundary
#print axioms Epstein22.continuous_primitive
#print axioms Epstein22.hasDerivAt_root
#print axioms Epstein22.hasDerivAt_boundary
#print axioms Epstein22.hasDerivAt_primitive
#print axioms Epstein22.intervalIntegrable_kernel
#print axioms Epstein22.integral_kernel_interval
#print axioms Epstein22.boundary_normalized
#print axioms Epstein22.tendsto_boundary_atTop
#print axioms Epstein22.tendsto_primitive_atTop
#print axioms Epstein22.tendsto_primitive_atBot
#print axioms Epstein22.integrable_kernel
#print axioms Epstein22.integral_kernel
#print axioms Epstein22.boundary_le_one
#print axioms Epstein22.boundary_deficit
#print axioms Epstein22.boundary_deficit_bounds
