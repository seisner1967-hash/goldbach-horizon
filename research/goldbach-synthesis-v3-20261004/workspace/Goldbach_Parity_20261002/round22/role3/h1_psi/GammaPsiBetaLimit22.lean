import GammaPsiCore22
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! SOURCE ONLY: the domination below is a concrete consequence of cpow,
the mean value theorem, and the positive-real Beta integrals. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def betaEndpointConstant (z : ℂ) : ℝ :=
  ‖z - 1‖ * (1 + (1 / 2 : ℝ) ^ (z.re - 2))

def betaDifferenceMajorant (z : ℂ) (t : ℝ) : ℝ :=
  2 * (t ^ (z.re - 1) + 1) + betaEndpointConstant z

def psiBetaIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  (1 - (t : ℂ) ^ (z - 1)) / (1 - (t : ℂ))

theorem betaEndpointConstant_nonneg (z : ℂ) : 0 ≤ betaEndpointConstant z := by
  unfold betaEndpointConstant
  positivity

theorem betaDifferenceMajorant_nonneg {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ betaDifferenceMajorant z t := by
  unfold betaDifferenceMajorant
  have hc := betaEndpointConstant_nonneg z
  have hr := Real.rpow_nonneg ht (z.re - 1)
  linarith

theorem rpow_le_half_endpoint_sum {t e : ℝ} (ht : t ∈ Icc (1 / 2) 1) :
    t ^ e ≤ 1 + (1 / 2 : ℝ) ^ e := by
  by_cases he : 0 ≤ e
  · have h := Real.rpow_le_one (by linarith [ht.1] : 0 ≤ t) ht.2 he
    have hh := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) e
    linarith
  · have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
      ht.1 (le_of_lt (lt_of_not_ge he))
    linarith

theorem norm_ofReal_cpow {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖(t : ℂ) ^ z‖ = t ^ z.re := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos ht]

theorem hasDerivAt_ofReal_cpow {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ (z - 1))
      ((z - 1) * (t : ℂ) ^ (z - 2)) t := by
  have h := (Complex.hasStrictDerivAt_cpow_const
    (c := z - 1) (Complex.ofReal_mem_slitPlane.mpr ht)).hasDerivAt.comp_ofReal
  simpa only [show z - 1 - 1 = z - 2 by ring] using h

theorem norm_cpow_sub_one_le_endpoint {z : ℂ} {t : ℝ}
    (ht : t ∈ Icc (1 / 2) 1) :
    ‖(t : ℂ) ^ (z - 1) - 1‖ ≤ betaEndpointConstant z * (1 - t) := by
  have hd (u : ℝ) (hu : u ∈ Icc (1 / 2 : ℝ) 1) :=
    hasDerivAt_ofReal_cpow (by linarith [hu.1] : 0 < u) z
  have hb (u : ℝ) (hu : u ∈ Icc (1 / 2 : ℝ) 1) :
      ‖deriv (fun v : ℝ => (v : ℂ) ^ (z - 1)) u‖ ≤ betaEndpointConstant z := by
    rw [(hd u hu).deriv, norm_mul,
      norm_ofReal_cpow (by linarith [hu.1] : 0 < u)]
    simp only [Complex.sub_re, Complex.ofNat_re]
    exact mul_le_mul_of_nonneg_left (rpow_le_half_endpoint_sum hu) (norm_nonneg _)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hb (convex_Icc (1 / 2 : ℝ) 1)
    (show (1 : ℝ) ∈ Icc (1 / 2) 1 by constructor <;> norm_num) ht
  simpa only [Complex.ofReal_one, Complex.one_cpow, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using h

theorem norm_betaFactor_le_two {w t : ℝ} (hw : 0 ≤ w)
    (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖(1 - (t : ℂ)) ^ ((w : ℂ) - 1)‖ ≤ 2 := by
  have hb : 0 < 1 - t := by linarith [ht.2]
  have hble : 1 - t ≤ 1 := by linarith [ht.1]
  have hbhalf : (1 / 2 : ℝ) ≤ 1 - t := by linarith [ht.2]
  rw [show 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) by
      simp only [Complex.ofReal_sub, Complex.ofReal_one],
    norm_ofReal_cpow hb]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  calc
    (1 - t) ^ (w - 1) ≤ (1 - t) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hb hble (by linarith)
    _ = 1 / (1 - t) := by simp only [Real.rpow_neg_one, one_div]
    _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hbhalf
    _ = 2 := by norm_num

theorem norm_betaDifference_le_left {z : ℂ} {w t : ℝ} (hw : 0 ≤ w)
    (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖betaDifferenceIntegrand z w t‖ ≤ betaDifferenceMajorant z t := by
  have hnum : ‖(t : ℂ) ^ (z - 1) - 1‖ ≤ t ^ (z.re - 1) + 1 := by
    simpa only [norm_ofReal_cpow ht.1, Complex.sub_re, Complex.one_re, norm_one]
      using norm_sub_le ((t : ℂ) ^ (z - 1)) (1 : ℂ)
  have hfac := norm_betaFactor_le_two hw ht
  unfold betaDifferenceIntegrand
  rw [norm_mul]
  calc
    _ ≤ (t ^ (z.re - 1) + 1) * 2 :=
      mul_le_mul hnum hfac (norm_nonneg _) (by positivity)
    _ ≤ betaDifferenceMajorant z t := by
      unfold betaDifferenceMajorant
      have hc := betaEndpointConstant_nonneg z
      linarith

theorem norm_betaDifference_le_right {z : ℂ} {w t : ℝ} (hw : 0 ≤ w)
    (ht : t ∈ Ico (1 / 2 : ℝ) 1) :
    ‖betaDifferenceIntegrand z w t‖ ≤ betaDifferenceMajorant z t := by
  have hb : 0 < 1 - t := by linarith [ht.2]
  have hble : 1 - t ≤ 1 := by linarith [ht.1]
  have hnum := norm_cpow_sub_one_le_endpoint ⟨ht.1, ht.2.le⟩ (z := z)
  have hfac : ‖(1 - (t : ℂ)) ^ ((w : ℂ) - 1)‖ = (1 - t) ^ (w - 1) := by
    rw [show 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) by
        simp only [Complex.ofReal_sub, Complex.ofReal_one],
      norm_ofReal_cpow hb]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  have hcancel : (1 - t) * (1 - t) ^ (w - 1) = (1 - t) ^ w := by
    rw [Real.rpow_sub_one hb.ne']
    field_simp [hb.ne']
  unfold betaDifferenceIntegrand
  rw [norm_mul, hfac]
  calc
    _ ≤ (betaEndpointConstant z * (1 - t)) * (1 - t) ^ (w - 1) :=
      mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hb.le _)
    _ = betaEndpointConstant z * (1 - t) ^ w := by rw [mul_assoc, hcancel]
    _ ≤ betaEndpointConstant z := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.rpow_le_one hb.le hble hw) (betaEndpointConstant_nonneg z)
    _ ≤ betaDifferenceMajorant z t := by
      unfold betaDifferenceMajorant
      have hr := Real.rpow_nonneg (by linarith [ht.1] : 0 ≤ t) (z.re - 1)
      linarith

theorem norm_betaDifference_le_majorant {z : ℂ} {w t : ℝ} (hw : 0 ≤ w)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖betaDifferenceIntegrand z w t‖ ≤ betaDifferenceMajorant z t := by
  by_cases ht1 : t = 1
  · subst t
    simp only [betaDifferenceIntegrand, Complex.ofReal_one, Complex.one_cpow,
      sub_self, zero_mul, norm_zero]
    exact betaDifferenceMajorant_nonneg zero_le_one
  · by_cases hhalf : t ≤ 1 / 2
    · exact norm_betaDifference_le_left hw ⟨ht.1, hhalf⟩
    · exact norm_betaDifference_le_right hw
        ⟨(lt_of_not_ge hhalf).le, lt_of_le_of_ne ht.2 ht1⟩

theorem intervalIntegrable_betaDifferenceMajorant {z : ℂ} (hz : 0 < z.re) :
    IntervalIntegrable (betaDifferenceMajorant z) volume 0 1 := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (z.re - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hc : IntervalIntegrable (fun _ : ℝ => betaEndpointConstant z) volume 0 1 :=
    intervalIntegrable_const
  exact ((hr.add h1).const_mul 2).add hc

theorem intervalIntegrable_betaDifference {z : ℂ} (hz : 0 < z.re)
    {w : ℝ} (hw : 0 < w) :
    IntervalIntegrable (betaDifferenceIntegrand z w) volume 0 1 := by
  have hi := Complex.betaIntegral_convergent hz (show 0 < (w : ℂ).re from hw)
  have h1 := Complex.betaIntegral_convergent
    (show 0 < (1 : ℂ).re by norm_num) (show 0 < (w : ℂ).re from hw)
  simpa only [betaDifferenceIntegrand, sub_self, Complex.cpow_zero, one_mul, sub_mul]
    using hi.sub h1

theorem betaDifference_pointwise_tendsto {z : ℂ} {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => betaDifferenceIntegrand z (betaStep n) t) atTop
      (𝓝 (betaDifferenceIntegrand z 0 t)) := by
  by_cases ht1 : t = 1
  · subst t
    simpa only [betaDifferenceIntegrand, Complex.ofReal_one, Complex.one_cpow,
      sub_self, zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ))
        atTop (𝓝 0))
  · have hb : (1 - (t : ℂ)) ≠ 0 := by
      have hreal : 1 - t ≠ 0 := by
        intro h
        apply ht1
        linarith
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
        Complex.ofReal_ne_zero.mpr hreal
    have hexp : ContinuousAt (fun w : ℝ => (1 - (t : ℂ)) ^ ((w : ℂ) - 1)) 0 :=
      (Complex.continuous_ofReal.continuousAt.sub continuousAt_const).const_cpow
        (Or.inl hb)
    exact (tendsto_const_nhds.mul (hexp.tendsto.comp betaStep_tendsto_zero))

theorem betaDifference_limit_aestronglyMeasurable {z : ℂ} (hz : 0 < z.re) :
    AEStronglyMeasurable (betaDifferenceIntegrand z 0) (volume.restrict (Ioc 0 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (intervalIntegrable_betaDifference hz (betaStep_pos n)).1.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact betaDifference_pointwise_tendsto ht

theorem integrableOn_betaDifference_limit {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (betaDifferenceIntegrand z 0) (Ioc 0 1) := by
  apply (intervalIntegrable_betaDifferenceMajorant hz).1.mono'
    (betaDifference_limit_aestronglyMeasurable hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact norm_betaDifference_le_majorant le_rfl ht

theorem betaDifference_dominated_limit {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => ∫ t : ℝ in 0..1, betaDifferenceIntegrand z (betaStep n) t)
      atTop (𝓝 (∫ t : ℝ in 0..1, betaDifferenceIntegrand z 0 t)) := by
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply tendsto_integral_of_dominated_convergence (betaDifferenceMajorant z)
    (fun n => (intervalIntegrable_betaDifference hz (betaStep_pos n)).1.aestronglyMeasurable)
    (intervalIntegrable_betaDifferenceMajorant hz).1
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact norm_betaDifference_le_majorant (betaStep_pos n).le ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact betaDifference_pointwise_tendsto ht

theorem betaDifference_zero_integral {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in 0..1, betaDifferenceIntegrand z 0 t) =
      -(Real.eulerMascheroniConstant : ℂ) - gammaPsi z := by
  have h := betaDifference_tendsto hz
  have h' : Tendsto (fun n : ℕ => ∫ t : ℝ in 0..1,
      betaDifferenceIntegrand z (betaStep n) t) atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - gammaPsi z)) := by
    have heq : (fun n : ℕ => Complex.betaIntegral z (betaStep n) -
        Complex.betaIntegral 1 (betaStep n)) =
        (fun n : ℕ => ∫ t : ℝ in 0..1, betaDifferenceIntegrand z (betaStep n) t) := by
      funext n
      exact betaDifference_eq_integral hz (betaStep_pos n)
    rwa [heq] at h
  exact tendsto_nhds_unique (betaDifference_dominated_limit hz) h'

theorem betaDifference_zero_eq_neg_psiBeta (z : ℂ) (t : ℝ) :
    betaDifferenceIntegrand z 0 t = -psiBetaIntegrand z t := by
  simp only [betaDifferenceIntegrand, Complex.ofReal_zero, zero_sub,
    Complex.cpow_neg_one, psiBetaIntegrand, div_eq_mul_inv, neg_mul, sub_mul]
  ring

theorem integrableOn_psiBetaIntegrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (psiBetaIntegrand z) (Ioc 0 1) := by
  simpa only [betaDifference_zero_eq_neg_psiBeta, neg_neg] using
    (integrableOn_betaDifference_limit hz).neg

theorem gammaPsi_eq_beta_integral {z : ℂ} (hz : 0 < z.re) :
    gammaPsi z = -(Real.eulerMascheroniConstant : ℂ) +
      ∫ t : ℝ in 0..1, psiBetaIntegrand z t := by
  have h := betaDifference_zero_integral hz
  simp only [betaDifference_zero_eq_neg_psiBeta, intervalIntegral.integral_neg] at h
  linear_combination h

end GoldbachContinuous22

#print axioms GoldbachContinuous22.betaEndpointConstant
#print axioms GoldbachContinuous22.betaDifferenceMajorant
#print axioms GoldbachContinuous22.psiBetaIntegrand
#print axioms GoldbachContinuous22.betaEndpointConstant_nonneg
#print axioms GoldbachContinuous22.betaDifferenceMajorant_nonneg
#print axioms GoldbachContinuous22.rpow_le_half_endpoint_sum
#print axioms GoldbachContinuous22.norm_ofReal_cpow
#print axioms GoldbachContinuous22.hasDerivAt_ofReal_cpow
#print axioms GoldbachContinuous22.norm_cpow_sub_one_le_endpoint
#print axioms GoldbachContinuous22.norm_betaFactor_le_two
#print axioms GoldbachContinuous22.norm_betaDifference_le_left
#print axioms GoldbachContinuous22.norm_betaDifference_le_right
#print axioms GoldbachContinuous22.norm_betaDifference_le_majorant
#print axioms GoldbachContinuous22.intervalIntegrable_betaDifferenceMajorant
#print axioms GoldbachContinuous22.intervalIntegrable_betaDifference
#print axioms GoldbachContinuous22.betaDifference_pointwise_tendsto
#print axioms GoldbachContinuous22.betaDifference_limit_aestronglyMeasurable
#print axioms GoldbachContinuous22.integrableOn_betaDifference_limit
#print axioms GoldbachContinuous22.betaDifference_dominated_limit
#print axioms GoldbachContinuous22.betaDifference_zero_integral
#print axioms GoldbachContinuous22.betaDifference_zero_eq_neg_psiBeta
#print axioms GoldbachContinuous22.integrableOn_psiBetaIntegrand
#print axioms GoldbachContinuous22.gammaPsi_eq_beta_integral
