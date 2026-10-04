import ThermalC5Mellin22
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! SOURCE ONLY. This is the actual Arch kernel of C2, not a function defined
by C5. Its integrability is inherited from the paid paired Mellin kernel plus
two explicitly evaluated integrable corrections. The Jacobian exp(v), the
log(2) term and the unit -1 are all derived below. No final equality or free
Integrable premise occurs in the concrete C5 theorem. Dependencies are SOURCE
unless their individual, exact source has already received an actual verdict. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def c5ThermalReal (Y x : ℝ) : ℝ := (x / Y) * Real.exp (-x / Y)

def c5Logistic (v : ℝ) : ℝ := Real.exp (-v) / (1 + Real.exp (-v))

def c5ArchKernel (Y x : ℝ) : ℂ :=
  (thermalTest Y x + thermalTest Y x⁻¹ / (x : ℂ) -
    2 * thermalTest Y 1 / (x : ℂ)) / ((x : ℂ) - (x : ℂ)⁻¹)

def c5ArchRealKernel (Y x : ℝ) : ℝ :=
  (c5ThermalReal Y x + c5ThermalReal Y (1 / x) / x -
    2 * c5ThermalReal Y 1 / x) / (x - 1 / x)

def c5ArchLogKernel (Y v : ℝ) : ℂ :=
  (thermalTest Y (Real.exp v) + (Real.exp (-v) : ℂ) * thermalTest Y (Real.exp (-v)) -
    2 * (Real.exp (-v) : ℂ) * thermalTest Y 1) /
    ((1 - Real.exp (-2 * v) : ℝ) : ℂ)

theorem c5ThermalReal_nonneg {Y x : ℝ} (hY : 0 < Y) (hx : 0 ≤ x) :
    0 ≤ c5ThermalReal Y x := by
  unfold c5ThermalReal
  positivity

theorem thermalTest_eq_c5ThermalReal (Y x : ℝ) :
    thermalTest Y x = (c5ThermalReal Y x : ℂ) := by
  rw [thermalTest_eq_real]
  unfold c5ThermalReal
  rw [neg_div]

theorem c5ThermalMinusPrimitive_deriv (Y v : ℝ) :
    HasDerivAt (fun w : ℝ => Real.exp (-Real.exp (-w) / Y))
      (c5ThermalReal Y (Real.exp (-v))) v := by
  have h := ((((hasDerivAt_id v).neg.exp).neg).div_const Y).exp
  simp only [mul_one, one_mul] at h
  convert h using 1
  unfold c5ThermalReal
  ring

theorem c5ThermalMinusPrimitive_limit (Y : ℝ) :
    Tendsto (fun v : ℝ => Real.exp (-Real.exp (-v) / Y)) atTop (𝓝 1) := by
  have harg : Tendsto (fun v : ℝ => -Real.exp (-v) / Y) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero, zero_div] using Real.tendsto_exp_neg_atTop_nhds_zero.neg.div_const Y
  exact Real.tendsto_exp_nhds_zero_nhds_one.comp harg

theorem c5ThermalPlusPrimitive_deriv (Y v : ℝ) :
    HasDerivAt (fun w : ℝ => -Real.exp (-Real.exp w / Y))
      (c5ThermalReal Y (Real.exp v)) v := by
  have h := ((((hasDerivAt_id v).exp.neg).div_const Y).exp).neg
  simp only [mul_one, one_mul] at h
  convert h using 1
  unfold c5ThermalReal
  ring

theorem c5ThermalPlusPrimitive_limit {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun v : ℝ => -Real.exp (-Real.exp v / Y)) atTop (𝓝 0) := by
  have harg : Tendsto (fun v : ℝ => Real.exp v / Y) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_div_const hY
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).neg
  simpa only [Function.comp_apply, neg_div, neg_zero] using h

theorem integrable_c5ThermalMinus {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun v : ℝ => thermalTest Y (Real.exp (-v))) (Ioi (0 : ℝ)) := by
  have hR := integrableOn_Ioi_deriv_of_nonneg' (a := (0 : ℝ))
    (fun v hv => c5ThermalMinusPrimitive_deriv Y v)
    (fun v hv => c5ThermalReal_nonneg hY (Real.exp_pos (-v)).le)
    (c5ThermalMinusPrimitive_limit Y)
  have hcont : Continuous (fun v : ℝ => thermalTest Y (Real.exp (-v))) := by
    exact (thermalTest_continuous Y).comp (continuous_id.neg.rexp)
  apply hR.mono' hcont.aestronglyMeasurable
  filter_upwards with v
  rw [thermalTest_eq_c5ThermalReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (c5ThermalReal_nonneg hY (Real.exp_pos (-v)).le)]

theorem integral_c5ThermalMinus {Y : ℝ} (hY : 0 < Y) :
    (∫ v : ℝ in Ioi 0, thermalTest Y (Real.exp (-v))) =
      ((1 - Real.exp (-1 / Y) : ℝ) : ℂ) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ))
    (fun v hv => c5ThermalMinusPrimitive_deriv Y v)
    (fun v hv => c5ThermalReal_nonneg hY (Real.exp_pos (-v)).le)
    (c5ThermalMinusPrimitive_limit Y)
  simp only [neg_zero, Real.exp_zero] at h
  simp_rw [thermalTest_eq_c5ThermalReal]
  rw [integral_ofReal, h]

theorem integrable_c5ThermalPlus {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun v : ℝ => thermalTest Y (Real.exp v)) (Ioi (0 : ℝ)) := by
  have hR := integrableOn_Ioi_deriv_of_nonneg' (a := (0 : ℝ))
    (fun v hv => c5ThermalPlusPrimitive_deriv Y v)
    (fun v hv => c5ThermalReal_nonneg hY (Real.exp_pos v).le)
    (c5ThermalPlusPrimitive_limit hY)
  have hcont : Continuous (fun v : ℝ => thermalTest Y (Real.exp v)) :=
    (thermalTest_continuous Y).comp Real.continuous_exp
  apply hR.mono' hcont.aestronglyMeasurable
  filter_upwards with v
  rw [thermalTest_eq_c5ThermalReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (c5ThermalReal_nonneg hY (Real.exp_pos v).le)]

theorem integral_c5ThermalPlus {Y : ℝ} (hY : 0 < Y) :
    (∫ v : ℝ in Ioi 0, thermalTest Y (Real.exp v)) = (Real.exp (-1 / Y) : ℂ) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ))
    (fun v hv => c5ThermalPlusPrimitive_deriv Y v)
    (fun v hv => c5ThermalReal_nonneg hY (Real.exp_pos v).le)
    (c5ThermalPlusPrimitive_limit hY)
  simp only [Real.exp_zero, zero_sub, neg_neg] at h
  simp_rw [thermalTest_eq_c5ThermalReal]
  rw [integral_ofReal, h]

theorem c5Logistic_nonneg (v : ℝ) : 0 ≤ c5Logistic v := by
  unfold c5Logistic
  positivity

theorem c5Logistic_le_exp (v : ℝ) : c5Logistic v ≤ Real.exp (-v) := by
  unfold c5Logistic
  apply (div_le_iff₀ (by positivity : 0 < 1 + Real.exp (-v))).mpr
  nlinarith [Real.exp_pos (-v)]

theorem integrable_c5Logistic : IntegrableOn c5Logistic (Ioi (0 : ℝ)) := by
  have h := integrableOn_exp_negative_scale (a := (1 : ℝ)) (by norm_num)
  simp only [neg_one_mul] at h
  have hcont : Continuous c5Logistic := by
    unfold c5Logistic
    fun_prop (disch := positivity)
  apply h.mono' hcont.aestronglyMeasurable
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_of_nonneg (c5Logistic_nonneg v)]
  exact c5Logistic_le_exp v

theorem c5LogisticPrimitive_deriv (v : ℝ) :
    HasDerivAt (fun w : ℝ => -Real.log (1 + Real.exp (-w))) (c5Logistic v) v := by
  have h := (((hasDerivAt_const v (1 : ℝ)).add
    (hasDerivAt_id v).neg.exp).log
      (by positivity : 1 + Real.exp (-v) ≠ 0)).neg
  simp only [mul_one, zero_add] at h
  convert h using 1
  unfold c5Logistic
  ring

theorem c5LogisticPrimitive_limit :
    Tendsto (fun v : ℝ => -Real.log (1 + Real.exp (-v))) atTop (𝓝 0) := by
  have harg : Tendsto (fun v : ℝ => 1 + Real.exp (-v)) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero)
  have h := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg).neg
  simpa only [Real.log_one, neg_zero] using h

theorem integral_c5Logistic : (∫ v : ℝ in Ioi 0, c5Logistic v) = Real.log 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun v hv => c5LogisticPrimitive_deriv v) integrable_c5Logistic
    c5LogisticPrimitive_limit
  simpa only [neg_zero, Real.exp_zero, one_add_one_eq_two, zero_sub, neg_neg] using h

theorem integrable_c5Logistic_complex :
    IntegrableOn (fun v : ℝ => (c5Logistic v : ℂ)) (Ioi (0 : ℝ)) := by
  have hcont : Continuous (fun v : ℝ => (c5Logistic v : ℂ)) := by
    unfold c5Logistic
    fun_prop (disch := positivity)
  apply integrable_c5Logistic.mono' hcont.aestronglyMeasurable
  filter_upwards with v
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (c5Logistic_nonneg v)]

theorem c5ArchLog_eq_Mellin_correction (Y : ℝ) {v : ℝ} (hv : 0 < v) :
    c5ArchLogKernel Y v = c5MellinImageKernel Y v + thermalTest Y (Real.exp v) -
      (2 * thermalTest Y 1) * (c5Logistic v : ℂ) := by
  have he2 : Real.exp (-2 * v) = Real.exp (-v) ^ 2 := by
    rw [show -2 * v = -v + -v by ring, Real.exp_add, pow_two]
  have hd : ((1 - Real.exp (-2 * v) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (psiDenominator_pos hv).ne'
  have hp : ((1 + Real.exp (-v) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  unfold c5ArchLogKernel c5MellinImageKernel c5Logistic
  rw [he2] at hd ⊢
  push_cast at hd hp ⊢
  field_simp [hd, hp] <;> ring

theorem integrable_c5ArchLogKernel {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (c5ArchLogKernel Y) (Ioi (0 : ℝ)) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have h := ((integrable_c5MellinImageKernel hY).add (integrable_c5ThermalPlus hY0)).sub
    (integrable_c5Logistic_complex.const_mul (2 * thermalTest Y 1))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (c5ArchLog_eq_Mellin_correction Y hv).symm

theorem integral_c5ArchLog_correction {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ v : ℝ in Ioi 0, c5ArchLogKernel Y v) =
      (∫ v : ℝ in Ioi 0, c5MellinImageKernel Y v) + (Real.exp (-1 / Y) : ℂ) -
        (2 * thermalTest Y 1) * (Real.log 2 : ℂ) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hm := integrable_c5MellinImageKernel hY
  have hf := integrable_c5ThermalPlus hY0
  have hq := integrable_c5Logistic_complex.const_mul (2 * thermalTest Y 1)
  have heq : c5ArchLogKernel Y =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun v => c5MellinImageKernel Y v + thermalTest Y (Real.exp v) -
        (2 * thermalTest Y 1) * (c5Logistic v : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact c5ArchLog_eq_Mellin_correction Y hv
  rw [integral_congr_ae heq, integral_sub (hm.add hf) hq, integral_add hm hf,
    integral_c5ThermalPlus hY0, integral_mul_left, integral_ofReal, integral_c5Logistic]

theorem c5Exp_image_positive : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact Real.one_lt_exp_iff.mpr hv
  · intro hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    exact ⟨Real.log x, Real.log_pos hx, Real.exp_log hx0⟩

theorem c5Arch_exp_jacobian (Y : ℝ) {v : ℝ} (hv : 0 < v) :
    |Real.exp v| • c5ArchKernel Y (Real.exp v) = c5ArchLogKernel Y v := by
  have hx : 0 < Real.exp v := Real.exp_pos v
  have hx1 : 1 < Real.exp v := Real.one_lt_exp_iff.mpr hv
  have hi : (Real.exp v)⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr hx1.le
  have hd : (Real.exp v : ℂ) - (Real.exp v : ℂ)⁻¹ ≠ 0 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hc : (Real.exp v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he2 : Real.exp (-2 * v) = (Real.exp v)⁻¹ ^ 2 := by
    rw [show -2 * v = -v + -v by ring, Real.exp_add, Real.exp_neg, pow_two]
  have hq : ((1 - Real.exp (-2 * v) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (psiDenominator_pos hv).ne'
  rw [abs_of_pos hx, Complex.real_smul]
  unfold c5ArchKernel c5ArchLogKernel
  rw [he2] at hq ⊢
  rw [Real.exp_neg]
  push_cast at hq ⊢
  field_simp [hd, hc, hq] <;> ring

theorem integrable_c5ArchKernel {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (c5ArchKernel Y) (Ioi (1 : ℝ)) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun v hv => (Real.hasDerivAt_exp v).hasDerivWithinAt)
    Real.exp_injective.injOn (c5ArchKernel Y)
  rw [c5Exp_image_positive] at hchange
  apply hchange.mpr
  apply (integrable_c5ArchLogKernel hY).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (c5Arch_exp_jacobian Y hv).symm

theorem integral_c5ArchKernel_eq_logKernel (Y : ℝ) :
    (∫ x : ℝ in Ioi 1, c5ArchKernel Y x) =
      ∫ v : ℝ in Ioi 0, c5ArchLogKernel Y v := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun v hv => (Real.hasDerivAt_exp v).hasDerivWithinAt)
    Real.exp_injective.injOn (c5ArchKernel Y)
  rw [c5Exp_image_positive] at hchange
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact c5Arch_exp_jacobian Y hv

theorem c5ArchKernel_eq_real (Y x : ℝ) :
    c5ArchKernel Y x = (c5ArchRealKernel Y x : ℂ) := by
  unfold c5ArchKernel c5ArchRealKernel
  simp only [thermalTest_eq_c5ThermalReal, one_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_inv, Complex.ofReal_ofNat]

theorem integral_c5ArchKernel_eq_real (Y : ℝ) :
    (∫ x : ℝ in Ioi 1, c5ArchKernel Y x) =
      ((∫ x : ℝ in Ioi 1, c5ArchRealKernel Y x) : ℂ) := by
  simp_rw [c5ArchKernel_eq_real]
  exact integral_ofReal

theorem integrable_c5ArchRealKernel {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (c5ArchRealKernel Y) (Ioi (1 : ℝ)) := by
  have h := (integrable_c5ArchKernel hY).re
  change Integrable (fun x : ℝ => (c5ArchKernel Y x).re)
    (volume.restrict (Ioi (1 : ℝ))) at h
  simpa only [c5ArchKernel_eq_real, Complex.ofReal_re] using h

theorem log_four_pi_eq_log_pi_add_two_log_two :
    Real.log (4 * Real.pi) = Real.log Real.pi + 2 * Real.log 2 := by
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero,
    show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- C5 for the genuine Gamma/chi contour and the independently defined C2
    Arch integrand. Every term is retained; the -1 comes from the two FTC
    values 1-exp(-1/Y) and exp(-1/Y), never from a selected normalization. -/
theorem thermalC5_arch_identity {Y : ℝ} (hY : 1 ≤ Y) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ,
      gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
        (deriv contourChi (leftChiPoint t) / contourChi (leftChiPoint t))) =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        thermalTest Y 1) + (∫ x : ℝ in Ioi 1, c5ArchKernel Y x) - 1 := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hM := integral_c5ArchLog_correction hY
  rw [← integral_c5ArchKernel_eq_logKernel Y] at hM
  rw [c5Chi_preArch_identity hY, integral_c5ThermalMinus hY0,
    log_four_pi_eq_log_pi_add_two_log_two]
  push_cast at hM ⊢
  linear_combination -hM

/-- The same C5 identity with the actual real C2 integral, including the
    quotient f(1/x)/x and both factors of log(2). -/
theorem thermalC5_arch_real_identity {Y : ℝ} (hY : 1 ≤ Y) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ,
      gammaContourFactor Y (-(1 / 2 : ℝ)) 1 t *
        (deriv contourChi (leftChiPoint t) / contourChi (leftChiPoint t))) =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        thermalTest Y 1) + ((∫ x : ℝ in Ioi 1, c5ArchRealKernel Y x) : ℂ) - 1 := by
  rw [← integral_c5ArchKernel_eq_real]
  exact thermalC5_arch_identity hY

end GoldbachContinuous22

#print axioms GoldbachContinuous22.c5ThermalReal
#print axioms GoldbachContinuous22.c5Logistic
#print axioms GoldbachContinuous22.c5ArchKernel
#print axioms GoldbachContinuous22.c5ArchRealKernel
#print axioms GoldbachContinuous22.c5ArchLogKernel
#print axioms GoldbachContinuous22.c5ThermalReal_nonneg
#print axioms GoldbachContinuous22.thermalTest_eq_c5ThermalReal
#print axioms GoldbachContinuous22.c5ThermalMinusPrimitive_deriv
#print axioms GoldbachContinuous22.c5ThermalMinusPrimitive_limit
#print axioms GoldbachContinuous22.c5ThermalPlusPrimitive_deriv
#print axioms GoldbachContinuous22.c5ThermalPlusPrimitive_limit
#print axioms GoldbachContinuous22.integrable_c5ThermalMinus
#print axioms GoldbachContinuous22.integral_c5ThermalMinus
#print axioms GoldbachContinuous22.integrable_c5ThermalPlus
#print axioms GoldbachContinuous22.integral_c5ThermalPlus
#print axioms GoldbachContinuous22.c5Logistic_nonneg
#print axioms GoldbachContinuous22.c5Logistic_le_exp
#print axioms GoldbachContinuous22.integrable_c5Logistic
#print axioms GoldbachContinuous22.c5LogisticPrimitive_deriv
#print axioms GoldbachContinuous22.c5LogisticPrimitive_limit
#print axioms GoldbachContinuous22.integral_c5Logistic
#print axioms GoldbachContinuous22.integrable_c5Logistic_complex
#print axioms GoldbachContinuous22.c5ArchLog_eq_Mellin_correction
#print axioms GoldbachContinuous22.integrable_c5ArchLogKernel
#print axioms GoldbachContinuous22.integral_c5ArchLog_correction
#print axioms GoldbachContinuous22.c5Exp_image_positive
#print axioms GoldbachContinuous22.c5Arch_exp_jacobian
#print axioms GoldbachContinuous22.integrable_c5ArchKernel
#print axioms GoldbachContinuous22.integral_c5ArchKernel_eq_logKernel
#print axioms GoldbachContinuous22.c5ArchKernel_eq_real
#print axioms GoldbachContinuous22.integral_c5ArchKernel_eq_real
#print axioms GoldbachContinuous22.integrable_c5ArchRealKernel
#print axioms GoldbachContinuous22.log_four_pi_eq_log_pi_add_two_log_two
#print axioms GoldbachContinuous22.thermalC5_arch_identity
#print axioms GoldbachContinuous22.thermalC5_arch_real_identity
