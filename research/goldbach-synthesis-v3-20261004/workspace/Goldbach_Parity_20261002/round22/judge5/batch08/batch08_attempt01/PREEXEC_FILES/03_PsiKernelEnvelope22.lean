import ContourChiScaled22
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! SOURCE ONLY. This is the explicit continuous envelope proposed for the
future mixed-integrability proof. Its continuity and v-integrability are
derived, not assumed. The kernel domination and the true G factor are still
separate obligations; this file makes no Fubini or C5 claim. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def psiKernelEnvelope (t v : ℝ) : ℝ :=
  (14 + 4 * |t|) * Real.exp (1 - v) + 8 * Real.exp (-(3 / 2 : ℝ) * v)

theorem psiKernelEnvelope_nonneg (t v : ℝ) : 0 ≤ psiKernelEnvelope t v := by
  unfold psiKernelEnvelope
  positivity

theorem psiKernelEnvelope_joint_continuous :
    Continuous (fun p : ℝ × ℝ => psiKernelEnvelope p.1 p.2) := by
  unfold psiKernelEnvelope
  fun_prop

theorem psiKernelEnvelope_ge_near {t v : ℝ} (hv : v ≤ 1) :
    14 + 4 * |t| ≤ psiKernelEnvelope t v := by
  have hc : 0 ≤ 14 + 4 * |t| := by positivity
  have he : 1 ≤ Real.exp (1 - v) := Real.one_le_exp_iff.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left he hc
  have htail : 0 ≤ 8 * Real.exp (-(3 / 2 : ℝ) * v) := by positivity
  unfold psiKernelEnvelope
  nlinarith

theorem psiKernelEnvelope_ge_tail (t v : ℝ) :
    8 * Real.exp (-(3 / 2 : ℝ) * v) ≤ psiKernelEnvelope t v := by
  unfold psiKernelEnvelope
  have h : 0 ≤ (14 + 4 * |t|) * Real.exp (1 - v) := by positivity
  linarith

theorem negativeScale_image_Ioi {a : ℝ} (ha : 0 < a) :
    (fun v : ℝ => -a * v) '' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ha) hv
  · intro hu
    refine ⟨-u / a, div_pos (neg_pos.mpr hu) ha, ?_⟩
    field_simp [ha.ne'] <;> ring

theorem negativeScale_injOn_Ioi {a : ℝ} (ha : 0 < a) :
    InjOn (fun v : ℝ => -a * v) (Ioi (0 : ℝ)) := by
  intro v hv w hw h
  exact mul_left_cancel₀ (neg_ne_zero.mpr ha.ne') h

theorem integrableOn_exp_negative_scale {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun v : ℝ => Real.exp (-a * v)) (Ioi (0 : ℝ)) := by
  have hsource : IntegrableOn Real.exp (Iio (0 : ℝ)) :=
    (integrableOn_exp_Iic (0 : ℝ)).mono_set (fun v hv => hv.le)
  have himage : IntegrableOn Real.exp ((fun v : ℝ => -a * v) '' Ioi (0 : ℝ)) := by
    rw [negativeScale_image_Ioi ha]
    exact hsource
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun v hv => (by
      simpa only [mul_one] using (hasDerivAt_id v).const_mul (-a) :
        HasDerivAt (fun w : ℝ => -a * w) (-a) v).hasDerivWithinAt)
    (negativeScale_injOn_Ioi ha) Real.exp).mp himage
  have hj : IntegrableOn (fun v : ℝ => a * Real.exp (-a * v)) (Ioi (0 : ℝ)) := by
    simpa only [abs_neg, abs_of_pos ha, smul_eq_mul] using h
  apply (hj.div_const a).congr
  exact Eventually.of_forall (fun v => by field_simp [ha.ne'])

theorem integrableOn_psiKernelEnvelope (t : ℝ) :
    IntegrableOn (psiKernelEnvelope t) (Ioi (0 : ℝ)) := by
  have h1 := integrableOn_exp_negative_scale (by norm_num : (0 : ℝ) < 1)
  have h2 := integrableOn_exp_negative_scale (by norm_num : (0 : ℝ) < 3 / 2)
  have h := (h1.const_mul ((14 + 4 * |t|) * Real.exp 1)).add (h2.const_mul 8)
  apply h.congr
  filter_upwards with v
  unfold psiKernelEnvelope
  rw [show 1 - v = 1 + -v by ring, Real.exp_add]
  simp only [neg_one_mul]
  ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.psiKernelEnvelope
#print axioms GoldbachContinuous22.psiKernelEnvelope_nonneg
#print axioms GoldbachContinuous22.psiKernelEnvelope_joint_continuous
#print axioms GoldbachContinuous22.psiKernelEnvelope_ge_near
#print axioms GoldbachContinuous22.psiKernelEnvelope_ge_tail
#print axioms GoldbachContinuous22.negativeScale_image_Ioi
#print axioms GoldbachContinuous22.negativeScale_injOn_Ioi
#print axioms GoldbachContinuous22.integrableOn_exp_negative_scale
#print axioms GoldbachContinuous22.integrableOn_psiKernelEnvelope
