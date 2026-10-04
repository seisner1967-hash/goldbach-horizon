import MellinThermal22
import GammaContourComponent22

/- SOURCE_ONLY. Mellin inversion is applied to the actual thermal test only
   after constructing absolute convergence of its transform on the whole
   real vertical line. The two fixed H1 lines c=-1/2 and c=3/2 are included.
   This does not justify multiplication by the zeta logarithmic derivative,
   interchange with the prime-power sum, or the global C3 trace identity. -/

noncomputable section

open Set MeasureTheory Complex
open scoped Topology

namespace GoldbachContinuous22

theorem gammaContourFactor_vertical_integrable {Y c : ℝ} (hY : 1 ≤ Y)
    (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2) :
    Integrable (gammaContourFactor Y c 1) := by
  have hpos := (gammaContourFactor_tail_integrable_and_bound hY hc0 hc1
    (by norm_num : |(1 : ℝ)| = 1) (by norm_num : (0 : ℝ) ≤ 0)).1
  have hnegativeMode := (gammaContourFactor_tail_integrable_and_bound hY hc0 hc1
    (by norm_num : |(-1 : ℝ)| = 1) (by norm_num : (0 : ℝ) ≤ 0)).1
  have hreflection := (MeasurePreserving.integrableOn_comp_preimage
    (Measure.measurePreserving_neg volume) (Homeomorph.neg ℝ).measurableEmbedding).2
    hnegativeMode
  have hneg : IntegrableOn (gammaContourFactor Y c 1) (Iio 0) := by
    convert hreflection using 1
    · ext t
      simp [gammaContourFactor, gammaContourPoint]
    · ext t
      simp
  have hnonpos : IntegrableOn (gammaContourFactor Y c 1) (Iic 0) :=
    integrableOn_Iic_iff_integrableOn_Iio.mpr hneg
  have hcover : Iic (0 : ℝ) ∪ Ioi 0 = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 0
  rw [← integrableOn_univ, ← hcover, integrableOn_union]
  exact ⟨hnonpos, hpos⟩

theorem thermalTest_mellin_vertical_integrable {Y c : ℝ}
    (hY : 1 ≤ Y) (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2) :
    VerticalIntegrable (mellin (thermalTest Y)) c := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hf := gammaContourFactor_vertical_integrable hY hc0 hc1
  apply hf.congr
  filter_upwards with t
  rw [mellin_thermalTest hY0 (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith)]
  simp only [gammaContourFactor, gammaContourPoint, one_mul,
    weightedGammaTerm_eq_cpow hY0]

/-- The true inversion on both H1 lines; there is no free Mellin premise. -/
theorem thermalTest_mellin_inversion {Y c x : ℝ} (hY : 1 ≤ Y)
    (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2) (hx : 0 < x) :
    mellinInv c (mellin (thermalTest Y)) x = thermalTest Y x := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  exact mellin_inversion c (thermalTest Y) hx
    (thermalTest_mellin_convergent hY0 (by
      simp only [Complex.ofReal_re]
      linarith))
    (thermalTest_mellin_vertical_integrable hY hc0 hc1)
    (thermalTest_continuous Y).continuousAt

theorem thermalTest_gamma_inversion {Y c x : ℝ} (hY : 1 ≤ Y)
    (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2) (hx : 0 < x) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
        ((Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
          Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I + 1))) = thermalTest Y x := by
  have h := thermalTest_mellin_inversion hY hc0 hc1 hx
  unfold mellinInv at h
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have heq : (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) •
      mellin (thermalTest Y) ((c : ℂ) + (t : ℂ) * Complex.I)) =
      (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
        ((Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
          Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I + 1))) := by
    ext t
    rw [mellin_thermalTest hY0 (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, add_zero]
      linarith), smul_eq_mul]
  rwa [heq] at h

end GoldbachContinuous22

#print axioms GoldbachContinuous22.gammaContourFactor_vertical_integrable
#print axioms GoldbachContinuous22.thermalTest_mellin_vertical_integrable
#print axioms GoldbachContinuous22.thermalTest_mellin_inversion
#print axioms GoldbachContinuous22.thermalTest_gamma_inversion
