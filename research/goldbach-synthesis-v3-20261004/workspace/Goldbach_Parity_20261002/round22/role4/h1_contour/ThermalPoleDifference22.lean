import ThermalPoleMellin22
import Mathlib.Analysis.SpecialFunctions.Integrals

/- SOURCE_ONLY. The left rational-pole integral and its difference with the
   right line are obtained by actual Mellin inversion and paid Fubini. The
   result is Y because the thermal test has its proved Mellin value at s=1.
   No contour-shift, residue theorem, or free pole identity is assumed.
   The normalizer is 1/(2*pi); alpha retains its monograph meaning. -/

noncomputable section
open Complex Set MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

theorem thermalPole_left_inner_integral {Y d : ℝ} (hd : d < 1) (t : ℝ) :
    (∫ x : ℝ, thermalRectangleIntegrand Y d (Ioo 0 1) x t) =
      -(gammaContourFactor Y d 1 t / (gammaContourPoint d 1 t - 1)) := by
  change (∫ x : ℝ, (Ioo (0 : ℝ) 1).indicator
    (fun u : ℝ => thermalMellinPower u d t) x * gammaContourFactor Y d 1 t) = _
  rw [integral_mul_right, integral_indicator measurableSet_Ioo]
  have hcpow : (∫ x : ℝ in Ioo 0 1, thermalMellinPower x d t) =
      ∫ x : ℝ in Ioo 0 1, (x : ℂ) ^ (-gammaContourPoint d 1 t) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact thermalMellinPower_eq_cpow hx.1 d t
  have hre : -1 < (-gammaContourPoint d 1 t).re := by
    simp only [Complex.neg_re, gammaContourPoint, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hne : -gammaContourPoint d 1 t + 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  rw [hcpow, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_cpow (Or.inl hre)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow,
    Complex.zero_cpow hne, sub_zero]
  have hden : -gammaContourPoint d 1 t + 1 = -(gammaContourPoint d 1 t - 1) := by
    ring
  rw [hden, div_neg]
  ring

theorem thermalPole_left_mellin_identity {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd : d < 1) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, gammaContourFactor Y d 1 t /
        (gammaContourPoint d 1 t - 1)) =
      -(∫ x : ℝ in Ioo 0 1, thermalTest Y x) := by
  have hd1 : d ≤ 3 / 2 := by linarith
  have hx : IntegrableOn (fun x : ℝ => x ^ (-d)) (Ioo 0 1) :=
    (integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
  have hpos : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
  have h := thermalRectangle_mellin_exchange hY hd0 hd1 measurableSet_Ioo hpos hx
  have heq : (fun t : ℝ => ∫ x : ℝ, thermalRectangleIntegrand Y d (Ioo 0 1) x t) =
      (fun t : ℝ => -(gammaContourFactor Y d 1 t /
        (gammaContourPoint d 1 t - 1))) := funext (thermalPole_left_inner_integral hd)
  rw [heq, integral_neg, smul_neg] at h
  exact neg_eq_iff_eq_neg.mp h

theorem thermalPole_left_vertical_integrable {Y d : ℝ} (hY : 1 ≤ Y)
    (hd0 : -(1 / 2) ≤ d) (hd : d < 1) :
    Integrable (fun t : ℝ => gammaContourFactor Y d 1 t /
      (gammaContourPoint d 1 t - 1)) := by
  have hd1 : d ≤ 3 / 2 := by linarith
  have hx : IntegrableOn (fun x : ℝ => x ^ (-d)) (Ioo 0 1) :=
    (integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
  have hpos : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
  have hint := thermalRectangleIntegrand_integrable hY hd0 hd1
    measurableSet_Ioo hpos hx
  have hneg : Integrable (fun t : ℝ => -(gammaContourFactor Y d 1 t /
      (gammaContourPoint d 1 t - 1))) := by
    apply hint.integral_prod_right.congr
    filter_upwards with t
    exact thermalPole_left_inner_integral hd t
  simpa only [neg_neg] using hneg.neg

theorem thermalTest_positive_integrable {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (thermalTest Y) (Ioi 0) := by
  have h := thermalTest_mellin_convergent (s := (1 : ℂ)) hY (by norm_num)
  simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul] using h

theorem thermalTest_positive_integral {Y : ℝ} (hY : 0 < Y) :
    (∫ x : ℝ in Ioi 0, thermalTest Y x) = (Y : ℂ) := by
  have h := mellin_thermalTest (s := (1 : ℂ)) hY (by norm_num)
  have hg : Complex.Gamma ((1 : ℂ) + 1) = 1 := by
    rw [Complex.Gamma_add_one (1 : ℂ) one_ne_zero, Complex.Gamma_one, one_mul]
  simpa only [mellin, sub_self, Complex.cpow_zero, one_smul, Complex.cpow_one,
    hg, mul_one] using h

theorem thermalTest_split_at_one {Y : ℝ} (hY : 0 < Y) :
    (∫ x : ℝ in Ioi 0, thermalTest Y x) =
      (∫ x : ℝ in Ioo 0 1, thermalTest Y x) +
      (∫ x : ℝ in Ioi 1, thermalTest Y x) := by
  have hint := thermalTest_positive_integrable hY
  have hl : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
  have hr : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := fun _ hx => lt_trans zero_lt_one hx
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact (not_lt_of_ge hx.2) hx'
  have hset : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact lt_trans zero_lt_one hx
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (lt_of_not_ge hx1)
  have h := setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set hl) (hint.mono_set hr)
  rwa [hset, integral_Ioc_eq_integral_Ioo] at h

/-- The entire rational-pole difference contributes exactly Y. This is a
    consequence of two paid Mellin/Fubini calculations, not a contour axiom. -/
theorem thermalPole_difference_eq_Y {Y c d : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) (hd0 : -(1 / 2) ≤ d) (hd : d < 1) :
    (1 / (2 * Real.pi)) •
      ((∫ t : ℝ, gammaContourFactor Y c 1 t /
        (gammaContourPoint c 1 t - 1)) -
       (∫ t : ℝ, gammaContourFactor Y d 1 t /
        (gammaContourPoint d 1 t - 1))) = (Y : ℂ) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  rw [smul_sub, thermalPole_right_mellin_identity hY hc hc1,
    thermalPole_left_mellin_identity hY hd0 hd, sub_neg_eq_add, add_comm,
    ← thermalTest_split_at_one hY0, thermalTest_positive_integral hY0]

end GoldbachContinuous22

#print axioms GoldbachContinuous22.thermalPole_left_inner_integral
#print axioms GoldbachContinuous22.thermalPole_left_mellin_identity
#print axioms GoldbachContinuous22.thermalPole_left_vertical_integrable
#print axioms GoldbachContinuous22.thermalTest_positive_integrable
#print axioms GoldbachContinuous22.thermalTest_positive_integral
#print axioms GoldbachContinuous22.thermalTest_split_at_one
#print axioms GoldbachContinuous22.thermalPole_difference_eq_Y
