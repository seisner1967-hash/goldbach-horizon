import MellinDualLambdaInterchange22
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/- SOURCE_ONLY. The rational-pole contribution is derived from actual Mellin
   inversion and a constructed two-dimensional Fubini dominateur. Cpi denotes
   1/(2*pi), never the canonical arithmetic cutoff alpha. Auxiliary set lemmas
   carry ordinary domain/integrability hypotheses; the right-line conclusion
   pays these hypotheses for the fixed domain x>1. No contour identity assumed.
   The complementary left-line calculation and its difference Y remain open. -/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def thermalMellinPower (x c t : ℝ) : ℂ :=
  Complex.exp ((Real.log x : ℂ) * (-gammaContourPoint c 1 t))

def thermalRectangleIntegrand (Y c : ℝ) (S : Set ℝ) (x t : ℝ) : ℂ := by
  classical
  exact S.indicator (fun u : ℝ => thermalMellinPower u c t) x *
    gammaContourFactor Y c 1 t

theorem thermalMellinPower_eq_cpow {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    thermalMellinPower x c t = (x : ℂ) ^ (-gammaContourPoint c 1 t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  rfl

theorem thermalRectangleIntegrand_measurable {Y c : ℝ} {S : Set ℝ}
    (hc0 : -(1 / 2) ≤ c) (hS : MeasurableSet S) :
    Measurable (Function.uncurry (thermalRectangleIntegrand Y c S)) := by
  have hlog : Measurable (fun p : ℝ × ℝ => (Real.log p.1 : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)
  have hp : Measurable (fun p : ℝ × ℝ => -gammaContourPoint c 1 p.2) := by
    apply Continuous.measurable
    unfold gammaContourPoint
    fun_prop
  have hexp : Measurable (fun p : ℝ × ℝ => thermalMellinPower p.1 c p.2) :=
    Complex.continuous_exp.measurable.comp (hlog.mul hp)
  have hind := hexp.indicator (hS.preimage measurable_fst)
  have hG := (gammaContourFactor_continuous Y c 1 hc0).measurable.comp measurable_snd
  convert hind.mul hG using 1 <;>
    (ext p; classical; by_cases hpS : p.1 ∈ S <;>
      simp [thermalRectangleIntegrand, Function.uncurry,
        hpS, Set.indicator_of_mem, Set.indicator_of_not_mem])

theorem norm_thermalRectangleIntegrand {Y c : ℝ} {S : Set ℝ}
    (hSpos : S ⊆ Ioi (0 : ℝ)) (x t : ℝ) :
    ‖thermalRectangleIntegrand Y c S x t‖ =
      S.indicator (fun u : ℝ => u ^ (-c)) x * ‖gammaContourFactor Y c 1 t‖ := by
  classical
  by_cases hxS : x ∈ S
  · have hx : 0 < x := hSpos hxS
    rw [thermalRectangleIntegrand, Set.indicator_of_mem hxS,
      Set.indicator_of_mem hxS, norm_mul, thermalMellinPower_eq_cpow hx,
      Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.neg_re, gammaContourPoint, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  · simp [thermalRectangleIntegrand, Set.indicator_of_not_mem hxS]

theorem thermalRectangleIntegrand_integrable {Y c : ℝ} {S : Set ℝ}
    (hY : 1 ≤ Y) (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2)
    (hS : MeasurableSet S) (hSpos : S ⊆ Ioi (0 : ℝ))
    (hX : IntegrableOn (fun x : ℝ => x ^ (-c)) S) :
    Integrable (Function.uncurry (thermalRectangleIntegrand Y c S))
      (volume.prod volume) := by
  have hx := hX.integrable_indicator hS
  have hG := (gammaContourFactor_vertical_integrable hY hc0 hc1).norm
  have hbound := hx.prod_mul hG
  apply hbound.mono' (thermalRectangleIntegrand_measurable hc0 hS).aestronglyMeasurable
  filter_upwards with p
  exact (norm_thermalRectangleIntegrand hSpos p.1 p.2).le

theorem thermalRectangleIntegrand_single_inversion {Y c : ℝ} {S : Set ℝ}
    (hY : 1 ≤ Y) (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2)
    (hSpos : S ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ, thermalRectangleIntegrand Y c S x t) =
      S.indicator (thermalTest Y) x := by
  classical
  by_cases hxS : x ∈ S
  · have hx : 0 < x := hSpos hxS
    have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
    simp only [thermalRectangleIntegrand, Set.indicator_of_mem hxS,
      thermalMellinPower_eq_cpow hx, gammaContourFactor,
      weightedGammaTerm_eq_cpow hY0, gammaContourPoint, one_mul]
    exact thermalTest_gamma_inversion hY hc0 hc1 hx
  · simp [thermalRectangleIntegrand, Set.indicator_of_not_mem hxS]

/-- The Fubini exchange is paid by the product dominateur x^(-c)|G(c+it)|.
    The set/integrability parameters here are discharged in the fixed-pole
    theorem below; this auxiliary statement is not a free contour contract. -/
theorem thermalRectangle_mellin_exchange {Y c : ℝ} {S : Set ℝ}
    (hY : 1 ≤ Y) (hc0 : -(1 / 2) ≤ c) (hc1 : c ≤ 3 / 2)
    (hS : MeasurableSet S) (hSpos : S ⊆ Ioi (0 : ℝ))
    (hX : IntegrableOn (fun x : ℝ => x ^ (-c)) S) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, ∫ x : ℝ, thermalRectangleIntegrand Y c S x t) =
      ∫ x : ℝ in S, thermalTest Y x := by
  have hint := thermalRectangleIntegrand_integrable hY hc0 hc1 hS hSpos hX
  have hswap := integral_integral_swap hint
  calc
    _ = (1 / (2 * Real.pi)) •
        (∫ x : ℝ, ∫ t : ℝ, thermalRectangleIntegrand Y c S x t) := by
      rw [hswap]
    _ = ∫ x : ℝ, (1 / (2 * Real.pi)) •
        (∫ t : ℝ, thermalRectangleIntegrand Y c S x t) :=
      (integral_smul _ _).symm
    _ = ∫ x : ℝ, S.indicator (thermalTest Y) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact thermalRectangleIntegrand_single_inversion hY hc0 hc1 hSpos x
    _ = _ := integral_indicator hS

theorem thermalPole_right_inner_integral {Y c : ℝ} (hc : 1 < c) (t : ℝ) :
    (∫ x : ℝ, thermalRectangleIntegrand Y c (Ioi 1) x t) =
      gammaContourFactor Y c 1 t / (gammaContourPoint c 1 t - 1) := by
  have heq : (fun x : ℝ => thermalRectangleIntegrand Y c (Ioi 1) x t) =
      (fun x : ℝ => (Ioi (1 : ℝ)).indicator
        (fun u : ℝ => thermalMellinPower u c t) x * gammaContourFactor Y c 1 t) := rfl
  rw [heq, integral_mul_right, integral_indicator measurableSet_Ioi]
  have hcpow : (∫ x : ℝ in Ioi 1, thermalMellinPower x c t) =
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-gammaContourPoint c 1 t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact thermalMellinPower_eq_cpow (lt_trans zero_lt_one hx) c t
  rw [hcpow, integral_Ioi_cpow_of_lt (by
    simp only [Complex.neg_re, gammaContourPoint, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith) (by norm_num : (0 : ℝ) < 1)]
  have hs : gammaContourPoint c 1 t ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [gammaContourPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re] at hre
    linarith
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hden : -gammaContourPoint c 1 t + 1 = -(gammaContourPoint c 1 t - 1) := by ring
  rw [hden]
  field_simp [sub_ne_zero.mpr hs]
  ring

/-- Actual rational-pole integral on the right line. Every Fubini/domain
    hypothesis is constructed for x>1. Cpi is written explicitly. -/
theorem thermalPole_right_mellin_identity {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    (1 / (2 * Real.pi)) •
      (∫ t : ℝ, gammaContourFactor Y c 1 t /
        (gammaContourPoint c 1 t - 1)) =
      ∫ x : ℝ in Ioi 1, thermalTest Y x := by
  have hc0 : -(1 / 2) ≤ c := by linarith
  have hx : IntegrableOn (fun x : ℝ => x ^ (-c)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hpos : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := fun _ hx => lt_trans zero_lt_one hx
  have h := thermalRectangle_mellin_exchange hY hc0 hc1 measurableSet_Ioi hpos hx
  have heq : (fun t : ℝ => ∫ x : ℝ, thermalRectangleIntegrand Y c (Ioi 1) x t) =
      (fun t : ℝ => gammaContourFactor Y c 1 t / (gammaContourPoint c 1 t - 1)) :=
    funext (thermalPole_right_inner_integral hc)
  rwa [heq] at h

theorem thermalPole_right_vertical_integrable {Y c : ℝ} (hY : 1 ≤ Y)
    (hc : 1 < c) (hc1 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => gammaContourFactor Y c 1 t /
      (gammaContourPoint c 1 t - 1)) := by
  have hc0 : -(1 / 2) ≤ c := by linarith
  have hx : IntegrableOn (fun x : ℝ => x ^ (-c)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hpos : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := fun _ hx => lt_trans zero_lt_one hx
  have hint := thermalRectangleIntegrand_integrable hY hc0 hc1
    measurableSet_Ioi hpos hx
  apply hint.integral_prod_right.congr
  filter_upwards with t
  exact thermalPole_right_inner_integral hc t

end GoldbachContinuous22

#print axioms GoldbachContinuous22.thermalMellinPower
#print axioms GoldbachContinuous22.thermalRectangleIntegrand
#print axioms GoldbachContinuous22.thermalMellinPower_eq_cpow
#print axioms GoldbachContinuous22.thermalRectangleIntegrand_measurable
#print axioms GoldbachContinuous22.norm_thermalRectangleIntegrand
#print axioms GoldbachContinuous22.thermalRectangleIntegrand_integrable
#print axioms GoldbachContinuous22.thermalRectangleIntegrand_single_inversion
#print axioms GoldbachContinuous22.thermalRectangle_mellin_exchange
#print axioms GoldbachContinuous22.thermalPole_right_inner_integral
#print axioms GoldbachContinuous22.thermalPole_right_mellin_identity
#print axioms GoldbachContinuous22.thermalPole_right_vertical_integrable
