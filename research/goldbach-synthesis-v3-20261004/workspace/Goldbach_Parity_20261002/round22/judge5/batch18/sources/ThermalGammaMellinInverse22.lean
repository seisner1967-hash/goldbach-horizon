import GammaPrerequisites22
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-! SOURCE ONLY. The scalar exponential is recovered from the genuine Gamma
function by Mellin inversion at Re(s)=2. Mellin convergence and vertical L1
are derived here, rather than supplied as assumptions. GammaPrerequisites22
is a readonly independently checked dependency; this new source is uncompiled.
The Lambda exchange and complex-rate holomorphic continuation remain separate
obligations. No theorem for the final thermal trace is assumed or asserted. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace GoldbachThermalMellin22

def expKernel (x : ℝ) : ℂ := (Real.exp (-x) : ℂ)

def gammaLine (t : ℝ) : ℂ := Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)

theorem expKernel_continuous : Continuous expKernel := by
  unfold expKernel
  fun_prop

theorem gammaLine_continuous : Continuous gammaLine := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have harg : Continuous (fun u : ℝ => (2 : ℂ) + (u : ℂ) * Complex.I) := by fun_prop
  have hre : ((2 : ℂ) + (t : ℂ) * Complex.I).re = 2 := by simp
  have hg : ContinuousAt Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) :=
    (Complex.differentiableAt_Gamma _ (fun n => by
      intro hn
      have hr := congrArg Complex.re hn
      simp only [hre, Complex.neg_re, Complex.natCast_re] at hr
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith)).continuousAt
  exact hg.comp harg.continuousAt

/-- Positive and negative Gamma half-lines share a derived integrable envelope. -/
theorem gammaLine_half_integrable (negative : Bool) :
    IntegrableOn (fun t : ℝ => gammaLine (if negative then -t else t)) (Ioi 0) := by
  have hc : (0 : ℝ) < Real.pi / 4 := by positivity
  have hm : IntegrableOn (fun t : ℝ => 2 * Real.exp (-(Real.pi / 4) * t)) (Ioi 0) := by
    have h := (GoldbachContinuous22.real_laplace_integrable
      (a := (1 : ℝ)) (r := Real.pi / 4) (by norm_num) hc).const_mul 2
    simpa only [sub_self, Real.rpow_zero, mul_one, neg_mul] using h
  have hsign : Continuous (fun t : ℝ => if negative then -t else t) := by
    cases negative <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  apply hm.mono' (gammaLine_continuous.comp hsign).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hbound := GoldbachContinuous22.Gamma_strip_exponential_bound
    (s := (2 : ℂ) + ((if negative then -t else t : ℝ) : ℂ) * Complex.I)
    (by simp) (by simp)
  have him : ((2 : ℂ) + ((if negative then -t else t : ℝ) : ℂ) * Complex.I).im =
      (if negative then -t else t) := by simp
  rw [him] at hbound
  cases negative <;>
    simpa only [gammaLine, Bool.false_eq_true, if_false, if_true,
      abs_neg, abs_of_pos ht] using hbound

/-- Vertical Gamma integrability pays the Fourier-inversion prerequisite. -/
theorem gammaLine_integrable : Integrable gammaLine := by
  have hp : IntegrableOn gammaLine (Ioi 0) := by
    simpa only [Bool.false_eq_true, if_false] using gammaLine_half_integrable false
  have hn : IntegrableOn (fun t : ℝ => gammaLine (-t)) (Ioi 0) := by
    simpa only [if_true] using gammaLine_half_integrable true
  have hpre : (fun t : ℝ => -t) ⁻¹' Iio 0 = Ioi 0 := by
    ext t
    simp
  have hn' : IntegrableOn gammaLine (Iio 0) := by
    have ht : IntegrableOn (gammaLine ∘ (fun t : ℝ => -t))
        ((fun t : ℝ => -t) ⁻¹' Iio 0) := by
      simpa only [hpre, Function.comp_apply] using hn
    exact (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).mp ht
  have hl : IntegrableOn gammaLine (Iic 0) :=
    integrableOn_Iic_iff_integrableOn_Iio.mpr hn'
  have hu : Iic (0 : ℝ) ∪ Ioi 0 = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 0
  have hw := hl.union hp
  rw [hu] at hw
  exact integrableOn_univ.mp hw

theorem expKernel_mellin_convergent_two : MellinConvergent expKernel (2 : ℂ) := by
  have h := Complex.GammaIntegral_convergent (s := (2 : ℂ)) (by norm_num)
  simpa only [MellinConvergent, expKernel, smul_eq_mul, mul_comm] using h

/-- The Mellin transform is the actual Gamma function on its convergent domain. -/
theorem mellin_expKernel_eq_Gamma {s : ℂ} (hs : 0 < s.re) :
    mellin expKernel s = Complex.Gamma s := by
  calc
    _ = Complex.GammaIntegral s := (congrFun Complex.GammaIntegral_eq_mellin s).symm
    _ = _ := (Complex.Gamma_eq_integral hs).symm

theorem expKernel_mellin_vertical_two :
    Complex.VerticalIntegrable (mellin expKernel) (2 : ℝ) := by
  change Integrable (fun t : ℝ => mellin expKernel ((2 : ℂ) + (t : ℂ) * Complex.I))
  have heq : (fun t : ℝ => mellin expKernel ((2 : ℂ) + (t : ℂ) * Complex.I)) = gammaLine := by
    funext t
    exact mellin_expKernel_eq_Gamma (by simp)
  rw [heq]
  exact gammaLine_integrable

/-- Real Mellin inversion, with both actual L1 prerequisites derived above. -/
theorem mellinInv_Gamma_two {x : ℝ} (hx : 0 < x) :
    mellinInv 2 Complex.Gamma x = expKernel x := by
  have hi := mellin_inversion (2 : ℝ) expKernel hx
    expKernel_mellin_convergent_two expKernel_mellin_vertical_two
    expKernel_continuous.continuousAt
  have he : mellinInv 2 (mellin expKernel) x = mellinInv 2 Complex.Gamma x := by
    unfold mellinInv
    apply congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z)
    apply integral_congr_ae
    filter_upwards with t
    rw [mellin_expKernel_eq_Gamma (by simp)]
  rw [he] at hi
  exact hi

/-- The concrete normalized integral; the orientation and 1/(2*pi) are explicit. -/
theorem real_exp_eq_Gamma_integral {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
        (x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hi := (mellinInv_Gamma_two hx).symm
  simpa only [expKernel, mellinInv, Complex.real_smul, smul_eq_mul, mul_comm] using hi

end GoldbachThermalMellin22

#print axioms GoldbachThermalMellin22.expKernel
#print axioms GoldbachThermalMellin22.gammaLine
#print axioms GoldbachThermalMellin22.expKernel_continuous
#print axioms GoldbachThermalMellin22.gammaLine_continuous
#print axioms GoldbachThermalMellin22.gammaLine_half_integrable
#print axioms GoldbachThermalMellin22.gammaLine_integrable
#print axioms GoldbachThermalMellin22.expKernel_mellin_convergent_two
#print axioms GoldbachThermalMellin22.mellin_expKernel_eq_Gamma
#print axioms GoldbachThermalMellin22.expKernel_mellin_vertical_two
#print axioms GoldbachThermalMellin22.mellinInv_Gamma_two
#print axioms GoldbachThermalMellin22.real_exp_eq_Gamma_integral
