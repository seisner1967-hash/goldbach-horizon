import ThermalGammaMellinInverse22
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-! SOURCE ONLY, not compiled or probed by the author.
The local dependencies are the genuine Gamma rotation and real Mellin inversion
already independently checked in batches02/20. The fixed-w vertical L1 estimate
below is derived, not assumed. Local uniform derivative domination and the
analytic continuation of the integral remain separate, explicit obligations.
No Lambda exchange, zeta trace, PP/front correction or D_N bound is asserted.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace GoldbachComplexGammaMellin22

def verticalS (t : ℝ) : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I

def complexGammaKernel (w : ℂ) (t : ℝ) : ℂ :=
  Complex.Gamma (verticalS t) * w ^ (-verticalS t)

def rotationAngle (w : ℂ) : ℝ := (Real.pi / 2 + |Complex.arg w|) / 2

def decayGap (w : ℂ) : ℝ := rotationAngle w - |Complex.arg w|

def kernelCoefficient (w : ℂ) : ℝ :=
  ‖w‖ ^ (-2 : ℝ) * (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)

def complexGammaInverse (w : ℂ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ t : ℝ, complexGammaKernel w t

theorem verticalS_re (t : ℝ) : (verticalS t).re = 2 := by simp [verticalS]

theorem verticalS_im (t : ℝ) : (verticalS t).im = t := by simp [verticalS]

theorem verticalS_continuous : Continuous verticalS := by unfold verticalS; fun_prop

theorem rightHalfPlane_mem_slitPlane {w : ℂ} (hw : 0 < w.re) :
    w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw)

theorem rightHalfPlane_ne_zero {w : ℂ} (hw : 0 < w.re) : w ≠ 0 :=
  Complex.slitPlane_ne_zero (rightHalfPlane_mem_slitPlane hw)

theorem rotationAngle_pos (w : ℂ) : 0 < rotationAngle w := by
  dsimp only [rotationAngle]
  linarith [Real.pi_pos, abs_nonneg (Complex.arg w)]

theorem rotationAngle_lt_pi_half {w : ℂ} (hw : 0 < w.re) :
    rotationAngle w < Real.pi / 2 := by
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  dsimp only [rotationAngle]
  linarith

theorem decayGap_pos {w : ℂ} (hw : 0 < w.re) : 0 < decayGap w := by
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  dsimp only [decayGap, rotationAngle]
  linarith

/-- Both signs use a genuine admissible rotation; Gamma(2)=1 is evaluated. -/
theorem norm_Gamma_fixed_rotation {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    ‖Complex.Gamma (verticalS t)‖ ≤
      (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ) *
        Real.exp (-rotationAngle w * |t|) := by
  have hη0 := rotationAngle_pos w
  have hη1 := rotationAngle_lt_pi_half hw
  have hηlower : -(Real.pi / 2) < rotationAngle w := by linarith [Real.pi_pos]
  by_cases ht : 0 ≤ t
  · have h := GoldbachContinuous22.Gamma_rotation_bound
      (s := verticalS t) (theta := rotationAngle w)
      (by rw [verticalS_re]; norm_num) hηlower hη1
    rw [verticalS_re, verticalS_im, Real.Gamma_two, mul_one, Real.rpow_two] at h
    simpa only [abs_of_nonneg ht, mul_comm] using h
  · have hneg : t < 0 := lt_of_not_ge ht
    have h := GoldbachContinuous22.Gamma_rotation_bound
      (s := verticalS t) (theta := -rotationAngle w)
      (by rw [verticalS_re]; norm_num)
      (by linarith) (by linarith [Real.pi_pos])
    rw [verticalS_re, verticalS_im, Real.Gamma_two, Real.cos_neg, mul_one,
      Real.rpow_two] at h
    simpa only [abs_of_neg hneg, neg_neg, mul_neg, neg_mul, mul_comm] using h

/-- The principal branch retains the exact argument factor. -/
theorem norm_principal_power {w : ℂ} (hw : w ≠ 0) (t : ℝ) :
    ‖w ^ (-verticalS t)‖ = ‖w‖ ^ (-2 : ℝ) * Real.exp (t * Complex.arg w) := by
  simp only [Complex.norm_eq_abs]
  rw [Complex.abs_cpow_of_ne_zero hw]
  simp only [Complex.neg_re, verticalS_re, Complex.neg_im, verticalS_im]
  rw [mul_neg, Real.exp_neg, div_inv_eq_mul, mul_comm (Complex.arg w) t]

/-- A fully derived fixed-w envelope on the entire real vertical line. -/
theorem complexGammaKernel_bound {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    ‖complexGammaKernel w t‖ ≤
      kernelCoefficient w * Real.exp (-decayGap w * |t|) := by
  have hn : 0 ≤ ‖w‖ ^ (-2 : ℝ) := Real.rpow_nonneg (norm_nonneg w) _
  have hc : 0 ≤ (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ) := sq_nonneg _
  have hphase : -rotationAngle w * |t| + t * Complex.arg w ≤
      -decayGap w * |t| := by
    have h := le_abs_self (t * Complex.arg w)
    rw [abs_mul] at h
    dsimp only [decayGap]
    nlinarith
  rw [complexGammaKernel, norm_mul, norm_principal_power (rightHalfPlane_ne_zero hw)]
  calc
    _ ≤ ((1 / Real.cos (rotationAngle w)) ^ (2 : ℕ) *
        Real.exp (-rotationAngle w * |t|)) *
        (‖w‖ ^ (-2 : ℝ) * Real.exp (t * Complex.arg w)) :=
      mul_le_mul_of_nonneg_right (norm_Gamma_fixed_rotation hw t)
        (mul_nonneg hn (Real.exp_pos _).le)
    _ = kernelCoefficient w *
        Real.exp (-rotationAngle w * |t| + t * Complex.arg w) := by
      rw [Real.exp_add]
      dsimp only [kernelCoefficient]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (mul_nonneg hn hc)

theorem complexGammaKernel_continuous {w : ℂ} (hw : 0 < w.re) :
    Continuous (complexGammaKernel w) := by
  have hg : Continuous (fun t : ℝ => Complex.Gamma (verticalS t)) := by
    simpa only [GoldbachThermalMellin22.gammaLine, verticalS] using
      GoldbachThermalMellin22.gammaLine_continuous
  exact hg.mul (verticalS_continuous.neg.const_cpow
    (Or.inl (rightHalfPlane_ne_zero hw)))

/-- The actual integrand on either half-line is dominated by a real Laplace kernel. -/
theorem complexGammaKernel_half_integrable {w : ℂ} (hw : 0 < w.re)
    (negative : Bool) :
    IntegrableOn (fun t : ℝ => complexGammaKernel w (if negative then -t else t))
      (Ioi 0) := by
  have hm : IntegrableOn
      (fun t : ℝ => kernelCoefficient w * Real.exp (-decayGap w * t)) (Ioi 0) := by
    have h := (GoldbachContinuous22.real_laplace_integrable
      (a := (1 : ℝ)) (r := decayGap w) (by norm_num) (decayGap_pos hw)).const_mul
        (kernelCoefficient w)
    simpa only [sub_self, Real.rpow_zero, mul_one, neg_mul] using h
  have hsign : Continuous (fun t : ℝ => if negative then -t else t) := by
    cases negative <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  apply hm.mono' ((complexGammaKernel_continuous hw).comp hsign).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : (0 : ℝ) < t := Set.mem_Ioi.mp ht
  have h := complexGammaKernel_bound hw (if negative then -t else t)
  cases negative <;>
    simpa only [Bool.false_eq_true, if_false, if_true, abs_neg, abs_of_pos htpos] using h

/-- Whole-line L1 is built from the two half-lines; no L1 premise is supplied. -/
theorem complexGammaKernel_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (complexGammaKernel w) := by
  have hp : IntegrableOn (complexGammaKernel w) (Ioi 0) := by
    simpa only [Bool.false_eq_true, if_false] using complexGammaKernel_half_integrable hw false
  have hn : IntegrableOn (fun t : ℝ => complexGammaKernel w (-t)) (Ioi 0) := by
    simpa only [if_true] using complexGammaKernel_half_integrable hw true
  have hpre : (fun t : ℝ => -t) ⁻¹' Iio 0 = Ioi 0 := by ext t; simp
  have hn' : IntegrableOn (complexGammaKernel w) (Iio 0) := by
    have ht : IntegrableOn (complexGammaKernel w ∘ (fun t : ℝ => -t))
        ((fun t : ℝ => -t) ⁻¹' Iio 0) := by
      simpa only [hpre, Function.comp_apply] using hn
    exact (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).mp ht
  have hl : IntegrableOn (complexGammaKernel w) (Iic 0) :=
    integrableOn_Iic_iff_integrableOn_Iio.mpr hn'
  have hu : Iic (0 : ℝ) ∪ Ioi 0 = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 0
  have hh := hl.union hp
  rw [hu] at hh
  exact integrableOn_univ.mp hh

/-- The concrete complex derivative of the true kernel, with branch paid. -/
theorem complexGammaKernel_hasDerivAt_w {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    HasDerivAt (fun z : ℂ => complexGammaKernel z t)
      ((-verticalS t) * complexGammaKernel w t / w) w := by
  have hp : HasDerivAt (fun z : ℂ => z ^ (-verticalS t))
      ((-verticalS t) * w ^ (-verticalS t - 1)) w := by
    simpa only [mul_one] using
      (hasDerivAt_id w).cpow_const (c := -verticalS t) (rightHalfPlane_mem_slitPlane hw)
  have h := hp.const_mul (Complex.Gamma (verticalS t))
  have he : w ^ (-verticalS t - 1) = w ^ (-verticalS t) / w := by
    rw [Complex.cpow_sub _ _ (rightHalfPlane_ne_zero hw), Complex.cpow_one]
  rw [he] at h
  simpa only [complexGammaKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- Agreement on positive real rates uses the actual independently checked inversion20. -/
theorem complexGammaInverse_real {x : ℝ} (hx : 0 < x) :
    complexGammaInverse (x : ℂ) = Complex.exp (-(x : ℂ)) := by
  simpa only [complexGammaInverse, complexGammaKernel, verticalS,
    Complex.ofReal_exp, Complex.ofReal_neg] using
    (GoldbachThermalMellin22.real_exp_eq_Gamma_integral hx).symm

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.verticalS
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel
#print axioms GoldbachComplexGammaMellin22.rotationAngle
#print axioms GoldbachComplexGammaMellin22.decayGap
#print axioms GoldbachComplexGammaMellin22.kernelCoefficient
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse
#print axioms GoldbachComplexGammaMellin22.verticalS_re
#print axioms GoldbachComplexGammaMellin22.verticalS_im
#print axioms GoldbachComplexGammaMellin22.verticalS_continuous
#print axioms GoldbachComplexGammaMellin22.rightHalfPlane_mem_slitPlane
#print axioms GoldbachComplexGammaMellin22.rightHalfPlane_ne_zero
#print axioms GoldbachComplexGammaMellin22.rotationAngle_pos
#print axioms GoldbachComplexGammaMellin22.rotationAngle_lt_pi_half
#print axioms GoldbachComplexGammaMellin22.decayGap_pos
#print axioms GoldbachComplexGammaMellin22.norm_Gamma_fixed_rotation
#print axioms GoldbachComplexGammaMellin22.norm_principal_power
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel_bound
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel_continuous
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel_half_integrable
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel_integrable
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel_hasDerivAt_w
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse_real
