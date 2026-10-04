import ComplexGammaMellinLocal22
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! SOURCE ONLY. No compiler, tactic probe or numerical evaluator has been run.
This module constructs a neighborhood and an integrable derivative majorant for
the true Gamma/cpow kernel. Analytic continuation then uses the real Mellin
identity independently checked in batch20. It supplies no final L1, derivative,
holomorphy or inversion premise. It makes no zeta/Lambda exchange or D_N claim.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace GoldbachComplexGammaMellin22

def localArgRadius (w : ℂ) : ℝ :=
  (rotationAngle w + |Complex.arg w|) / 2

def localDecayGap (w : ℂ) : ℝ := rotationAngle w - localArgRadius w

def localDerivativeCoefficient (w : ℂ) : ℝ :=
  ((‖w‖ / 2) ^ (-2 : ℝ) *
    (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) / (‖w‖ / 2)

def localDerivativeEnvelope (w : ℂ) (t : ℝ) : ℝ :=
  localDerivativeCoefficient w * (2 + |t|) *
    Real.exp (-localDecayGap w * |t|)

theorem local_parameters {w : ℂ} (hw : 0 < w.re) :
    0 < ‖w‖ / 2 ∧ |Complex.arg w| < localArgRadius w ∧
      localArgRadius w < rotationAngle w ∧ 0 < localDecayGap w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr (rightHalfPlane_ne_zero hw)
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · dsimp only [localArgRadius, rotationAngle]
    linarith
  · dsimp only [localArgRadius, rotationAngle]
    linarith
  · dsimp only [localDecayGap, localArgRadius, rotationAngle]
    linarith

/-- Re, norm and the principal argument are controlled on one actual ball. -/
theorem exists_local_kernel_ball {w : ℂ} (hw : 0 < w.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball w ε,
      0 < z.re ∧ ‖w‖ / 2 ≤ ‖z‖ ∧ |Complex.arg z| ≤ localArgRadius w := by
  have hp := local_parameters hw
  have hre : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hw
  have hn : ∀ᶠ z : ℂ in 𝓝 w, ‖w‖ / 2 < ‖z‖ :=
    continuousAt_const.eventually_lt continuous_norm.continuousAt (by linarith [hp.1])
  have harg : ∀ᶠ z : ℂ in 𝓝 w, |Complex.arg z| < localArgRadius w :=
    (Complex.continuousAt_arg (rightHalfPlane_mem_slitPlane hw)).abs.eventually_lt
      continuousAt_const hp.2.1
  apply Metric.eventually_nhds_iff_ball.mp
  filter_upwards [hre, hn, harg] with z hz hnz haz
  exact ⟨hz, hnz.le, haz.le⟩

theorem verticalS_norm_le (t : ℝ) : ‖verticalS t‖ ≤ 2 + |t| := by
  calc
    ‖verticalS t‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = 2 + |t| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num

/-- One fixed rotation at the center controls all rates in its ball. -/
theorem complexGammaKernel_local_bound {w z : ℂ} (hw : 0 < w.re)
    (hz : 0 < z.re) (hn : ‖w‖ / 2 ≤ ‖z‖)
    (ha : |Complex.arg z| ≤ localArgRadius w) (t : ℝ) :
    ‖complexGammaKernel z t‖ ≤
      ((‖w‖ / 2) ^ (-2 : ℝ) *
        (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
        Real.exp (-localDecayGap w * |t|) := by
  have hm : 0 < ‖w‖ / 2 := (local_parameters hw).1
  have hpow : ‖z‖ ^ (-2 : ℝ) ≤ (‖w‖ / 2) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_nonpos hm hn (by norm_num)
  have hphase : -rotationAngle w * |t| + t * Complex.arg z ≤
      -localDecayGap w * |t| := by
    have hprod : t * Complex.arg z ≤ |t| * localArgRadius w :=
      (le_abs_self (t * Complex.arg z)).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ha (abs_nonneg t))
    dsimp only [localDecayGap]
    linarith
  have hc : 0 ≤ (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ) := sq_nonneg _
  have hm2 : 0 ≤ (‖w‖ / 2) ^ (-2 : ℝ) := Real.rpow_nonneg hm.le _
  rw [complexGammaKernel, norm_mul, norm_principal_power (rightHalfPlane_ne_zero hz)]
  calc
    _ ≤ ((1 / Real.cos (rotationAngle w)) ^ (2 : ℕ) *
        Real.exp (-rotationAngle w * |t|)) *
        ((‖w‖ / 2) ^ (-2 : ℝ) * Real.exp (t * Complex.arg z)) := by
      apply mul_le_mul (norm_Gamma_fixed_rotation hw t)
        (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le)
      · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _) (Real.exp_pos _).le
      · exact mul_nonneg hc (Real.exp_pos _).le
    _ = ((‖w‖ / 2) ^ (-2 : ℝ) *
        (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
        Real.exp (-rotationAngle w * |t| + t * Complex.arg z) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (mul_nonneg hm2 hc)

/-- This is the actual complex derivative, bounded by a named local envelope. -/
theorem complexGammaDerivative_local_bound {w z : ℂ} (hw : 0 < w.re)
    (hz : 0 < z.re) (hn : ‖w‖ / 2 ≤ ‖z‖)
    (ha : |Complex.arg z| ≤ localArgRadius w) (t : ℝ) :
    ‖(-verticalS t) * complexGammaKernel z t / z‖ ≤ localDerivativeEnvelope w t := by
  have hm : 0 < ‖w‖ / 2 := (local_parameters hw).1
  have hi : ‖z‖⁻¹ ≤ (‖w‖ / 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hm hn
  have hc : 0 ≤ (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ) := sq_nonneg _
  have hm2 : 0 ≤ (‖w‖ / 2) ^ (-2 : ℝ) := Real.rpow_nonneg hm.le _
  have hnum : ‖verticalS t‖ * ‖complexGammaKernel z t‖ ≤
      (2 + |t|) * (((‖w‖ / 2) ^ (-2 : ℝ) *
        (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
        Real.exp (-localDecayGap w * |t|)) :=
    mul_le_mul (verticalS_norm_le t) (complexGammaKernel_local_bound hw hz hn ha t)
      (norm_nonneg _) (by positivity)
  rw [norm_div, norm_mul, norm_neg, div_eq_mul_inv]
  calc
    _ ≤ ((2 + |t|) * (((‖w‖ / 2) ^ (-2 : ℝ) *
        (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
        Real.exp (-localDecayGap w * |t|))) * (‖w‖ / 2)⁻¹ :=
      mul_le_mul hnum hi (inv_nonneg.mpr (norm_nonneg z))
        (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hm2 hc) (Real.exp_pos _).le))
    _ = localDerivativeEnvelope w t := by
      dsimp only [localDerivativeEnvelope, localDerivativeCoefficient]
      rw [div_eq_mul_inv]
      ring

/-- Both Laplace moments are integrable; the negative half-line is transported. -/
theorem weightedExponential_integrable {d : ℝ} (hd : 0 < d) (C : ℝ) :
    Integrable (fun t : ℝ => C * (2 + |t|) * Real.exp (-d * |t|)) := by
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-d * t)) (Ioi 0) := by
    simpa only [sub_self, Real.rpow_zero, mul_one, neg_mul] using
      GoldbachContinuous22.real_laplace_integrable (a := 1) (by norm_num) hd
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-d * t)) (Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, neg_mul, mul_comm] using
      GoldbachContinuous22.real_laplace_integrable (a := 2) (by norm_num) hd
  have hp : IntegrableOn
      (fun t : ℝ => C * (2 + |t|) * Real.exp (-d * |t|)) (Ioi 0) := by
    apply (((h0.const_mul 2).add h1).const_mul C).congr
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with t ht
    rw [abs_of_pos ht]
    ring
  have hpre : (fun t : ℝ => -t) ⁻¹' Iio 0 = Ioi 0 := by ext t; simp
  have hn : IntegrableOn
      (fun t : ℝ => C * (2 + |t|) * Real.exp (-d * |t|)) (Iio 0) := by
    have hcomp : IntegrableOn
        ((fun t : ℝ => C * (2 + |t|) * Real.exp (-d * |t|)) ∘ (fun t : ℝ => -t))
        ((fun t : ℝ => -t) ⁻¹' Iio 0) := by
      simpa only [hpre, Function.comp_apply, abs_neg] using hp
    exact (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).mp hcomp
  have hl : IntegrableOn
      (fun t : ℝ => C * (2 + |t|) * Real.exp (-d * |t|)) (Iic 0) :=
    integrableOn_Iic_iff_integrableOn_Iio.mpr hn
  have hu : Iic (0 : ℝ) ∪ Ioi 0 = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 0
  have hi := hl.union hp
  rw [hu] at hi
  exact integrableOn_univ.mp hi

theorem localDerivativeEnvelope_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (localDerivativeEnvelope w) := by
  exact weightedExponential_integrable (local_parameters hw).2.2.2
    (localDerivativeCoefficient w)

/-- All hypotheses of parameter differentiation are constructed in this proof. -/
theorem complexGammaInverse_hasDerivAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt complexGammaInverse
      ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ t : ℝ, (-verticalS t) * complexGammaKernel w t / w) w := by
  obtain ⟨ε, hε, hb⟩ := exists_local_kernel_ball hw
  have hmeas : ∀ᶠ z : ℂ in 𝓝 w, AEStronglyMeasurable (complexGammaKernel z) := by
    have hre : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re :=
      continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hw
    filter_upwards [hre] with z hz
    exact (complexGammaKernel_continuous hz).aestronglyMeasurable
  have hdcont : Continuous (fun t : ℝ => (-verticalS t) * complexGammaKernel w t / w) :=
    (verticalS_continuous.neg.mul (complexGammaKernel_continuous hw)).div_const w
  have hbound : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball w ε,
      ‖(-verticalS t) * complexGammaKernel z t / z‖ ≤ localDerivativeEnvelope w t := by
    filter_upwards with t
    intro z hz
    obtain ⟨hz0, hn, ha⟩ := hb z hz
    exact complexGammaDerivative_local_bound hw hz0 hn ha t
  have hdiff : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball w ε,
      HasDerivAt (fun v : ℂ => complexGammaKernel v t)
        ((-verticalS t) * complexGammaKernel z t / z) z := by
    filter_upwards with t
    intro z hz
    exact complexGammaKernel_hasDerivAt_w (hb z hz).1 t
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := complexGammaKernel)
    (F' := fun z t => (-verticalS t) * complexGammaKernel z t / z)
    (bound := localDerivativeEnvelope w) hε hmeas (complexGammaKernel_integrable hw)
    hdcont.aestronglyMeasurable hbound (localDerivativeEnvelope_integrable hw) hdiff).2
  simpa only [complexGammaInverse] using hi.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem complexGammaInverse_analytic :
    AnalyticOnNhd ℂ complexGammaInverse GoldbachContinuous22.rightHalfPlane := by
  apply DifferentiableOn.analyticOnNhd _ GoldbachContinuous22.rightHalfPlane_isOpen
  intro w hw
  exact (complexGammaInverse_hasDerivAt hw).differentiableAt.differentiableWithinAt

/-- The real agreement set accumulates at one inside the connected half-plane. -/
theorem complexGammaInverse_eq_exp {w : ℂ} (hw : 0 < w.re) :
    complexGammaInverse w = Complex.exp (-w) := by
  have hexp : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-z))
      GoldbachContinuous22.rightHalfPlane := by
    apply DifferentiableOn.analyticOnNhd _ GoldbachContinuous22.rightHalfPlane_isOpen
    intro z _
    exact ((hasDerivAt_id z).neg.cexp).differentiableAt.differentiableWithinAt
  let rates : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hrates : Tendsto rates atTop (𝓝 1) := by
    simpa only [rates, add_zero] using
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomplex : Tendsto (fun n : ℕ => (rates n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using Complex.continuous_ofReal.tendsto 1 |>.comp hrates
  have hclosure : (1 : ℂ) ∈ closure
      ({z : ℂ | complexGammaInverse z = Complex.exp (-z)} \ {(1 : ℂ)}) := by
    apply mem_closure_of_tendsto hcomplex
    apply Eventually.of_forall
    intro n
    have hpos : 0 < rates n := by dsimp [rates]; positivity
    have hgt : 1 < rates n := by
      dsimp only [rates]
      exact lt_add_of_pos_right 1 (by positivity)
    constructor
    · exact complexGammaInverse_real hpos
    · simp only [mem_singleton_iff, Complex.ofReal_eq_one]
      exact ne_of_gt hgt
  exact complexGammaInverse_analytic.eqOn_of_preconnected_of_mem_closure hexp
    GoldbachContinuous22.rightHalfPlane_isPreconnected
    (by simp [GoldbachContinuous22.rightHalfPlane]) hclosure hw

theorem complex_exp_eq_Gamma_integral {w : ℂ} (hw : 0 < w.re) :
    Complex.exp (-w) = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      ∫ t : ℝ, Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
        w ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa only [complexGammaInverse, complexGammaKernel, verticalS] using
    (complexGammaInverse_eq_exp hw).symm

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.localArgRadius
#print axioms GoldbachComplexGammaMellin22.localDecayGap
#print axioms GoldbachComplexGammaMellin22.localDerivativeCoefficient
#print axioms GoldbachComplexGammaMellin22.localDerivativeEnvelope
#print axioms GoldbachComplexGammaMellin22.local_parameters
#print axioms GoldbachComplexGammaMellin22.exists_local_kernel_ball
#print axioms GoldbachComplexGammaMellin22.verticalS_norm_le
#print axioms GoldbachComplexGammaMellin22.complexGammaKernel_local_bound
#print axioms GoldbachComplexGammaMellin22.complexGammaDerivative_local_bound
#print axioms GoldbachComplexGammaMellin22.weightedExponential_integrable
#print axioms GoldbachComplexGammaMellin22.localDerivativeEnvelope_integrable
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse_hasDerivAt
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse_analytic
#print axioms GoldbachComplexGammaMellin22.complexGammaInverse_eq_exp
#print axioms GoldbachComplexGammaMellin22.complex_exp_eq_Gamma_integral
