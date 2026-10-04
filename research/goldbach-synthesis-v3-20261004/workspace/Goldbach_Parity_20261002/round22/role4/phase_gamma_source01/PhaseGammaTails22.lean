import PhaseGammaSharp22
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! SOURCE ONLY. Closed Gamma-only vertical tails for both signs. The real
kernels are integrated through explicit primitives with nonnegative
derivatives and limits proved from polynomial-exponential decay. The actual
complex Gamma products are continuous and dominated by these kernels.
No zeta factor, final spectral trace or D_N bound is asserted here. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace GoldbachContinuous22

def phaseExpTail (delta T : ℝ) : ℝ := Real.exp (-delta * T) / delta

def phaseQuadTail (delta T : ℝ) : ℝ :=
  Real.exp (-delta * T) *
    ((T + 2) ^ 2 / delta + 2 * (T + 2) / delta ^ 2 + 2 / delta ^ 3)

def phaseTailSign (negative : Bool) (t : ℝ) : ℝ := if negative then -t else t

def phaseClosedLeftTail (a theta T : ℝ) : ℝ :=
  ‖phaseW a theta‖ ^ (1 / 2 : ℝ) * phaseGammaConstant * phaseExpTail (phaseGap a theta) T

def phaseClosedRightTail (a theta T : ℝ) : ℝ :=
  ‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * phaseGammaConstant * phaseQuadTail (phaseGap a theta) T

theorem phaseTailSign_abs (negative : Bool) (t : ℝ) : |phaseTailSign negative t| = |t| := by
  cases negative <;> simp [phaseTailSign]

theorem phaseExpTail_primitive_deriv {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    HasDerivAt (fun x : ℝ => -phaseExpTail delta x) (Real.exp (-delta * t)) t := by
  have h := ((((hasDerivAt_id t).const_mul (-delta)).exp).div_const delta).neg
  change HasDerivAt (fun x : ℝ => -(Real.exp (-delta * x) / delta)) _ t
  convert h using 1 <;> field_simp [hd.ne'] <;> ring

theorem phaseQuadTail_primitive_deriv {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    HasDerivAt (fun x : ℝ => -phaseQuadTail delta x)
      ((t + 2) ^ 2 * Real.exp (-delta * t)) t := by
  have hx := (hasDerivAt_id t).add_const (2 : ℝ)
  have hp := (((hx.pow 2).div_const delta).add
    ((hx.const_mul 2).div_const (delta ^ 2))).add
      (hasDerivAt_const t (2 / delta ^ 3))
  have he := ((hasDerivAt_id t).const_mul (-delta)).exp
  have h := (he.mul hp).neg
  change HasDerivAt (fun x : ℝ => -(Real.exp (-delta * x) *
    ((x + 2) ^ 2 / delta + 2 * (x + 2) / delta ^ 2 + 2 / delta ^ 3))) _ t
  convert h using 1 <;> simp only [Nat.cast_ofNat, pow_one, zero_add, add_zero] <;>
    field_simp [hd.ne'] <;> ring

theorem phaseExpTail_primitive_limit {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun t : ℝ => -phaseExpTail delta t) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hd)
  simpa only [phaseExpTail, Function.comp_apply, neg_mul, zero_div, neg_zero] using
    (h.div_const delta).neg

theorem phaseQuadTail_primitive_limit {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun t : ℝ => -phaseQuadTail delta t) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) delta hd
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) delta hd
  have h2 : Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) delta hd
  have h := (((h2.div_const delta).add
    (h1.const_mul (4 / delta + 2 / delta ^ 2))).add
      (h0.const_mul (4 / delta + 4 / delta ^ 2 + 2 / delta ^ 3))).neg
  have heq : (fun t : ℝ => -phaseQuadTail delta t) =
      (fun t : ℝ => -((t ^ 2 * Real.exp (-delta * t)) / delta +
        (4 / delta + 2 / delta ^ 2) * (t * Real.exp (-delta * t)) +
        (4 / delta + 4 / delta ^ 2 + 2 / delta ^ 3) * Real.exp (-delta * t))) := by
    funext t
    unfold phaseQuadTail
    ring
  rw [heq]
  simpa only [zero_div, mul_zero, zero_add, neg_zero] using h

theorem integrable_phaseExpKernel {delta : ℝ} (hd : 0 < delta) (T : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-delta * t)) (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := T)
    (fun t ht => phaseExpTail_primitive_deriv hd t)
    (fun t ht => (Real.exp_pos _).le) (phaseExpTail_primitive_limit hd)

theorem integral_phaseExpKernel {delta : ℝ} (hd : 0 < delta) (T : ℝ) :
    (∫ t : ℝ in Ioi T, Real.exp (-delta * t)) = phaseExpTail delta T := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := T)
    (fun t ht => phaseExpTail_primitive_deriv hd t)
    (fun t ht => (Real.exp_pos _).le) (phaseExpTail_primitive_limit hd)
  simpa only [zero_sub, neg_neg] using h

theorem integrable_phaseQuadKernel {delta : ℝ} (hd : 0 < delta) (T : ℝ) :
    IntegrableOn (fun t : ℝ => (t + 2) ^ 2 * Real.exp (-delta * t)) (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := T)
    (fun t ht => phaseQuadTail_primitive_deriv hd t)
    (fun t ht => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (phaseQuadTail_primitive_limit hd)

theorem integral_phaseQuadKernel {delta : ℝ} (hd : 0 < delta) (T : ℝ) :
    (∫ t : ℝ in Ioi T, (t + 2) ^ 2 * Real.exp (-delta * t)) = phaseQuadTail delta T := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := T)
    (fun t ht => phaseQuadTail_primitive_deriv hd t)
    (fun t ht => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (phaseQuadTail_primitive_limit hd)
  simpa only [zero_sub, neg_neg] using h

/-- Positive real parts pay continuity of the true Gamma factor. -/
theorem phase_continuous_Gamma_of_re_pos {u : ℝ → ℂ} (hu : Continuous u)
    (hre : ∀ t : ℝ, 0 < (u t).re) : Continuous (fun t : ℝ => Complex.Gamma (u t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hg := (Complex.differentiableAt_Gamma (u t) (fun n => by
    intro hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hpos := hre t
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith)).continuousAt
  exact hg.comp hu.continuousAt

theorem phaseGammaLeft_continuous {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Continuous (phaseGammaLeft a theta) := by
  have harg : Continuous (fun t : ℝ => -((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
  have hg : Continuous (fun t : ℝ => Complex.Gamma (phaseHalf t)) :=
    phase_continuous_Gamma_of_re_pos (by unfold phaseHalf; fun_prop)
      (by intro t; norm_num [phaseHalf])
  exact (harg.const_cpow (Or.inl (phaseW_ne_zero ha theta))).mul hg

theorem phaseGammaRight_continuous {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Continuous (phaseGammaRight a theta) := by
  have harg : Continuous (fun t : ℝ => -((3 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
  have hg : Continuous (fun t : ℝ => Complex.Gamma (phaseFiveHalf t)) :=
    phase_continuous_Gamma_of_re_pos (by unfold phaseFiveHalf; fun_prop)
      (by intro t; norm_num [phaseFiveHalf])
  exact (harg.const_cpow (Or.inl (phaseW_ne_zero ha theta))).mul hg

theorem norm_phaseGammaLeft_signed_le {a : ℝ} (ha : 0 < a) (theta t : ℝ)
    (ht : 0 ≤ t) (negative : Bool) :
    ‖phaseGammaLeft a theta (phaseTailSign negative t)‖ ≤
      (‖phaseW a theta‖ ^ (1 / 2 : ℝ) * phaseGammaConstant) *
        Real.exp (-phaseGap a theta * t) := by
  simpa only [phaseGammaLeftEnvelope, phaseTailSign_abs, abs_of_nonneg ht] using
    norm_phaseGammaLeft_le ha theta (phaseTailSign negative t)

theorem norm_phaseGammaRight_signed_le {a : ℝ} (ha : 0 < a) (theta t : ℝ)
    (ht : 0 ≤ t) (negative : Bool) :
    ‖phaseGammaRight a theta (phaseTailSign negative t)‖ ≤
      (‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * phaseGammaConstant) *
        ((t + 2) ^ 2 * Real.exp (-phaseGap a theta * t)) := by
  simpa only [phaseGammaRightEnvelope, phaseTailSign_abs, abs_of_nonneg ht, mul_assoc] using
    norm_phaseGammaRight_le ha theta (phaseTailSign negative t)

theorem integrable_phaseGammaLeft_tail {a : ℝ} (ha : 0 < a) (theta T : ℝ)
    (hT : 0 ≤ T) (negative : Bool) :
    IntegrableOn (fun t : ℝ => phaseGammaLeft a theta (phaseTailSign negative t)) (Ioi T) := by
  have hmaj := (integrable_phaseExpKernel (phaseGap_pos ha theta) T).const_mul
    (‖phaseW a theta‖ ^ (1 / 2 : ℝ) * phaseGammaConstant)
  have hs : Continuous (phaseTailSign negative) := by cases negative <;> dsimp [phaseTailSign] <;> fun_prop
  apply hmaj.mono' ((phaseGammaLeft_continuous ha theta).comp hs).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_phaseGammaLeft_signed_le ha theta t (hT.trans ht.le) negative

theorem integrable_phaseGammaRight_tail {a : ℝ} (ha : 0 < a) (theta T : ℝ)
    (hT : 0 ≤ T) (negative : Bool) :
    IntegrableOn (fun t : ℝ => phaseGammaRight a theta (phaseTailSign negative t)) (Ioi T) := by
  have hmaj := (integrable_phaseQuadKernel (phaseGap_pos ha theta) T).const_mul
    (‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * phaseGammaConstant)
  have hs : Continuous (phaseTailSign negative) := by cases negative <;> dsimp [phaseTailSign] <;> fun_prop
  apply hmaj.mono' ((phaseGammaRight_continuous ha theta).comp hs).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_phaseGammaRight_signed_le ha theta t (hT.trans ht.le) negative

theorem norm_integral_phaseGammaLeft_tail_le {a : ℝ} (ha : 0 < a) (theta T : ℝ)
    (hT : 0 ≤ T) (negative : Bool) :
    ‖∫ t : ℝ in Ioi T, phaseGammaLeft a theta (phaseTailSign negative t)‖ ≤
      phaseClosedLeftTail a theta T := by
  have hmaj := (integrable_phaseExpKernel (phaseGap_pos ha theta) T).const_mul
    (‖phaseW a theta‖ ^ (1 / 2 : ℝ) * phaseGammaConstant)
  have h := norm_integral_le_of_norm_le hmaj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_phaseGammaLeft_signed_le ha theta t (hT.trans ht.le) negative)
  rw [integral_mul_left, integral_phaseExpKernel (phaseGap_pos ha theta)] at h
  exact h

theorem norm_integral_phaseGammaRight_tail_le {a : ℝ} (ha : 0 < a) (theta T : ℝ)
    (hT : 0 ≤ T) (negative : Bool) :
    ‖∫ t : ℝ in Ioi T, phaseGammaRight a theta (phaseTailSign negative t)‖ ≤
      phaseClosedRightTail a theta T := by
  have hmaj := (integrable_phaseQuadKernel (phaseGap_pos ha theta) T).const_mul
    (‖phaseW a theta‖ ^ (-3 / 2 : ℝ) * phaseGammaConstant)
  have h := norm_integral_le_of_norm_le hmaj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_phaseGammaRight_signed_le ha theta t (hT.trans ht.le) negative)
  rw [integral_mul_left, integral_phaseQuadKernel (phaseGap_pos ha theta)] at h
  exact h

theorem phaseClosedLeftTail_continuousOn (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => phaseClosedLeftTail p.1 p.2 T) {p | 0 < p.1} := by
  intro p hp
  have hw : Continuous (fun q : ℝ × ℝ => phaseW q.1 q.2) := by unfold phaseW; fun_prop
  have hn := hw.norm.continuousAt
  have hn0 : ‖phaseW p.1 p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (phaseW_ne_zero hp p.2)
  have hpow := hn.rpow_const (Or.inl hn0) (p := (1 / 2 : ℝ))
  have hd := phaseGap_continuousAt hp
  have he : ContinuousAt (fun q : ℝ × ℝ => Real.exp (-phaseGap q.1 q.2 * T)) p :=
    (hd.neg.mul (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => T) p)).rexp
  have htail : ContinuousAt (fun q : ℝ × ℝ => phaseExpTail (phaseGap q.1 q.2) T) p :=
    he.div hd (phaseGap_pos hp p.2).ne'
  exact ((hpow.mul continuousAt_const).mul htail).continuousWithinAt

theorem phaseClosedRightTail_continuousOn (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => phaseClosedRightTail p.1 p.2 T) {p | 0 < p.1} := by
  intro p hp
  have hw : Continuous (fun q : ℝ × ℝ => phaseW q.1 q.2) := by unfold phaseW; fun_prop
  have hn := hw.norm.continuousAt
  have hn0 : ‖phaseW p.1 p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (phaseW_ne_zero hp p.2)
  have hpow := hn.rpow_const (Or.inl hn0) (p := (-3 / 2 : ℝ))
  have hd := phaseGap_continuousAt hp
  have he : ContinuousAt (fun q : ℝ × ℝ => Real.exp (-phaseGap q.1 q.2 * T)) p :=
    (hd.neg.mul (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => T) p)).rexp
  have hd0 := (phaseGap_pos hp p.2).ne'
  have hpoly : ContinuousAt (fun q : ℝ × ℝ =>
      (T + 2) ^ 2 / phaseGap q.1 q.2 +
        2 * (T + 2) / phaseGap q.1 q.2 ^ 2 + 2 / phaseGap q.1 q.2 ^ 3) p :=
    ((continuousAt_const.div hd hd0).add
      (continuousAt_const.div (hd.pow 2) (pow_ne_zero 2 hd0))).add
        (continuousAt_const.div (hd.pow 3) (pow_ne_zero 3 hd0))
  have htail : ContinuousAt (fun q : ℝ × ℝ => phaseQuadTail (phaseGap q.1 q.2) T) p :=
    he.mul hpoly
  exact ((hpow.mul continuousAt_const).mul htail).continuousWithinAt

end GoldbachContinuous22

#print axioms GoldbachContinuous22.phaseExpTail
#print axioms GoldbachContinuous22.phaseQuadTail
#print axioms GoldbachContinuous22.phaseTailSign
#print axioms GoldbachContinuous22.phaseClosedLeftTail
#print axioms GoldbachContinuous22.phaseClosedRightTail
#print axioms GoldbachContinuous22.phaseTailSign_abs
#print axioms GoldbachContinuous22.phaseExpTail_primitive_deriv
#print axioms GoldbachContinuous22.phaseQuadTail_primitive_deriv
#print axioms GoldbachContinuous22.phaseExpTail_primitive_limit
#print axioms GoldbachContinuous22.phaseQuadTail_primitive_limit
#print axioms GoldbachContinuous22.integrable_phaseExpKernel
#print axioms GoldbachContinuous22.integral_phaseExpKernel
#print axioms GoldbachContinuous22.integrable_phaseQuadKernel
#print axioms GoldbachContinuous22.integral_phaseQuadKernel
#print axioms GoldbachContinuous22.phase_continuous_Gamma_of_re_pos
#print axioms GoldbachContinuous22.phaseGammaLeft_continuous
#print axioms GoldbachContinuous22.phaseGammaRight_continuous
#print axioms GoldbachContinuous22.norm_phaseGammaLeft_signed_le
#print axioms GoldbachContinuous22.norm_phaseGammaRight_signed_le
#print axioms GoldbachContinuous22.integrable_phaseGammaLeft_tail
#print axioms GoldbachContinuous22.integrable_phaseGammaRight_tail
#print axioms GoldbachContinuous22.norm_integral_phaseGammaLeft_tail_le
#print axioms GoldbachContinuous22.norm_integral_phaseGammaRight_tail_le
#print axioms GoldbachContinuous22.phaseClosedLeftTail_continuousOn
#print axioms GoldbachContinuous22.phaseClosedRightTail_continuousOn


