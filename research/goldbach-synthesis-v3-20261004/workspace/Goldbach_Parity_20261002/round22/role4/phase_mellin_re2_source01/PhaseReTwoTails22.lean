import PhaseZetaReTwo22
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! SOURCE ONLY. Actual Gamma * (-zeta'/zeta) * principal-power tails.
The constant four is imported from a derived Euler SOURCE theorem, never
provided as a premise. This is not the Mellin representation of T(w). -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def reTwoF (a theta t : ℝ) : ℂ :=
  Complex.Gamma (reTwoS t) * reTwoLogDeriv t * reTwoW a theta ^ (-reTwoS t)

def reTwoKernelTail (delta H : ℝ) : ℝ :=
  Real.exp (-delta * H) * ((H ^ 2 + 4) / delta + 2 * H / delta ^ 2 + 2 / delta ^ 3)

def reTwoTailSign (negative : Bool) (t : ℝ) : ℝ := if negative then -t else t

def reTwoClosedTail (a theta H : ℝ) : ℝ :=
  Real.exp 2 * ‖reTwoW a theta‖ ^ (-2 : ℝ) * reTwoKernelTail (reTwoGap a theta) H

/-- Two signed tails and normalization 1/(2*pi) give this closed expression. -/
def reTwoNormalizedTail (a theta H : ℝ) : ℝ := reTwoClosedTail a theta H / Real.pi

theorem norm_reTwoF_le {a : ℝ} (ha : 0 < a) (theta t : ℝ) :
    ‖reTwoF a theta t‖ ≤
      Real.exp 2 * ‖reTwoW a theta‖ ^ (-2 : ℝ) * (t ^ 2 + 4) *
        Real.exp (-reTwoGap a theta * |t|) := by
  have hg := norm_Gamma_reTwo_le t
  have hl := norm_reTwoLogDeriv_le_four t
  have hp := Real.rpow_nonneg (norm_nonneg (reTwoW a theta)) (-2 : ℝ)
  have hexp : Real.exp (2 - Real.pi * |t| / 2) *
      Real.exp (t * Complex.arg (reTwoW a theta)) =
      Real.exp 2 * Real.exp (-Real.pi * |t| / 2 + t * Complex.arg (reTwoW a theta)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [reTwoF, norm_mul, norm_mul, norm_reTwo_principal_power (reTwoW_ne_zero ha theta)]
  calc
    _ ≤ (((t ^ 2 + 4) / 4 * Real.exp (2 - Real.pi * |t| / 2)) * 4) *
        (‖reTwoW a theta‖ ^ (-2 : ℝ) * Real.exp (t * Complex.arg (reTwoW a theta))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hg hl (norm_nonneg _) (by positivity))
        (mul_nonneg hp (Real.exp_pos _).le)
    _ = ‖reTwoW a theta‖ ^ (-2 : ℝ) * (t ^ 2 + 4) *
        (Real.exp (2 - Real.pi * |t| / 2) * Real.exp (t * Complex.arg (reTwoW a theta))) := by
      ring
    _ = Real.exp 2 * ‖reTwoW a theta‖ ^ (-2 : ℝ) * (t ^ 2 + 4) *
        Real.exp (-Real.pi * |t| / 2 + t * Complex.arg (reTwoW a theta)) := by
      rw [hexp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (reTwo_exponent_le_gap a theta t))
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hp) (by positivity))

theorem reTwoKernelTail_primitive_deriv {delta : ℝ} (hd : 0 < delta) (t : ℝ) :
    HasDerivAt (fun x : ℝ => -reTwoKernelTail delta x)
      ((t ^ 2 + 4) * Real.exp (-delta * t)) t := by
  have hx := hasDerivAt_id t
  have hp := ((((hx.pow 2).add_const 4).div_const delta).add
    ((hx.const_mul 2).div_const (delta ^ 2))).add (hasDerivAt_const t (2 / delta ^ 3))
  have he := (hx.const_mul (-delta)).exp
  have h := (he.mul hp).neg
  change HasDerivAt (fun x : ℝ => -(Real.exp (-delta * x) *
    ((x ^ 2 + 4) / delta + 2 * x / delta ^ 2 + 2 / delta ^ 3))) _ t
  convert h using 1 <;> simp only [Nat.cast_ofNat, pow_one, zero_add, add_zero] <;>
    field_simp [hd.ne'] <;> ring

theorem reTwoKernelTail_primitive_limit {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun t : ℝ => -reTwoKernelTail delta t) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) delta hd
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) delta hd
  have h2 : Tendsto (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) delta hd
  have h := (((h2.div_const delta).add (h1.const_mul (2 / delta ^ 2))).add
    (h0.const_mul (4 / delta + 2 / delta ^ 3))).neg
  have heq : (fun t : ℝ => -reTwoKernelTail delta t) =
      (fun t : ℝ => -((t ^ 2 * Real.exp (-delta * t)) / delta +
        (2 / delta ^ 2) * (t * Real.exp (-delta * t)) +
        (4 / delta + 2 / delta ^ 3) * Real.exp (-delta * t))) := by
    funext t
    unfold reTwoKernelTail
    ring
  rw [heq]
  simpa only [zero_div, mul_zero, zero_add, neg_zero] using h

theorem integrable_reTwoKernel {delta : ℝ} (hd : 0 < delta) (H : ℝ) :
    IntegrableOn (fun t : ℝ => (t ^ 2 + 4) * Real.exp (-delta * t)) (Ioi H) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := H)
    (fun t ht => reTwoKernelTail_primitive_deriv hd t)
    (fun t ht => mul_nonneg (by positivity) (Real.exp_pos _).le)
    (reTwoKernelTail_primitive_limit hd)

theorem integral_reTwoKernel {delta : ℝ} (hd : 0 < delta) (H : ℝ) :
    (∫ t : ℝ in Ioi H, (t ^ 2 + 4) * Real.exp (-delta * t)) = reTwoKernelTail delta H := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := H)
    (fun t ht => reTwoKernelTail_primitive_deriv hd t)
    (fun t ht => mul_nonneg (by positivity) (Real.exp_pos _).le)
    (reTwoKernelTail_primitive_limit hd)
  simpa only [zero_sub, neg_neg] using h

theorem reTwoF_continuous {a : ℝ} (ha : 0 < a) (theta : ℝ) : Continuous (reTwoF a theta) := by
  have he : Continuous (fun t : ℝ => -reTwoS t) := reTwoS_continuous.neg
  exact (Gamma_reTwo_continuous.mul reTwoLogDeriv_continuous).mul
    (he.const_cpow (Or.inl (reTwoW_ne_zero ha theta)))

theorem reTwoTailSign_abs (negative : Bool) (t : ℝ) : |reTwoTailSign negative t| = |t| := by
  cases negative <;> simp [reTwoTailSign]

theorem reTwoTailSign_sq (negative : Bool) (t : ℝ) : reTwoTailSign negative t ^ 2 = t ^ 2 := by
  cases negative <;> simp [reTwoTailSign]

theorem norm_reTwoF_signed_le {a : ℝ} (ha : 0 < a) (theta t : ℝ)
    (ht : 0 ≤ t) (negative : Bool) :
    ‖reTwoF a theta (reTwoTailSign negative t)‖ ≤
      (Real.exp 2 * ‖reTwoW a theta‖ ^ (-2 : ℝ)) *
        ((t ^ 2 + 4) * Real.exp (-reTwoGap a theta * t)) := by
  simpa only [reTwoTailSign_abs, reTwoTailSign_sq, abs_of_nonneg ht, mul_assoc] using
    norm_reTwoF_le ha theta (reTwoTailSign negative t)

theorem integrable_reTwoF_tail {a : ℝ} (ha : 0 < a) (theta H : ℝ)
    (hH : 0 ≤ H) (negative : Bool) :
    IntegrableOn (fun t : ℝ => reTwoF a theta (reTwoTailSign negative t)) (Ioi H) := by
  have hmaj := (integrable_reTwoKernel (reTwoGap_pos ha theta) H).const_mul
    (Real.exp 2 * ‖reTwoW a theta‖ ^ (-2 : ℝ))
  have hs : Continuous (reTwoTailSign negative) := by cases negative <;> dsimp [reTwoTailSign] <;> fun_prop
  apply hmaj.mono' ((reTwoF_continuous ha theta).comp hs).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_reTwoF_signed_le ha theta t (hH.trans ht.le) negative

theorem norm_integral_reTwoF_tail_le {a : ℝ} (ha : 0 < a) (theta H : ℝ)
    (hH : 0 ≤ H) (negative : Bool) :
    ‖∫ t : ℝ in Ioi H, reTwoF a theta (reTwoTailSign negative t)‖ ≤ reTwoClosedTail a theta H := by
  have hmaj := (integrable_reTwoKernel (reTwoGap_pos ha theta) H).const_mul
    (Real.exp 2 * ‖reTwoW a theta‖ ^ (-2 : ℝ))
  have h := norm_integral_le_of_norm_le hmaj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_reTwoF_signed_le ha theta t (hH.trans ht.le) negative)
  rw [integral_mul_left, integral_reTwoKernel (reTwoGap_pos ha theta)] at h
  exact h

theorem norm_reTwo_normalized_signed_tail_sum_le {a : ℝ} (ha : 0 < a) (theta H : ℝ)
    (hH : 0 ≤ H) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t : ℝ in Ioi H, reTwoF a theta (reTwoTailSign false t)) +
        (∫ t : ℝ in Ioi H, reTwoF a theta (reTwoTailSign true t)))‖ ≤
      reTwoNormalizedTail a theta H := by
  have hsum := (norm_add_le
    (∫ t : ℝ in Ioi H, reTwoF a theta (reTwoTailSign false t))
    (∫ t : ℝ in Ioi H, reTwoF a theta (reTwoTailSign true t))).trans
      (add_le_add (norm_integral_reTwoF_tail_le ha theta H hH false)
        (norm_integral_reTwoF_tail_le ha theta H hH true))
  have hcoef : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hcoef]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (reTwoClosedTail a theta H + reTwoClosedTail a theta H) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = reTwoNormalizedTail a theta H := by
      unfold reTwoNormalizedTail
      field_simp [Real.pi_ne_zero]
      ring

theorem reTwoClosedTail_continuousOn (H : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => reTwoClosedTail p.1 p.2 H) {p | 0 < p.1} := by
  intro p hp
  have hw : Continuous (fun q : ℝ × ℝ => reTwoW q.1 q.2) := by unfold reTwoW; fun_prop
  have hn := hw.norm.continuousAt
  have hn0 : ‖reTwoW p.1 p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (reTwoW_ne_zero hp p.2)
  have hpow := hn.rpow_const (Or.inl hn0) (p := (-2 : ℝ))
  have hd := reTwoGap_continuousAt hp
  have hd0 := (reTwoGap_pos hp p.2).ne'
  have he : ContinuousAt (fun q : ℝ × ℝ => Real.exp (-reTwoGap q.1 q.2 * H)) p :=
    (hd.neg.mul (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => H) p)).rexp
  have hpoly : ContinuousAt (fun q : ℝ × ℝ => (H ^ 2 + 4) / reTwoGap q.1 q.2 +
      2 * H / reTwoGap q.1 q.2 ^ 2 + 2 / reTwoGap q.1 q.2 ^ 3) p :=
    ((continuousAt_const.div hd hd0).add
      (continuousAt_const.div (hd.pow 2) (pow_ne_zero 2 hd0))).add
        (continuousAt_const.div (hd.pow 3) (pow_ne_zero 3 hd0))
  have htail : ContinuousAt (fun q : ℝ × ℝ => reTwoKernelTail (reTwoGap q.1 q.2) H) p :=
    he.mul hpoly
  exact ((continuousAt_const.mul hpow).mul htail).continuousWithinAt

theorem reTwoNormalizedTail_continuousOn (H : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => reTwoNormalizedTail p.1 p.2 H) {p | 0 < p.1} :=
  (reTwoClosedTail_continuousOn H).div_const Real.pi

/-- Joint continuity also includes the truncation height, without a hidden fixed H. -/
theorem reTwoClosedTail_joint_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => reTwoClosedTail p.1 p.2.1 p.2.2) {p | 0 < p.1} := by
  intro p hp
  have hw : Continuous (fun q : ℝ × ℝ × ℝ => reTwoW q.1 q.2.1) := by unfold reTwoW; fun_prop
  have hm : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1)) := by fun_prop
  have hH : Continuous (fun q : ℝ × ℝ × ℝ => q.2.2) := by fun_prop
  have hn := hw.norm.continuousAt
  have hn0 : ‖reTwoW p.1 p.2.1‖ ≠ 0 := norm_ne_zero_iff.mpr (reTwoW_ne_zero hp p.2.1)
  have hpow := hn.rpow_const (Or.inl hn0) (p := (-2 : ℝ))
  have hd := (reTwoGap_continuousAt (p := (p.1, p.2.1)) hp).comp hm.continuousAt
  have hd0 := (reTwoGap_pos hp p.2.1).ne'
  have he : ContinuousAt (fun q : ℝ × ℝ × ℝ => Real.exp (-reTwoGap q.1 q.2.1 * q.2.2)) p :=
    (hd.neg.mul hH.continuousAt).rexp
  have hpoly : ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      (q.2.2 ^ 2 + 4) / reTwoGap q.1 q.2.1 +
        2 * q.2.2 / reTwoGap q.1 q.2.1 ^ 2 + 2 / reTwoGap q.1 q.2.1 ^ 3) p :=
    ((((hH.continuousAt.pow 2).add continuousAt_const).div hd hd0).add
      ((continuousAt_const.mul hH.continuousAt).div (hd.pow 2) (pow_ne_zero 2 hd0))).add
        (continuousAt_const.div (hd.pow 3) (pow_ne_zero 3 hd0))
  have htail : ContinuousAt (fun q : ℝ × ℝ × ℝ => reTwoKernelTail (reTwoGap q.1 q.2.1) q.2.2) p :=
    he.mul hpoly
  exact ((continuousAt_const.mul hpow).mul htail).continuousWithinAt

theorem reTwoNormalizedTail_joint_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => reTwoNormalizedTail p.1 p.2.1 p.2.2) {p | 0 < p.1} :=
  reTwoClosedTail_joint_continuousOn.div_const Real.pi

end GoldbachContinuous22

#print axioms GoldbachContinuous22.reTwoF
#print axioms GoldbachContinuous22.reTwoKernelTail
#print axioms GoldbachContinuous22.reTwoTailSign
#print axioms GoldbachContinuous22.reTwoClosedTail
#print axioms GoldbachContinuous22.reTwoNormalizedTail
#print axioms GoldbachContinuous22.norm_reTwoF_le
#print axioms GoldbachContinuous22.reTwoKernelTail_primitive_deriv
#print axioms GoldbachContinuous22.reTwoKernelTail_primitive_limit
#print axioms GoldbachContinuous22.integrable_reTwoKernel
#print axioms GoldbachContinuous22.integral_reTwoKernel
#print axioms GoldbachContinuous22.reTwoF_continuous
#print axioms GoldbachContinuous22.reTwoTailSign_abs
#print axioms GoldbachContinuous22.reTwoTailSign_sq
#print axioms GoldbachContinuous22.norm_reTwoF_signed_le
#print axioms GoldbachContinuous22.integrable_reTwoF_tail
#print axioms GoldbachContinuous22.norm_integral_reTwoF_tail_le
#print axioms GoldbachContinuous22.norm_reTwo_normalized_signed_tail_sum_le
#print axioms GoldbachContinuous22.reTwoClosedTail_continuousOn
#print axioms GoldbachContinuous22.reTwoNormalizedTail_continuousOn
#print axioms GoldbachContinuous22.reTwoClosedTail_joint_continuousOn
#print axioms GoldbachContinuous22.reTwoNormalizedTail_joint_continuousOn
