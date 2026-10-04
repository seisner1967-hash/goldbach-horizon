import ComplexGammaMellinHolomorphy22
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! SOURCE ONLY, not compiled or probed by the author.
The actual prime-power definition of Lambda is used directly. No divisor
inversion, Euler/logarithmic-derivative identity, free L1 hypothesis or free
Mellin equality is used. The analytic dependency is the actual independently
checked complex Gamma inversion27. Tail22 is NOT imported here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachComplexGammaMellin22

def lambdaMellinSize (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-2 : ℝ)

def lambdaMellinMass : ℝ := ∑' n : ℕ, lambdaMellinSize n

def lambdaMellinCoefficient (n : ℕ) (t : ℝ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-verticalS t)

def lambdaMellinDirichlet (t : ℝ) : ℂ := ∑' n : ℕ, lambdaMellinCoefficient n t

def lambdaMellinIntegrand (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  lambdaMellinCoefficient n t * complexGammaKernel w t

def lambdaMellinThermal (w : ℂ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-((n : ℂ) * w))

theorem lambda_direct_le_log {n : ℕ} (hn : 0 < n) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  split_ifs
  · exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos n)
      (by exact_mod_cast Nat.minFac_le hn)
  · exact Real.log_nonneg (by exact_mod_cast hn)

theorem lambdaMellinSize_nonneg (n : ℕ) : 0 ≤ lambdaMellinSize n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Direct log inequality at exponent 1/2, with its positive denominator paid. -/
theorem lambdaMellinSize_pseries_bound (n : ℕ) :
    lambdaMellinSize n ≤ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp [lambdaMellinSize]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hx : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / 2 : ℝ))
  rw [Real.log_rpow hx] at hlog
  have hl : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
  calc
    lambdaMellinSize n ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right (lambda_direct_le_log hn0) (Real.rpow_nonneg hx.le _)
    _ ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) * (n : ℝ) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg hx.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hx]
      norm_num

theorem lambdaMellinSize_summable : Summable lambdaMellinSize := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le lambdaMellinSize_nonneg lambdaMellinSize_pseries_bound
    (hp.mul_left 2)

/-- Integral test for a fully numerical bound, without an unspecified series constant. -/
theorem mellin_pseries_shift_two_sum_le (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 2 := by
  have hmono : AntitoneOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ)))
      (Icc (1 : ℝ) (1 + K)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_exponent_nonpos (by linarith [hx.1]) hxy (by norm_num)
  have hsum := hmono.sum_le_integral
  have hz : (0 : ℝ) ∉ uIcc (1 : ℝ) (1 + (K : ℝ)) := by
    have hle : (1 : ℝ) ≤ 1 + (K : ℝ) :=
      le_add_of_nonneg_right (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))
    rw [uIcc_of_le hle]
    simp
  have hi := integral_rpow (a := (1 : ℝ)) (b := (1 + K : ℝ))
    (r := -(3 / 2 : ℝ)) (Or.inr ⟨by norm_num, hz⟩)
  have he : (∫ x : ℝ in (1 : ℝ)..(1 + K : ℝ), x ^ (-(3 / 2 : ℝ))) ≤ 2 := by
    rw [hi]
    have hp := Real.rpow_nonneg (by positivity : 0 ≤ (1 + K : ℝ)) (-(3 / 2 : ℝ) + 1)
    norm_num at hp ⊢
    nlinarith
  apply le_trans _ he
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  push_cast
  ring

theorem mellin_pseries_tsum_le_three :
    (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 3 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have ht : (∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 2 :=
    Real.tsum_le_of_sum_range_le
      (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _) mellin_pseries_shift_two_sum_le
  have he := sum_add_tsum_nat_add 2 hs
  have hfirst : (∑ n ∈ Finset.range 2, (n : ℝ) ^ (-(3 / 2 : ℝ))) = 1 := by
    norm_num [Finset.sum_range_succ, Real.zero_rpow]
  rw [hfirst] at he
  linarith

theorem lambdaMellinMass_le_six : lambdaMellinMass ≤ 6 := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  calc
    lambdaMellinMass ≤ ∑' n : ℕ, 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
      tsum_le_tsum lambdaMellinSize_pseries_bound lambdaMellinSize_summable (hp.mul_left 2)
    _ = 2 * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
    _ ≤ 6 := by linarith [mellin_pseries_tsum_le_three]

theorem lambdaMellinMass_nonneg : 0 ≤ lambdaMellinMass :=
  tsum_nonneg lambdaMellinSize_nonneg

theorem norm_lambdaMellinCoefficient (n : ℕ) (t : ℝ) :
    ‖lambdaMellinCoefficient n t‖ = lambdaMellinSize n := by
  by_cases hn : n = 0
  · subst n
    simp [lambdaMellinCoefficient, lambdaMellinSize]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : ‖(n : ℂ) ^ (-verticalS t)‖ = (n : ℝ) ^ (-2 : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_eq_abs,
      Complex.abs_cpow_eq_rpow_re_of_pos hnR, Complex.neg_re, verticalS_re]
  simp only [lambdaMellinCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, hp, lambdaMellinSize]

theorem lambdaMellinCoefficient_norm_summable (t : ℝ) :
    Summable (fun n : ℕ => ‖lambdaMellinCoefficient n t‖) := by
  simpa only [norm_lambdaMellinCoefficient] using lambdaMellinSize_summable

theorem lambdaMellinCoefficient_continuous (n : ℕ) :
    Continuous (lambdaMellinCoefficient n) := by
  by_cases hn : n = 0
  · subst n
    simpa [lambdaMellinCoefficient] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  exact continuous_const.mul (verticalS_continuous.neg.const_cpow (Or.inl hnC))

theorem lambdaMellinDirichlet_continuous : Continuous lambdaMellinDirichlet := by
  apply continuous_tsum
  · exact lambdaMellinCoefficient_continuous
  · exact lambdaMellinSize_summable
  · intro n t
    exact (norm_lambdaMellinCoefficient n t).le

theorem norm_lambdaMellinDirichlet_le (t : ℝ) :
    ‖lambdaMellinDirichlet t‖ ≤ 6 := by
  calc
    _ ≤ ∑' n : ℕ, ‖lambdaMellinCoefficient n t‖ :=
      norm_tsum_le_tsum_norm (lambdaMellinCoefficient_norm_summable t)
    _ = lambdaMellinMass := by simp only [norm_lambdaMellinCoefficient, lambdaMellinMass]
    _ ≤ 6 := lambdaMellinMass_le_six

theorem norm_lambdaMellinIntegrand (w : ℂ) (n : ℕ) (t : ℝ) :
    ‖lambdaMellinIntegrand w n t‖ = lambdaMellinSize n * ‖complexGammaKernel w t‖ := by
  rw [lambdaMellinIntegrand, norm_mul, norm_lambdaMellinCoefficient]

theorem lambdaMellinIntegrand_integrable {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    Integrable (lambdaMellinIntegrand w n) := by
  have hb := (complexGammaKernel_integrable hw).norm.const_mul (lambdaMellinSize n)
  apply hb.mono' ((lambdaMellinCoefficient_continuous n).mul
    (complexGammaKernel_continuous hw)).aestronglyMeasurable
  filter_upwards with t
  exact (norm_lambdaMellinIntegrand w n t).le

theorem lambdaMellinIntegrand_integral_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖lambdaMellinIntegrand w n t‖) := by
  have h := lambdaMellinSize_summable.mul_right (∫ t : ℝ, ‖complexGammaKernel w t‖)
  refine h.congr fun n => ?_
  simp_rw [norm_lambdaMellinIntegrand]
  rw [integral_mul_left]

theorem lambdaMellinIntegrand_tsum_eq (w : ℂ) (t : ℝ) :
    (∑' n : ℕ, lambdaMellinIntegrand w n t) =
      lambdaMellinDirichlet t * complexGammaKernel w t := by
  exact tsum_mul_right

theorem lambdaMellinProduct_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun t : ℝ => lambdaMellinDirichlet t * complexGammaKernel w t) := by
  have hb := (complexGammaKernel_integrable hw).norm.const_mul (6 : ℝ)
  apply hb.mono' (lambdaMellinDirichlet_continuous.mul
    (complexGammaKernel_continuous hw)).aestronglyMeasurable
  filter_upwards with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_lambdaMellinDirichlet_le t) (norm_nonneg _)

theorem lambdaMellinProduct_local_uniform_bound {w : ℂ} (hw : 0 < w.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball w ε, 0 < z.re ∧ ∀ t : ℝ,
      ‖lambdaMellinDirichlet t * complexGammaKernel z t‖ ≤
        6 * ((‖w‖ / 2) ^ (-2 : ℝ) * (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
          Real.exp (-localDecayGap w * |t|) := by
  obtain ⟨ε, hε, hball⟩ := exists_local_kernel_ball hw
  refine ⟨ε, hε, ?_⟩
  intro z hz
  obtain ⟨hzR, hn, ha⟩ := hball z hz
  refine ⟨hzR, ?_⟩
  intro t
  rw [norm_mul]
  have h := complexGammaKernel_local_bound hw hzR hn ha t
  calc
    _ ≤ 6 * ‖complexGammaKernel z t‖ :=
      mul_le_mul_of_nonneg_right (norm_lambdaMellinDirichlet_le t) (norm_nonneg _)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 6)
      simpa only [mul_assoc] using hh

theorem lambdaMellinProduct_local_envelope_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun t : ℝ =>
      6 * ((‖w‖ / 2) ^ (-2 : ℝ) * (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ)) *
        Real.exp (-localDecayGap w * |t|)) := by
  let C : ℝ :=
    6 * ((‖w‖ / 2) ^ (-2 : ℝ) * (1 / Real.cos (rotationAngle w)) ^ (2 : ℕ))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hd : 0 < localDecayGap w := (local_parameters hw).2.2.2
  have h := weightedExponential_integrable hd C
  have hc : Continuous (fun t : ℝ => C * Real.exp (-localDecayGap w * |t|)) := by fun_prop
  apply h.mono' hc.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
  have ht : 1 ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hh : C ≤ C * (2 + |t|) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hC
  exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

/-- Principal powers of a positive-real multiple: no hidden branch wrap. -/
theorem principal_cpow_positive_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrC hw),
    Complex.log_ofReal_mul hr hw, Complex.ofReal_log hr.le, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero hrC, ← Complex.cpow_def_of_ne_zero hw]

theorem lambdaMellinIntegrand_single_inversion {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (∫ t : ℝ, lambdaMellinIntegrand w n t) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-((n : ℂ) * w)) := by
  by_cases hn : n = 0
  · subst n
    simp [lambdaMellinIntegrand, lambdaMellinCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnw : 0 < ((n : ℂ) * w).re := by
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      using mul_pos hnR hw
  have he : lambdaMellinIntegrand w n =
      (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        complexGammaKernel ((n : ℂ) * w) t) := by
    funext t
    have hp : ((n : ℂ) * w) ^ (-verticalS t) =
        (n : ℂ) ^ (-verticalS t) * w ^ (-verticalS t) := by
      simpa only [Complex.ofReal_natCast] using
        principal_cpow_positive_mul hnR (rightHalfPlane_ne_zero hw) (-verticalS t)
    change ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-verticalS t)) *
        (Complex.Gamma (verticalS t) * w ^ (-verticalS t)) =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Complex.Gamma (verticalS t) * ((n : ℂ) * w) ^ (-verticalS t))
    rw [hp]
    ring
  rw [he, integral_mul_left]
  calc
    _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
        complexGammaInverse ((n : ℂ) * w) := by unfold complexGammaInverse; ring
    _ = _ := by rw [complexGammaInverse_eq_exp hnw]

theorem lambdaMellinThermal_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (-((n : ℂ) * w))‖) := by
  have hs := lambdaMellinIntegrand_integral_norm_summable hw
  let Cpi : ℂ := (((1 / (2 * Real.pi) : ℝ) : ℂ))
  apply Summable.of_norm_bounded
    (fun n : ℕ => ‖Cpi‖ * (∫ t : ℝ, ‖lambdaMellinIntegrand w n t‖))
    (hs.mul_left ‖Cpi‖)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    ← lambdaMellinIntegrand_single_inversion hw n, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg Cpi)

/-- Actual infinite Lambda/Gamma interchange and inversion on Re(w)>0. -/
theorem lambdaMellinThermal_eq_integral {w : ℂ} (hw : 0 < w.re) :
    lambdaMellinThermal w = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ t : ℝ, lambdaMellinDirichlet t * complexGammaKernel w t) := by
  have he := integral_tsum_of_summable_integral_norm
    (lambdaMellinIntegrand_integrable hw) (lambdaMellinIntegrand_integral_norm_summable hw)
  have hf : (fun t : ℝ => ∑' n : ℕ, lambdaMellinIntegrand w n t) =
      (fun t : ℝ => lambdaMellinDirichlet t * complexGammaKernel w t) :=
    funext (lambdaMellinIntegrand_tsum_eq w)
  rw [hf] at he
  rw [← he, ← tsum_mul_left]
  exact tsum_congr (fun n => (lambdaMellinIntegrand_single_inversion hw n).symm)

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.lambdaMellinSize
#print axioms GoldbachComplexGammaMellin22.lambdaMellinMass
#print axioms GoldbachComplexGammaMellin22.lambdaMellinCoefficient
#print axioms GoldbachComplexGammaMellin22.lambdaMellinDirichlet
#print axioms GoldbachComplexGammaMellin22.lambdaMellinIntegrand
#print axioms GoldbachComplexGammaMellin22.lambdaMellinThermal
#print axioms GoldbachComplexGammaMellin22.lambda_direct_le_log
#print axioms GoldbachComplexGammaMellin22.lambdaMellinSize_nonneg
#print axioms GoldbachComplexGammaMellin22.lambdaMellinSize_pseries_bound
#print axioms GoldbachComplexGammaMellin22.lambdaMellinSize_summable
#print axioms GoldbachComplexGammaMellin22.mellin_pseries_shift_two_sum_le
#print axioms GoldbachComplexGammaMellin22.mellin_pseries_tsum_le_three
#print axioms GoldbachComplexGammaMellin22.lambdaMellinMass_le_six
#print axioms GoldbachComplexGammaMellin22.lambdaMellinMass_nonneg
#print axioms GoldbachComplexGammaMellin22.norm_lambdaMellinCoefficient
#print axioms GoldbachComplexGammaMellin22.lambdaMellinCoefficient_norm_summable
#print axioms GoldbachComplexGammaMellin22.lambdaMellinCoefficient_continuous
#print axioms GoldbachComplexGammaMellin22.lambdaMellinDirichlet_continuous
#print axioms GoldbachComplexGammaMellin22.norm_lambdaMellinDirichlet_le
#print axioms GoldbachComplexGammaMellin22.norm_lambdaMellinIntegrand
#print axioms GoldbachComplexGammaMellin22.lambdaMellinIntegrand_integrable
#print axioms GoldbachComplexGammaMellin22.lambdaMellinIntegrand_integral_norm_summable
#print axioms GoldbachComplexGammaMellin22.lambdaMellinIntegrand_tsum_eq
#print axioms GoldbachComplexGammaMellin22.lambdaMellinProduct_integrable
#print axioms GoldbachComplexGammaMellin22.lambdaMellinProduct_local_uniform_bound
#print axioms GoldbachComplexGammaMellin22.lambdaMellinProduct_local_envelope_integrable
#print axioms GoldbachComplexGammaMellin22.principal_cpow_positive_mul
#print axioms GoldbachComplexGammaMellin22.lambdaMellinIntegrand_single_inversion
#print axioms GoldbachComplexGammaMellin22.lambdaMellinThermal_norm_summable
#print axioms GoldbachComplexGammaMellin22.lambdaMellinThermal_eq_integral
