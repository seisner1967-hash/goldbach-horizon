import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic
import TS.Goldbach.Strong.TS303.ClosedAnchoredMacroscopicEnvelope

/-!
# TS304 - Closed Completion Correction and Horizontal Decay

TS303 closes the three spectral pieces of the horizontal Perron integrand.
This sprint closes the remaining archimedean completion correction and then
assembles the full horizontal decay at every fixed arithmetic scale.

The proof deliberately avoids a complex Stirling or digamma asymptotic.  On a
fixed-radius ball around a finite-grid height, the explicit xi/zeta multiplier
is holomorphic and nonzero.  Euler's integral bounds Gamma from above, while
Euler's reflection identity gives a lower bound at the center.  A centered
holomorphic logarithm and the TS300 Borel-Caratheodory estimate convert the
resulting exponential value ratio into a logarithmic-derivative bound linear
in the height.

The final horizontal envelope adds four independently proved pieces: the
nearby-zero reciprocal load (TS300), the finite macroscopic correction
(TS302), the anchored macroscopic quotient (TS303), and the completion
correction proved here.
-/

noncomputable section

namespace TS304
namespace Goldbach

open Complex Filter Metric Set Topology MeasureTheory
open scoped Topology

/-! ## A fixed Gamma bound on the compact real interval used below -/

/-- A positive fixed bound for real Gamma on `[1/8, 3]`. -/
noncomputable def gammaCompactBound : Real :=
  max 1 (sSup (Real.Gamma '' Set.Icc (1 / 8 : Real) 3))

theorem gammaCompactBound_pos : 0 < gammaCompactBound := by
  unfold gammaCompactBound
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem real_Gamma_le_gammaCompactBound
    {a : Real}
    (ha : Membership.mem (Set.Icc (1 / 8 : Real) 3) a) :
    Real.Gamma a <= gammaCompactBound := by
  have hContinuous : ContinuousOn Real.Gamma (Set.Icc (1 / 8 : Real) 3) := by
    intro x hx
    exact (Real.differentiableAt_Gamma (by
      intro m hm
      have hxPos : 0 < x := by linarith [hx.1]
      have hmNonnegative : 0 <= (m : Real) := Nat.cast_nonneg m
      nlinarith)).continuousAt.continuousWithinAt
  have hCompact : IsCompact (Real.Gamma '' Set.Icc (1 / 8 : Real) 3) := by
    exact isCompact_Icc.image_of_continuousOn hContinuous
  have hMem : Membership.mem (Real.Gamma '' Set.Icc (1 / 8 : Real) 3)
      (Real.Gamma a) :=
    Exists.intro a (And.intro ha rfl)
  exact (le_csSup hCompact.bddAbove hMem).trans (le_max_right _ _)

/-- Euler's integral bounds complex Gamma by real Gamma at the real part. -/
theorem norm_Gamma_le_real_Gamma_re
    {s : Complex}
    (hs : 0 < s.re) :
    norm (Complex.Gamma s) <= Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  apply MeasureTheory.norm_integral_le_of_norm_le
  next => exact Real.GammaIntegral_convergent hs
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
  simp only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-x)), Complex.norm_eq_abs]
  rw [Complex.abs_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.abs_exp, Complex.abs_ofReal, sub_re, Real.exp_pos]

/-- Uniform complex Gamma bound when the real part lies in `[1/8, 3]`. -/
theorem norm_Gamma_le_gammaCompactBound
    {s : Complex}
    (hs : Membership.mem (Set.Icc (1 / 8 : Real) 3) s.re) :
    norm (Complex.Gamma s) <= gammaCompactBound := by
  exact (norm_Gamma_le_real_Gamma_re (by linarith [hs.1])).trans
    (real_Gamma_le_gammaCompactBound hs)

/-! ## Elementary strip and Gamma estimates -/

/-- Fixed local radius used around every quantitative horizontal point. -/
noncomputable def completionLocalRadius : Real := 1 / 4

theorem completionLocalRadius_pos : 0 < completionLocalRadius := by
  norm_num [completionLocalRadius]

theorem local_point_re_bounds
    {c z : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hz : dist z c <= completionLocalRadius) :
    Membership.mem (Set.Icc (-7 / 4 : Real) (9 / 4 : Real)) z.re := by
  have hRe : |(z - c).re| <= norm (z - c) := by
    simpa [Complex.norm_eq_abs] using Complex.abs_re_le_abs (z - c)
  have hNorm : norm (z - c) <= completionLocalRadius := by
    simpa [dist_eq] using hz
  have hReBounds := abs_le.mp hRe
  have hReLower := hReBounds.1
  have hReUpper := hReBounds.2
  simp only [sub_re] at hReLower hReUpper
  unfold completionLocalRadius at hNorm
  constructor <;> linarith [hcRe.1, hcRe.2]

theorem local_point_abs_im_ge
    {c z : Complex}
    (hcIm : 1 <= |c.im|)
    (hz : dist z c <= completionLocalRadius) :
    3 / 4 <= |z.im| := by
  have hIm : |(z - c).im| <= norm (z - c) := by
    simpa [Complex.norm_eq_abs] using Complex.abs_im_le_abs (z - c)
  have hNorm : norm (z - c) <= completionLocalRadius := by
    simpa [dist_eq] using hz
  have hTriangle : |c.im| <= |z.im| + |z.im - c.im| := by
    calc
      |c.im| = |z.im - (z.im - c.im)| := by ring_nf
      _ <= |z.im| + |z.im - c.im| := abs_sub _ _
  unfold completionLocalRadius at hNorm
  simp only [sub_im] at hIm
  linarith

/-- Gamma in the fixed horizontal strip has a uniform upper bound away from
the real axis. -/
theorem norm_Gamma_half_le
    {w : Complex}
    (hwRe : Membership.mem (Set.Icc (-7 / 4 : Real) (9 / 4 : Real)) w.re)
    (hwIm : 3 / 4 <= |w.im|) :
    norm (Complex.Gamma (w / 2)) <= (8 / 3 : Real) * gammaCompactBound := by
  let u : Complex := w / 2
  have huRe : Membership.mem (Set.Icc (1 / 8 : Real) 3) (u + 1).re := by
    dsimp [u]
    simp only [Complex.div_re, add_re, one_re]
    norm_num
    constructor <;> nlinarith [hwRe.1, hwRe.2]
  have huNorm : 3 / 8 <= norm u := by
    have hwNorm : |w.im| <= norm w := by
      simpa [Complex.norm_eq_abs] using Complex.abs_im_le_abs w
    calc
      (3 / 8 : Real) <= norm w / 2 := by linarith
      _ = norm (w / 2) := by simp [norm_div]
      _ = norm u := by rfl
  have huNe : Not (u = 0) := by
    intro hu
    rw [hu] at huNorm
    norm_num at huNorm
  have hRec := Complex.Gamma_add_one u huNe
  have hGammaNext := norm_Gamma_le_gammaCompactBound huRe
  have hNormEq : norm (Complex.Gamma u) =
      norm (Complex.Gamma (u + 1)) / norm u := by
    have hRecNorm := congrArg norm hRec
    simp only [norm_mul] at hRecNorm
    rw [hRecNorm]
    apply (eq_div_iff (norm_ne_zero_iff.mpr huNe)).mpr
    ring
  rw [hNormEq]
  calc
    norm (Complex.Gamma (u + 1)) / norm u <=
        gammaCompactBound / (3 / 8 : Real) := by
      calc
        norm (Complex.Gamma (u + 1)) / norm u <=
            gammaCompactBound / norm u :=
          div_le_div_of_nonneg_right hGammaNext (norm_nonneg _)
        _ <= gammaCompactBound / (3 / 8 : Real) :=
          div_le_div_of_nonneg_left gammaCompactBound_pos.le (by norm_num) huNorm
    _ = (8 / 3 : Real) * gammaCompactBound := by ring

/-- A coarse exponential bound for complex sine. -/
theorem norm_sin_le_exp_abs_im (z : Complex) :
    norm (Complex.sin z) <= Real.exp |z.im| := by
  have hPos : 0 < Real.exp |z.im| := Real.exp_pos _
  have hOne : norm (Complex.exp (-z * Complex.I)) <= Real.exp |z.im| := by
    rw [Complex.norm_eq_abs, Complex.abs_exp]
    simp only [mul_re, neg_re, I_re, I_im, mul_zero, neg_mul, sub_neg_eq_add,
      zero_add]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have hTwo : norm (Complex.exp (z * Complex.I)) <= Real.exp |z.im| := by
    rw [Complex.norm_eq_abs, Complex.abs_exp]
    simp only [mul_re, I_re, I_im, mul_zero]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  unfold Complex.sin
  calc
    norm ((Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) *
          Complex.I / 2) =
        norm (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) / 2 := by
      simp [norm_div, norm_mul]
    _ <= (norm (Complex.exp (-z * Complex.I)) +
          norm (Complex.exp (z * Complex.I))) / 2 := by
      gcongr
      exact norm_sub_le _ _
    _ <= (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = Real.exp |z.im| := by ring

/-- Reflection plus the compact Gamma bound gives a lower bound for Gamma on
the horizontal centers. -/
theorem Gamma_half_lower_bound
    {c : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hcIm : 1 <= |c.im|) :
    Real.pi /
        (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)) <=
      norm (Complex.Gamma (c / 2)) := by
  let u : Complex := c / 2
  let v : Complex := 1 - u
  have huIm : |u.im| = |c.im| / 2 := by
    dsimp [u]
    simp only [Complex.div_im]
    norm_num
    rw [show c.im * 2 / 4 = c.im / 2 by ring, abs_div]
    norm_num
  have huImPos : 0 < |u.im| := by rw [huIm]; positivity
  have hvNe : Not (v = 0) := by
    intro hv
    have hvIm := congrArg Complex.im hv
    dsimp [v] at hvIm
    simp only [sub_im, one_im, zero_sub, zero_im, neg_eq_zero] at hvIm
    exact huImPos.ne' (abs_eq_zero.mpr hvIm)
  have hvRe : Membership.mem (Set.Icc (1 / 8 : Real) 3) (v + 1).re := by
    dsimp [v, u]
    simp only [sub_re, one_re, add_re, Complex.div_re]
    norm_num
    constructor <;> nlinarith [hcRe.1, hcRe.2]
  have hvNorm : 1 / 2 <= norm v := by
    have hvImNorm : |v.im| <= norm v := by
      simpa [Complex.norm_eq_abs] using Complex.abs_im_le_abs v
    have hvImAbs : |v.im| = |c.im| / 2 := by
      dsimp [v]
      simp only [sub_im, one_im, zero_sub, abs_neg, huIm]
    rw [hvImAbs] at hvImNorm
    linarith
  have hRec := Complex.Gamma_add_one v hvNe
  have hGammaNext := norm_Gamma_le_gammaCompactBound hvRe
  have hGammaV : norm (Complex.Gamma v) <= 2 * gammaCompactBound := by
    have hRecNorm := congrArg norm hRec
    simp only [norm_mul] at hRecNorm
    have hEq : norm (Complex.Gamma v) =
        norm (Complex.Gamma (v + 1)) / norm v := by
      rw [hRecNorm]
      apply (eq_div_iff (norm_ne_zero_iff.mpr hvNe)).mpr
      ring
    rw [hEq]
    calc
      norm (Complex.Gamma (v + 1)) / norm v <=
          gammaCompactBound / (1 / 2 : Real) := by
        calc
          norm (Complex.Gamma (v + 1)) / norm v <=
              gammaCompactBound / norm v :=
            div_le_div_of_nonneg_right hGammaNext (norm_nonneg _)
          _ <= gammaCompactBound / (1 / 2 : Real) :=
            div_le_div_of_nonneg_left gammaCompactBound_pos.le (by norm_num) hvNorm
      _ = 2 * gammaCompactBound := by ring
  have hSinNe : Not (Complex.sin (Real.pi * u) = 0) := by
    intro hSinZero
    have hkExists := Complex.sin_eq_zero_iff.mp hSinZero
    let k := hkExists.choose
    have hk := hkExists.choose_spec
    have hIm := congrArg Complex.im hk
    norm_num [mul_im] at hIm
    have hPi : Not (Real.pi = 0) := ne_of_gt Real.pi_pos
    have huImZero : u.im = 0 := hIm.resolve_left hPi
    exact huImPos.ne' (abs_eq_zero.mpr huImZero)
  have hReflection := Complex.Gamma_mul_Gamma_one_sub u
  have hProduct :
      Complex.Gamma u * Complex.Gamma (1 - u) *
          Complex.sin (Real.pi * u) = Real.pi := by
    calc
      Complex.Gamma u * Complex.Gamma (1 - u) *
          Complex.sin (Real.pi * u) =
        (Real.pi / Complex.sin (Real.pi * u)) *
          Complex.sin (Real.pi * u) := by rw [hReflection]
      _ = Real.pi := by field_simp
  have hProductNorm := congrArg norm hProduct
  simp only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hProductNorm
  have hSin : norm (Complex.sin (Real.pi * u)) <=
      Real.exp (Real.pi * |c.im| / 2) := by
    apply (norm_sin_le_exp_abs_im (Real.pi * u)).trans_eq
    congr 2
    simp [mul_im, abs_mul, abs_of_pos Real.pi_pos, huIm]
    ring
  have hMajor : Real.pi <=
      norm (Complex.Gamma u) *
        (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)) := by
    have hGammaUNonnegative := norm_nonneg (Complex.Gamma u)
    have hSinNonnegative := norm_nonneg (Complex.sin (Real.pi * u))
    calc
      Real.pi = norm (Complex.Gamma u) * norm (Complex.Gamma (1 - u)) *
          norm (Complex.sin (Real.pi * u)) := hProductNorm.symm
      _ <= norm (Complex.Gamma u) * (2 * gammaCompactBound) *
          norm (Complex.sin (Real.pi * u)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hGammaV hGammaUNonnegative)
          hSinNonnegative
      _ <= norm (Complex.Gamma u) * (2 * gammaCompactBound) *
          Real.exp (Real.pi * |c.im| / 2) := by
        exact mul_le_mul_of_nonneg_left hSin
          (mul_nonneg hGammaUNonnegative
            (mul_nonneg (by norm_num) gammaCompactBound_pos.le))
      _ = norm (Complex.Gamma u) *
          (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)) := by ring
  have hDenPos : 0 <
      2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2) := by
    exact mul_pos (mul_pos (by norm_num) gammaCompactBound_pos) (Real.exp_pos _)
  have hMajor' : Real.pi <= norm (Complex.Gamma u) *
      (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)) := by
    simpa [u] using hMajor
  apply (mul_le_mul_right hDenPos).mp
  have hCancel :
      (Real.pi /
          (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2))) *
        (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)) =
          Real.pi := by
    field_simp
  rw [hCancel]
  exact hMajor'

/-! ## Bounds for the explicit xi/zeta multiplier -/

/-- Fixed bound for the real-power factor contributed by `pi^(-s/2)`. -/
noncomputable def piHalfPowerUpper : Real := Real.pi ^ (2 : Real)

theorem piHalfPowerUpper_pos : 0 < piHalfPowerUpper := by
  unfold piHalfPowerUpper
  exact Real.rpow_pos_of_pos Real.pi_pos _

theorem norm_pi_cpow_neg_half_le
    {w : Complex}
    (hwRe : Membership.mem (Set.Icc (-7 / 4 : Real) (9 / 4 : Real)) w.re) :
    norm ((Real.pi : Complex) ^ (-w / 2)) <= piHalfPowerUpper := by
  rw [Complex.norm_eq_abs,
    Complex.abs_cpow_eq_rpow_re_of_pos Real.pi_pos]
  unfold piHalfPowerUpper
  apply Real.rpow_le_rpow_of_exponent_le
  next => linarith [Real.two_le_pi]
  simp only [div_re, neg_re]
  norm_num
  linarith [hwRe.1]

theorem piHalfPowerLower_le_norm
    {c : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re) :
    Real.pi ^ (-1 : Real) <=
      norm ((Real.pi : Complex) ^ (-c / 2)) := by
  rw [Complex.norm_eq_abs,
    Complex.abs_cpow_eq_rpow_re_of_pos Real.pi_pos]
  apply Real.rpow_le_rpow_of_exponent_le
  next => linarith [Real.two_le_pi]
  simp only [div_re, neg_re]
  norm_num
  linarith [hcRe.2]

theorem xiZetaLocalMultiplier_eq_polynomial_mul_gamma (s : Complex) :
    TS290.Goldbach.xiZetaLocalMultiplier s =
      (s * (s - 1) / 2) *
        ((Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2)) := by
  unfold TS290.Goldbach.xiZetaLocalMultiplier
    TS282.Goldbach.completedRiemannZetaGammaInv
  change
    (s * (s - 1) / 2) /
        (Inv.inv ((Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2))) = _
  simp [div_eq_mul_inv]

theorem xiZetaLocalMultiplier_norm_upper_local
    {T : Nat} {c w : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hcIm : 1 <= |c.im|)
    (hcNorm : norm c <= (T : Real) + 3)
    (hw : dist w c <= completionLocalRadius) :
    norm (TS290.Goldbach.xiZetaLocalMultiplier w) <=
      (4 * piHalfPowerUpper * gammaCompactBound) *
        ((T : Real) + 4) ^ 2 := by
  have hwRe := local_point_re_bounds hcRe hw
  have hwIm := local_point_abs_im_ge hcIm hw
  have hwNorm : norm w <= (T : Real) + 4 := by
    have hDist : norm (w - c) <= completionLocalRadius := by
      simpa [dist_eq] using hw
    unfold completionLocalRadius at hDist
    calc
      norm w = norm ((w - c) + c) := by ring_nf
      _ <= norm (w - c) + norm c := norm_add_le _ _
      _ <= 1 / 4 + ((T : Real) + 3) := by linarith
      _ <= (T : Real) + 4 := by linarith
  have hwSubNorm : norm (w - 1) <= (T : Real) + 5 := by
    calc
      norm (w - 1) <= norm w + norm (1 : Complex) := norm_sub_le _ _
      _ <= ((T : Real) + 4) + 1 := by
        simpa using add_le_add_right hwNorm 1
      _ = (T : Real) + 5 := by ring
  have hGamma := norm_Gamma_half_le hwRe hwIm
  have hPi := norm_pi_cpow_neg_half_le hwRe
  rw [xiZetaLocalMultiplier_eq_polynomial_mul_gamma]
  simp only [norm_mul, norm_div, norm_ofNat]
  have hTNonnegative : 0 <= (T : Real) := Nat.cast_nonneg T
  have hPi0 := piHalfPowerUpper_pos.le
  have hGamma0 := gammaCompactBound_pos.le
  calc
    norm w * norm (w - 1) / 2 *
        (norm ((Real.pi : Complex) ^ (-w / 2)) *
          norm (Complex.Gamma (w / 2))) <=
      ((T : Real) + 4) * ((T : Real) + 5) / 2 *
        (piHalfPowerUpper * ((8 / 3 : Real) * gammaCompactBound)) := by
      gcongr
    _ <= (4 * piHalfPowerUpper * gammaCompactBound) *
        ((T : Real) + 4) ^ 2 := by
      have hU : 0 < (T : Real) + 4 := by positivity
      have hGeom :
          ((T : Real) + 4) * ((T : Real) + 5) <=
            3 * ((T : Real) + 4) ^ 2 := by
        nlinarith [sq_nonneg ((T : Real) + 4)]
      have hFactor0 :
          0 <= (4 / 3 : Real) * piHalfPowerUpper * gammaCompactBound := by
        positivity
      calc
        ((T : Real) + 4) * ((T : Real) + 5) / 2 *
            (piHalfPowerUpper * ((8 / 3 : Real) * gammaCompactBound)) =
          ((4 / 3 : Real) * piHalfPowerUpper * gammaCompactBound) *
            (((T : Real) + 4) * ((T : Real) + 5)) := by ring
        _ <= ((4 / 3 : Real) * piHalfPowerUpper * gammaCompactBound) *
            (3 * ((T : Real) + 4) ^ 2) :=
          mul_le_mul_of_nonneg_left hGeom hFactor0
        _ = (4 * piHalfPowerUpper * gammaCompactBound) *
            ((T : Real) + 4) ^ 2 := by ring

theorem xiZetaLocalMultiplier_norm_lower_center
    {c : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hcIm : 1 <= |c.im|) :
    (Real.pi ^ (-1 : Real)) *
        (Real.pi /
          (4 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2))) <=
      norm (TS290.Goldbach.xiZetaLocalMultiplier c) := by
  have hcNorm : 1 <= norm c := by
    have hIm := Complex.abs_im_le_abs c
    simpa [Complex.norm_eq_abs] using hcIm.trans hIm
  have hcSubNorm : 1 <= norm (c - 1) := by
    have hIm := Complex.abs_im_le_abs (c - 1)
    have hEq : (c - 1).im = c.im := by simp
    rw [hEq] at hIm
    simpa [Complex.norm_eq_abs] using hcIm.trans hIm
  have hPolynomial : 1 / 2 <= norm (c * (c - 1) / 2) := by
    rw [norm_div, norm_mul, norm_ofNat]
    nlinarith [mul_le_mul hcNorm hcSubNorm (by norm_num : (0 : Real) <= 1)
      (norm_nonneg c)]
  have hPi := piHalfPowerLower_le_norm hcRe
  have hGamma := Gamma_half_lower_bound hcRe hcIm
  rw [xiZetaLocalMultiplier_eq_polynomial_mul_gamma, norm_mul, norm_mul]
  have hPiPos : 0 < Real.pi ^ (-1 : Real) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have hGammaDenPos : 0 <
      2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2) := by
    exact mul_pos (mul_pos (by norm_num) gammaCompactBound_pos) (Real.exp_pos _)
  have hGamma0 : 0 <= norm (Complex.Gamma (c / 2)) := norm_nonneg _
  calc
    (Real.pi ^ (-1 : Real)) *
        (Real.pi /
          (4 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2))) =
      (1 / 2 : Real) *
        ((Real.pi ^ (-1 : Real)) *
          (Real.pi /
            (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)))) := by ring
    _ <= norm (c * (c - 1) / 2) *
        ((Real.pi ^ (-1 : Real)) *
          (Real.pi /
            (2 * gammaCompactBound * Real.exp (Real.pi * |c.im| / 2)))) := by
      gcongr
    _ <= norm (c * (c - 1) / 2) *
        (norm ((Real.pi : Complex) ^ (-c / 2)) *
          norm (Complex.Gamma (c / 2))) := by
      gcongr

/-! ## A centered local logarithm of the completion multiplier -/

def completionMultiplierLogDerivative (z : Complex) : Complex :=
  deriv TS290.Goldbach.xiZetaLocalMultiplier z /
    TS290.Goldbach.xiZetaLocalMultiplier z

theorem completionMultiplier_nonzero_on_ball
    {c z : Complex}
    (hcIm : 1 <= |c.im|)
    (hz : Membership.mem (Metric.ball c completionLocalRadius) z) :
    Not (TS290.Goldbach.xiZetaLocalMultiplier z = 0) := by
  have hzAbs : 3 / 4 <= |z.im| :=
    local_point_abs_im_ge hcIm (Metric.mem_ball.mp hz).le
  apply TS297.Goldbach.xiZetaLocalMultiplier_ne_zero_of_im_ne_zero
  exact fun hZero => by
    rw [hZero, abs_zero] at hzAbs
    norm_num at hzAbs

theorem completionMultiplier_analyticOn_ball
    {c : Complex}
    (hcIm : 1 <= |c.im|) :
    AnalyticOnNhd Complex TS290.Goldbach.xiZetaLocalMultiplier
      (Metric.ball c completionLocalRadius) := by
  intro z hz
  have hzIm : Not (z.im = 0) := fun hZero => by
    have hzAbs : 3 / 4 <= |z.im| :=
      local_point_abs_im_ge hcIm (Metric.mem_ball.mp hz).le
    rw [hZero, abs_zero] at hzAbs
    norm_num at hzAbs
  unfold TS290.Goldbach.xiZetaLocalMultiplier
  have hGammaAnalytic : AnalyticAt Complex
      TS282.Goldbach.completedRiemannZetaGammaInv z :=
    TS282.Goldbach.differentiable_completedRiemannZetaGammaInv.differentiableOn.analyticAt
      univ_mem
  exact
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div
      analyticAt_const (by norm_num)).div hGammaAnalytic
      (TS282.Goldbach.completedRiemannZetaGammaInv_ne_zero_of_im_ne_zero hzIm)

theorem completionMultiplierLogDerivative_differentiableOn
    {c : Complex}
    (hcIm : 1 <= |c.im|) :
    DifferentiableOn Complex completionMultiplierLogDerivative
      (Metric.ball c completionLocalRadius) := by
  exact
    ((completionMultiplier_analyticOn_ball hcIm).deriv.div
      (completionMultiplier_analyticOn_ball hcIm)
      (fun z hz => completionMultiplier_nonzero_on_ball hcIm hz)).differentiableOn

/-- Primitive of the multiplier logarithmic derivative on the local ball. -/
noncomputable def completionLogPrimitive
    (c : Complex)
    (hcIm : 1 <= |c.im|) : Complex -> Complex :=
  Classical.choose
    (TS278.Goldbach.differentiableOn_holomorphicExactOn_ball
      (completionMultiplierLogDerivative_differentiableOn hcIm))

theorem completionLogPrimitive_hasDerivAt
    {c z : Complex}
    (hcIm : 1 <= |c.im|)
    (hz : Membership.mem (Metric.ball c completionLocalRadius) z) :
    HasDerivAt (completionLogPrimitive c hcIm)
      (completionMultiplierLogDerivative z) z :=
  Classical.choose_spec
    (TS278.Goldbach.differentiableOn_holomorphicExactOn_ball
      (completionMultiplierLogDerivative_differentiableOn hcIm)) z hz

def centeredCompletionLog
    (c : Complex)
    (hcIm : 1 <= |c.im|)
    (z : Complex) : Complex :=
  completionLogPrimitive c hcIm z - completionLogPrimitive c hcIm c

@[simp] theorem centeredCompletionLog_self
    (c : Complex)
    (hcIm : 1 <= |c.im|) :
    centeredCompletionLog c hcIm c = 0 := by
  simp [centeredCompletionLog]

theorem centeredCompletionLog_differentiableOn
    {c : Complex}
    (hcIm : 1 <= |c.im|) :
    DifferentiableOn Complex (centeredCompletionLog c hcIm)
      (Metric.ball c completionLocalRadius) := by
  intro z hz
  exact ((completionLogPrimitive_hasDerivAt hcIm hz).sub_const _).differentiableAt.differentiableWithinAt

def completionPrimitiveCorrectedMultiplier
    (c : Complex)
    (hcIm : 1 <= |c.im|)
    (z : Complex) : Complex :=
  TS290.Goldbach.xiZetaLocalMultiplier z *
    Complex.exp (-(completionLogPrimitive c hcIm z))

theorem completionPrimitiveCorrectedMultiplier_hasDerivAt_zero
    {c z : Complex}
    (hcIm : 1 <= |c.im|)
    (hz : Membership.mem (Metric.ball c completionLocalRadius) z) :
    HasDerivAt (completionPrimitiveCorrectedMultiplier c hcIm) 0 z := by
  have hM : HasDerivAt TS290.Goldbach.xiZetaLocalMultiplier
      (deriv TS290.Goldbach.xiZetaLocalMultiplier z) z :=
    ((completionMultiplier_analyticOn_ball hcIm) z hz).differentiableAt.hasDerivAt
  have hP := completionLogPrimitive_hasDerivAt hcIm hz
  have hProduct := hM.mul hP.neg.cexp
  apply hProduct.congr_deriv
  unfold completionMultiplierLogDerivative
  have hMNe := completionMultiplier_nonzero_on_ball hcIm hz
  field_simp
  ring

theorem completionPrimitiveCorrectedMultiplier_eq_center
    {c z : Complex}
    (hcIm : 1 <= |c.im|)
    (hz : Membership.mem (Metric.ball c completionLocalRadius) z) :
    completionPrimitiveCorrectedMultiplier c hcIm z =
      completionPrimitiveCorrectedMultiplier c hcIm c := by
  have hDiff : DifferentiableOn Complex
      (completionPrimitiveCorrectedMultiplier c hcIm)
      (Metric.ball c completionLocalRadius) := by
    intro w hw
    exact (completionPrimitiveCorrectedMultiplier_hasDerivAt_zero hcIm hw).differentiableAt.differentiableWithinAt
  have hFDeriv : forall w : Complex,
      Membership.mem (Metric.ball c completionLocalRadius) w ->
      fderivWithin Complex (completionPrimitiveCorrectedMultiplier c hcIm)
        (Metric.ball c completionLocalRadius) w = 0 := by
    intro w hw
    rw [fderivWithin_of_isOpen isOpen_ball hw]
    have h := (completionPrimitiveCorrectedMultiplier_hasDerivAt_zero hcIm hw).hasFDerivAt.fderiv
    calc
      fderiv Complex (completionPrimitiveCorrectedMultiplier c hcIm) w =
          ContinuousLinearMap.smulRight 1 0 := h
      _ = 0 := by ext; simp
  exact Convex.is_const_of_fderivWithin_eq_zero
    (convex_ball c completionLocalRadius) hDiff hFDeriv hz
    (Metric.mem_ball_self completionLocalRadius_pos)

theorem exp_centeredCompletionLog_eq_ratio
    {c z : Complex}
    (hcIm : 1 <= |c.im|)
    (hz : Membership.mem (Metric.ball c completionLocalRadius) z) :
    Complex.exp (centeredCompletionLog c hcIm z) =
      TS290.Goldbach.xiZetaLocalMultiplier z /
        TS290.Goldbach.xiZetaLocalMultiplier c := by
  have hConst := completionPrimitiveCorrectedMultiplier_eq_center hcIm hz
  have hcMem : Membership.mem (Metric.ball c completionLocalRadius) c :=
    Metric.mem_ball_self completionLocalRadius_pos
  have hcNe := completionMultiplier_nonzero_on_ball hcIm hcMem
  unfold completionPrimitiveCorrectedMultiplier at hConst
  unfold centeredCompletionLog
  rw [Complex.exp_sub]
  have hTransport := congrArg
    (fun q : Complex =>
      q * Complex.exp (completionLogPrimitive c hcIm z) /
        TS290.Goldbach.xiZetaLocalMultiplier c) hConst
  simpa [Complex.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm, hcNe] using hTransport.symm

theorem deriv_centeredCompletionLog_center
    {c : Complex}
    (hcIm : 1 <= |c.im|) :
    deriv (centeredCompletionLog c hcIm) c =
      TS297.Goldbach.xiZetaCompletionLogDerivative c := by
  have hcMem : Membership.mem (Metric.ball c completionLocalRadius) c :=
    Metric.mem_ball_self completionLocalRadius_pos
  have hDeriv := (completionLogPrimitive_hasDerivAt hcIm hcMem).deriv
  unfold centeredCompletionLog
  rw [deriv_sub_const, hDeriv]
  rfl

/-! ## Closed linear real-part and logarithmic-derivative envelopes -/

noncomputable def completionLocalUpperConstant : Real :=
  4 * piHalfPowerUpper * gammaCompactBound

noncomputable def completionCenterLowerBase : Real :=
  (Real.pi ^ (-1 : Real)) * (Real.pi / (4 * gammaCompactBound))

noncomputable def completionValueRatioConstant : Real :=
  completionLocalUpperConstant / completionCenterLowerBase

theorem completionLocalUpperConstant_pos : 0 < completionLocalUpperConstant := by
  unfold completionLocalUpperConstant
  exact mul_pos (mul_pos (by norm_num) piHalfPowerUpper_pos) gammaCompactBound_pos

theorem completionCenterLowerBase_pos : 0 < completionCenterLowerBase := by
  unfold completionCenterLowerBase
  exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (div_pos Real.pi_pos (mul_pos (by norm_num) gammaCompactBound_pos))

theorem completionValueRatioConstant_pos : 0 < completionValueRatioConstant := by
  unfold completionValueRatioConstant
  exact div_pos completionLocalUpperConstant_pos completionCenterLowerBase_pos

noncomputable def completionValueRatioMajorant (T : Nat) : Real :=
  completionValueRatioConstant * ((T : Real) + 4) ^ 2 *
    Real.exp (Real.pi * ((T : Real) + 1) / 2)

theorem completionValueRatioMajorant_pos (T : Nat) :
    0 < completionValueRatioMajorant T := by
  unfold completionValueRatioMajorant
  exact mul_pos
    (mul_pos completionValueRatioConstant_pos (sq_pos_of_pos (by positivity)))
    (Real.exp_pos _)

theorem xiZetaLocalMultiplier_norm_ratio_le
    {T : Nat} {c w : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hcImLower : 1 <= |c.im|)
    (hcImUpper : |c.im| <= (T : Real) + 1)
    (hcNorm : norm c <= (T : Real) + 3)
    (hw : dist w c <= completionLocalRadius) :
    norm (TS290.Goldbach.xiZetaLocalMultiplier w /
        TS290.Goldbach.xiZetaLocalMultiplier c) <=
      completionValueRatioMajorant T := by
  have hUpper := xiZetaLocalMultiplier_norm_upper_local
    hcRe hcImLower hcNorm hw
  have hLowerRaw := xiZetaLocalMultiplier_norm_lower_center hcRe hcImLower
  have hLower :
      completionCenterLowerBase /
          Real.exp (Real.pi * |c.im| / 2) <=
        norm (TS290.Goldbach.xiZetaLocalMultiplier c) := by
    unfold completionCenterLowerBase
    convert hLowerRaw using 1
    all_goals ring
  have hCenterPos : 0 < norm (TS290.Goldbach.xiZetaLocalMultiplier c) :=
    norm_pos_iff.mpr (TS297.Goldbach.xiZetaLocalMultiplier_ne_zero_of_im_ne_zero
      (fun h => by rw [h, abs_zero] at hcImLower; norm_num at hcImLower))
  have hLowerPos : 0 < completionCenterLowerBase /
      Real.exp (Real.pi * |c.im| / 2) :=
    div_pos completionCenterLowerBase_pos (Real.exp_pos _)
  rw [norm_div]
  calc
    norm (TS290.Goldbach.xiZetaLocalMultiplier w) /
        norm (TS290.Goldbach.xiZetaLocalMultiplier c) <=
      (completionLocalUpperConstant * ((T : Real) + 4) ^ 2) /
        (completionCenterLowerBase /
          Real.exp (Real.pi * |c.im| / 2)) := by
      have hUpper' :
          norm (TS290.Goldbach.xiZetaLocalMultiplier w) <=
            completionLocalUpperConstant * ((T : Real) + 4) ^ 2 := by
        simpa [completionLocalUpperConstant] using hUpper
      calc
        norm (TS290.Goldbach.xiZetaLocalMultiplier w) /
            norm (TS290.Goldbach.xiZetaLocalMultiplier c) <=
          (completionLocalUpperConstant * ((T : Real) + 4) ^ 2) /
            norm (TS290.Goldbach.xiZetaLocalMultiplier c) :=
          div_le_div_of_nonneg_right hUpper' hCenterPos.le
        _ <= (completionLocalUpperConstant * ((T : Real) + 4) ^ 2) /
            (completionCenterLowerBase /
              Real.exp (Real.pi * |c.im| / 2)) :=
          div_le_div_of_nonneg_left
            (mul_nonneg completionLocalUpperConstant_pos.le
              (sq_nonneg ((T : Real) + 4)))
            hLowerPos hLower
    _ = completionValueRatioConstant * ((T : Real) + 4) ^ 2 *
        Real.exp (Real.pi * |c.im| / 2) := by
      unfold completionValueRatioConstant
      field_simp [completionCenterLowerBase_pos.ne', Real.exp_ne_zero]
    _ <= completionValueRatioConstant * ((T : Real) + 4) ^ 2 *
        Real.exp (Real.pi * ((T : Real) + 1) / 2) := by
      have hPrefix : 0 <= completionValueRatioConstant * ((T : Real) + 4) ^ 2 :=
        mul_nonneg completionValueRatioConstant_pos.le (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hPrefix
      apply Real.exp_le_exp.mpr
      gcongr
    _ = completionValueRatioMajorant T := by
      rfl

noncomputable def completionClosedEnvelopeConstant : Real :=
  3 + Real.pi / 2 + max 0 (Real.log completionValueRatioConstant)

noncomputable def completionClosedRealPartEnvelope (T : Nat) : Real :=
  completionClosedEnvelopeConstant * ((T : Real) + 4)

theorem completionClosedEnvelopeConstant_pos :
    0 < completionClosedEnvelopeConstant := by
  unfold completionClosedEnvelopeConstant
  have hMax : 0 <= max 0 (Real.log completionValueRatioConstant) := le_max_left _ _
  nlinarith [Real.pi_pos]

theorem completionClosedRealPartEnvelope_pos (T : Nat) :
    0 < completionClosedRealPartEnvelope T := by
  unfold completionClosedRealPartEnvelope
  exact mul_pos completionClosedEnvelopeConstant_pos (by positivity)

theorem log_completionValueRatioMajorant_lt_closedEnvelope (T : Nat) :
    Real.log (completionValueRatioMajorant T) <
      completionClosedRealPartEnvelope T := by
  let C := completionValueRatioConstant
  let U : Real := (T : Real) + 4
  have hC : 0 < C := completionValueRatioConstant_pos
  have hU : 1 <= U := by
    dsimp [U]
    have hT0 : 0 <= (T : Real) := Nat.cast_nonneg T
    linarith
  have hLogU : Real.log U <= U :=
    (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hU)).trans (by linarith)
  have hLogC : Real.log C <= max 0 (Real.log C) := le_max_right _ _
  have hMax0 : 0 <= max 0 (Real.log C) := le_max_left _ _
  have hTOne : (T : Real) + 1 <= U := by dsimp [U]; linarith
  have hExpand :
      Real.log (completionValueRatioMajorant T) =
        Real.log C + 2 * Real.log U + Real.pi * ((T : Real) + 1) / 2 := by
    unfold completionValueRatioMajorant
    dsimp [C, U]
    have hUNe : Not (((T : Real) + 4) = 0) := by positivity
    rw [Real.log_mul (mul_ne_zero (ne_of_gt hC) (pow_ne_zero _ hUNe))
      (Real.exp_ne_zero _),
      Real.log_mul (ne_of_gt hC) (pow_ne_zero _ hUNe),
      Real.log_pow, Real.log_exp]
    norm_num
  rw [hExpand]
  unfold completionClosedRealPartEnvelope completionClosedEnvelopeConstant
  dsimp [C, U] at *
  have hPi0 : 0 <= Real.pi / 2 := by positivity
  have hBound :
      Real.log C + 2 * Real.log U + Real.pi * ((T : Real) + 1) / 2 <=
        (2 + Real.pi / 2 + max 0 (Real.log C)) * U := by
    calc
      Real.log C + 2 * Real.log U + Real.pi * ((T : Real) + 1) / 2 <=
        max 0 (Real.log C) + 2 * U + Real.pi * U / 2 := by
          gcongr
      _ <= (2 + Real.pi / 2 + max 0 (Real.log C)) * U := by
        nlinarith
  exact hBound.trans_lt (by
    have hUPos : 0 < U := lt_of_lt_of_le zero_lt_one hU
    nlinarith)

theorem centeredCompletionLog_re_lt_closedEnvelope
    {T : Nat} {c z : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hcImLower : 1 <= |c.im|)
    (hcImUpper : |c.im| <= (T : Real) + 1)
    (hcNorm : norm c <= (T : Real) + 3)
    (hz : Membership.mem (Metric.ball c completionLocalRadius) z) :
    (centeredCompletionLog c hcImLower z).re <
      completionClosedRealPartEnvelope T := by
  have hExpEq := congrArg norm (exp_centeredCompletionLog_eq_ratio hcImLower hz)
  have hExp : Real.exp (centeredCompletionLog c hcImLower z).re =
      norm (TS290.Goldbach.xiZetaLocalMultiplier z /
        TS290.Goldbach.xiZetaLocalMultiplier c) := by
    simpa [Complex.norm_eq_abs, Complex.abs_exp] using hExpEq
  have hRatio := xiZetaLocalMultiplier_norm_ratio_le
    hcRe hcImLower hcImUpper hcNorm (Metric.mem_ball.mp hz).le
  have hRe : (centeredCompletionLog c hcImLower z).re <=
      Real.log (completionValueRatioMajorant T) := by
    apply (Real.le_log_iff_exp_le (completionValueRatioMajorant_pos T)).mpr
    simpa [hExp] using hRatio
  exact hRe.trans_lt (log_completionValueRatioMajorant_lt_closedEnvelope T)

theorem xiZetaCompletionLogDerivative_norm_le_general
    {T : Nat} {c : Complex}
    (hcRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
    (hcImLower : 1 <= |c.im|)
    (hcImUpper : |c.im| <= (T : Real) + 1)
    (hcNorm : norm c <= (T : Real) + 3) :
    norm (TS297.Goldbach.xiZetaCompletionLogDerivative c) <=
      16 * completionClosedRealPartEnvelope T := by
  let L : Complex -> Complex := centeredCompletionLog c hcImLower
  have hHalfPos : 0 < completionLocalRadius / 2 := by
    unfold completionLocalRadius
    norm_num
  have hHalfLt : completionLocalRadius / 2 < completionLocalRadius := by
    linarith [completionLocalRadius_pos]
  have hDiffOn : DifferentiableOn Complex L
      (Metric.ball c completionLocalRadius) :=
    centeredCompletionLog_differentiableOn hcImLower
  have hDiffCont : DiffContOnCl Complex L
      (Metric.ball c (completionLocalRadius / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    rw [closure_ball c hHalfPos.ne'] at hz
    have hzBig : Membership.mem (Metric.ball c completionLocalRadius) z :=
      Metric.closedBall_subset_ball hHalfLt hz
    exact (hDiffOn.differentiableAt
      (Metric.isOpen_ball.mem_nhds hzBig)).differentiableWithinAt
  have hSphere : forall z : Complex,
      Membership.mem (Metric.sphere c (completionLocalRadius / 2)) z ->
      norm (L z) <= 2 * completionClosedRealPartEnvelope T := by
    intro z hz
    let f : Complex -> Complex := fun w => L (c + w)
    have hfDiff : DifferentiableOn Complex f
        (Metric.ball 0 completionLocalRadius) := by
      intro w hw
      have hcw : Membership.mem (Metric.ball c completionLocalRadius) (c + w) := by
        simpa [Metric.mem_ball, dist_eq] using hw
      have hLAt : DifferentiableAt Complex L (c + w) :=
        hDiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds hcw)
      exact (hLAt.comp w
        ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
    have hfMaps : MapsTo f (Metric.ball 0 completionLocalRadius)
        {u | u.re < completionClosedRealPartEnvelope T} := by
      intro w hw
      apply centeredCompletionLog_re_lt_closedEnvelope
        hcRe hcImLower hcImUpper hcNorm
      simpa [Metric.mem_ball, dist_eq] using hw
    have hfZero : f 0 = 0 := by simp [f, L]
    have hw : Membership.mem (Metric.ball 0 completionLocalRadius) (z - c) := by
      have hzNorm : norm (z - c) = completionLocalRadius / 2 := by
        have hz' := Metric.mem_sphere.mp hz
        simpa [dist_eq] using hz'
      simpa [Metric.mem_ball, dist_eq, hzNorm] using hHalfLt
    have hBC := TS300.Goldbach.centered_borelCaratheodory_zero
      (completionClosedRealPartEnvelope_pos T) hfDiff hfMaps
      completionLocalRadius_pos hw hfZero
    have hzNorm : norm (z - c) = completionLocalRadius / 2 := by
      have hz' := Metric.mem_sphere.mp hz
      simpa [dist_eq] using hz'
    have hBC' : norm (L z) <=
        2 * completionClosedRealPartEnvelope T *
          (completionLocalRadius / 2) /
            (completionLocalRadius - completionLocalRadius / 2) := by
      simpa [f, Complex.norm_eq_abs, hzNorm] using hBC
    exact hBC'.trans_eq (by
      unfold completionLocalRadius
      ring)
  have hCauchy : norm (deriv L c) <=
      (2 * completionClosedRealPartEnvelope T) /
        (completionLocalRadius / 2) :=
    norm_deriv_le_of_forall_mem_sphere_norm_le hHalfPos hDiffCont hSphere
  rw [deriv_centeredCompletionLog_center hcImLower] at hCauchy
  apply hCauchy.trans_eq
  unfold completionLocalRadius
  ring

theorem finiteGridTop_center_geometry
    (T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    let c := TS300.Goldbach.finiteGridTopHorizontalPoint T sigma
    And (Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
      (And (1 <= |c.im|)
        (And (|c.im| <= (T : Real) + 1) (norm c <= (T : Real) + 3))) := by
  dsimp
  have hTauPos := TS299.Goldbach.finiteGridStrongTau_pos hT
  have hTauGt := TS299.Goldbach.finiteGridStrongTau_gt T
  have hTauLt := TS299.Goldbach.finiteGridStrongTau_lt T
  have hSigmaAbs : |sigma| <= 2 := by
    rw [abs_le]
    norm_num [TS294.Goldbach.fixedPerronLeft,
      TS294.Goldbach.fixedPerronRight] at hSigma
    constructor <;> linarith
  have hNorm := Complex.abs_le_abs_re_add_abs_im
    (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)
  simp [TS300.Goldbach.finiteGridTopHorizontalPoint,
    abs_of_pos hTauPos] at hNorm
  have hOne : (1 : Real) <= (T : Real) := by exact_mod_cast hT
  have hRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2)
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma).re := by
    simpa [TS300.Goldbach.finiteGridTopHorizontalPoint,
      TS294.Goldbach.fixedPerronLeft,
      TS294.Goldbach.fixedPerronRight] using hSigma
  have hImLower : 1 <=
      |(TS300.Goldbach.finiteGridTopHorizontalPoint T sigma).im| := by
    simp [TS300.Goldbach.finiteGridTopHorizontalPoint, abs_of_pos hTauPos]
    linarith
  have hImUpper :
      |(TS300.Goldbach.finiteGridTopHorizontalPoint T sigma).im| <=
        (T : Real) + 1 := by
    simp [TS300.Goldbach.finiteGridTopHorizontalPoint, abs_of_pos hTauPos]
    exact le_of_lt hTauLt
  have hNorm' : norm (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) <=
      (T : Real) + 3 := by
    rw [Complex.norm_eq_abs]
    calc
      Complex.abs (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) <=
          |sigma| + TS299.Goldbach.finiteGridStrongTau T := hNorm
      _ <= 2 + ((T : Real) + 1) :=
        add_le_add hSigmaAbs (le_of_lt hTauLt)
      _ = (T : Real) + 3 := by ring
  exact And.intro hRe (And.intro hImLower (And.intro hImUpper hNorm'))

theorem finiteGridBottom_center_geometry
    (T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    let c := TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma
    And (Membership.mem (Set.Icc (-3 / 2 : Real) 2) c.re)
      (And (1 <= |c.im|)
        (And (|c.im| <= (T : Real) + 1) (norm c <= (T : Real) + 3))) := by
  dsimp
  have hTauPos := TS299.Goldbach.finiteGridStrongTau_pos hT
  have hTauGt := TS299.Goldbach.finiteGridStrongTau_gt T
  have hTauLt := TS299.Goldbach.finiteGridStrongTau_lt T
  have hSigmaAbs : |sigma| <= 2 := by
    rw [abs_le]
    norm_num [TS294.Goldbach.fixedPerronLeft,
      TS294.Goldbach.fixedPerronRight] at hSigma
    constructor <;> linarith
  have hNorm := Complex.abs_le_abs_re_add_abs_im
    (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)
  simp [TS300.Goldbach.finiteGridBottomHorizontalPoint,
    abs_of_pos hTauPos] at hNorm
  have hOne : (1 : Real) <= (T : Real) := by exact_mod_cast hT
  have hRe : Membership.mem (Set.Icc (-3 / 2 : Real) 2)
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma).re := by
    simpa [TS300.Goldbach.finiteGridBottomHorizontalPoint,
      TS294.Goldbach.fixedPerronLeft,
      TS294.Goldbach.fixedPerronRight] using hSigma
  have hImLower : 1 <=
      |(TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma).im| := by
    simp [TS300.Goldbach.finiteGridBottomHorizontalPoint, abs_of_pos hTauPos]
    linarith
  have hImUpper :
      |(TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma).im| <=
        (T : Real) + 1 := by
    simp [TS300.Goldbach.finiteGridBottomHorizontalPoint, abs_of_pos hTauPos]
    exact le_of_lt hTauLt
  have hNorm' : norm (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) <=
      (T : Real) + 3 := by
    rw [Complex.norm_eq_abs]
    calc
      Complex.abs (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) <=
          |sigma| + TS299.Goldbach.finiteGridStrongTau T := hNorm
      _ <= 2 + ((T : Real) + 1) :=
        add_le_add hSigmaAbs (le_of_lt hTauLt)
      _ = (T : Real) + 3 := by ring
  exact And.intro hRe (And.intro hImLower (And.intro hImUpper hNorm'))

noncomputable def completionClosedLogDerivativeEnvelope (T : Nat) : Real :=
  16 * completionClosedRealPartEnvelope T

theorem xiZetaCompletionLogDerivative_norm_le_top
    (T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (TS297.Goldbach.xiZetaCompletionLogDerivative
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      completionClosedLogDerivativeEnvelope T := by
  have hGeom := finiteGridTop_center_geometry T hT sigma hSigma
  have hRe := hGeom.1
  have hImLower := hGeom.2.1
  have hImUpper := hGeom.2.2.1
  have hNorm := hGeom.2.2.2
  exact xiZetaCompletionLogDerivative_norm_le_general
    hRe hImLower hImUpper hNorm

theorem xiZetaCompletionLogDerivative_norm_le_bottom
    (T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (TS297.Goldbach.xiZetaCompletionLogDerivative
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      completionClosedLogDerivativeEnvelope T := by
  have hGeom := finiteGridBottom_center_geometry T hT sigma hSigma
  have hRe := hGeom.1
  have hImLower := hGeom.2.1
  have hImUpper := hGeom.2.2.1
  have hNorm := hGeom.2.2.2
  exact xiZetaCompletionLogDerivative_norm_le_general
    hRe hImLower hImUpper hNorm

/-! ## Exact finite-grid horizontal logarithmic-derivative bound -/

noncomputable def finiteGridClosedHorizontalLogDerivativeEnvelope
    (T : Nat) : Real :=
  completionClosedLogDerivativeEnvelope T +
    TS299.Goldbach.finiteGridClosedLoadEnvelope T +
      TS303.Goldbach.xiMacroscopicClosedLogDerivativeEnvelope T +
        TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T

theorem finiteGridClosedHorizontalLogDerivativeEnvelope_nonnegative
    (T : Nat) (hT : 1 <= T) :
    0 <= finiteGridClosedHorizontalLogDerivativeEnvelope T := by
  unfold finiteGridClosedHorizontalLogDerivativeEnvelope
  have hCompletion : 0 <= completionClosedLogDerivativeEnvelope T := by
    unfold completionClosedLogDerivativeEnvelope
    exact mul_nonneg (by norm_num) (completionClosedRealPartEnvelope_pos T).le
  have hLoad := TS300.Goldbach.finiteGridClosedLoadEnvelope_nonnegative T hT
  have hMacro :=
    TS303.Goldbach.xiMacroscopicClosedLogDerivativeEnvelope_nonnegative T
  have hCorrection :=
    TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope_nonnegative T
  positivity

theorem neg_riemannZeta_logDerivative_norm_le_finiteGrid_top
    (T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm
        (-deriv riemannZeta
            (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
          riemannZeta
            (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      finiteGridClosedHorizontalLogDerivativeEnvelope T := by
  let s := TS300.Goldbach.finiteGridTopHorizontalPoint T sigma
  have hIm : Not (s.im = 0) := by
    dsimp [s]
    simp [TS300.Goldbach.finiteGridTopHorizontalPoint,
      ne_of_gt (TS299.Goldbach.finiteGridStrongTau_pos hT)]
  have hZeta : Not (riemannZeta s = 0) := by
    exact TS299.Goldbach.riemannZeta_ne_zero_on_finiteGridStrong_top
      T hT sigma hSigma.1 hSigma.2
  have hXi : Not (TS282.Goldbach.riemannXiCandidate s = 0) := by
    simpa [s] using
      TS301.Goldbach.riemannXiCandidate_ne_zero_at_finiteGridTop
        T hT sigma hSigma
  have hPolynomial : Not (TS296.Goldbach.heightZeroPolynomial T s = 0) := by
    simpa [s] using
      TS301.Goldbach.heightZeroPolynomial_ne_zero_at_finiteGridTop T hT sigma
  have hAvoid : forall rho : TS292.Goldbach.ConcreteNontrivialZero,
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho ->
        Not (s = rho.1) := by
    simpa [s] using TS301.Goldbach.finiteGridTop_avoids_heightZeros T hT sigma
  have hXiIdentity := TS296.Goldbach.heightXiQuotient_logDerivative_identity
    T s hXi hPolynomial hAvoid
  have hMacroBridge :=
    TS301.Goldbach.heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection_top
      T hT sigma hSigma
  have hExact :
      -deriv riemannZeta s / riemannZeta s =
        TS297.Goldbach.xiZetaCompletionLogDerivative s -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T s +
            (deriv (TS301.Goldbach.xiMacroscopicQuotient T) s /
                TS301.Goldbach.xiMacroscopicQuotient T s +
              TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s)) := by
    calc
      -deriv riemannZeta s / riemannZeta s =
          TS297.Goldbach.xiZetaCompletionLogDerivative s -
            deriv TS282.Goldbach.riemannXiCandidate s /
              TS282.Goldbach.riemannXiCandidate s :=
        TS297.Goldbach.neg_riemannZeta_logDerivative_eq_completion_sub_xi
          hIm hZeta
      _ = TS297.Goldbach.xiZetaCompletionLogDerivative s -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T s +
            deriv (TS296.Goldbach.heightXiQuotient T) s /
              TS296.Goldbach.heightXiQuotient T s) := by rw [hXiIdentity]
      _ = _ := by
        simpa [s] using
          (congrArg
            (fun q : Complex =>
              TS297.Goldbach.xiZetaCompletionLogDerivative s -
                (TS295.Goldbach.finiteZeroLogDerivativeSum T s + q))
            hMacroBridge)
  change norm (-deriv riemannZeta s / riemannZeta s) <= _
  rw [hExact]
  have hLoad :
      norm (TS295.Goldbach.finiteZeroLogDerivativeSum T s) <=
        TS299.Goldbach.finiteGridClosedLoadEnvelope T := by
    have hRaw := TS295.Goldbach.finiteZeroLogDerivativeSum_norm_le_reciprocalLoad_top
      (TS299.Goldbach.finiteGridStrongPerronContourData T hT) sigma
    have hClosed := TS299.Goldbach.finiteGridStrongLoad_le_closed T hT
    have hRaw' :
        norm (TS295.Goldbach.finiteZeroLogDerivativeSum T s) <=
          TS295.Goldbach.reciprocalZeroLoad T
            (TS299.Goldbach.finiteGridStrongTau T) := by
      simpa [s, TS299.Goldbach.finiteGridStrongPerronContourData,
        TS300.Goldbach.finiteGridTopHorizontalPoint] using hRaw
    exact hRaw'.trans hClosed
  have hCompletion := xiZetaCompletionLogDerivative_norm_le_top T hT sigma hSigma
  have hMacro :=
    TS303.Goldbach.xiMacroscopicQuotient_logDerivative_norm_le_linear_top
      T sigma hSigma
  have hCorrection :=
    TS302.Goldbach.xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_top
      T hT sigma
  unfold finiteGridClosedHorizontalLogDerivativeEnvelope
  calc
    norm
        (TS297.Goldbach.xiZetaCompletionLogDerivative s -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T s +
            (deriv (TS301.Goldbach.xiMacroscopicQuotient T) s /
                TS301.Goldbach.xiMacroscopicQuotient T s +
              TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s))) <=
      norm (TS297.Goldbach.xiZetaCompletionLogDerivative s) +
        (norm (TS295.Goldbach.finiteZeroLogDerivativeSum T s) +
          (norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T) s /
              TS301.Goldbach.xiMacroscopicQuotient T s) +
            norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s))) := by
      exact (norm_sub_le _ _).trans
        (add_le_add_left
          ((norm_add_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)) _)
    _ <= completionClosedLogDerivativeEnvelope T +
        (TS299.Goldbach.finiteGridClosedLoadEnvelope T +
          (TS303.Goldbach.xiMacroscopicClosedLogDerivativeEnvelope T +
            TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T)) := by
      exact add_le_add hCompletion
        (add_le_add hLoad (add_le_add hMacro hCorrection))
    _ = _ := by ring

theorem neg_riemannZeta_logDerivative_norm_le_finiteGrid_bottom
    (T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm
        (-deriv riemannZeta
            (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
          riemannZeta
            (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      finiteGridClosedHorizontalLogDerivativeEnvelope T := by
  let s := TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma
  have hIm : Not (s.im = 0) := by
    dsimp [s]
    simp [TS300.Goldbach.finiteGridBottomHorizontalPoint,
      ne_of_gt (TS299.Goldbach.finiteGridStrongTau_pos hT)]
  have hZeta : Not (riemannZeta s = 0) := by
    exact TS299.Goldbach.riemannZeta_ne_zero_on_finiteGridStrong_bottom
      T hT sigma hSigma.1 hSigma.2
  have hXi : Not (TS282.Goldbach.riemannXiCandidate s = 0) := by
    simpa [s] using
      TS301.Goldbach.riemannXiCandidate_ne_zero_at_finiteGridBottom
        T hT sigma hSigma
  have hPolynomial : Not (TS296.Goldbach.heightZeroPolynomial T s = 0) := by
    simpa [s] using
      TS301.Goldbach.heightZeroPolynomial_ne_zero_at_finiteGridBottom T hT sigma
  have hAvoid : forall rho : TS292.Goldbach.ConcreteNontrivialZero,
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho ->
        Not (s = rho.1) := by
    simpa [s] using TS301.Goldbach.finiteGridBottom_avoids_heightZeros T hT sigma
  have hXiIdentity := TS296.Goldbach.heightXiQuotient_logDerivative_identity
    T s hXi hPolynomial hAvoid
  have hMacroBridge :=
    TS301.Goldbach.heightXiQuotient_logDerivative_eq_macroscopic_add_finiteCorrection_bottom
      T hT sigma hSigma
  have hExact :
      -deriv riemannZeta s / riemannZeta s =
        TS297.Goldbach.xiZetaCompletionLogDerivative s -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T s +
            (deriv (TS301.Goldbach.xiMacroscopicQuotient T) s /
                TS301.Goldbach.xiMacroscopicQuotient T s +
              TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s)) := by
    calc
      -deriv riemannZeta s / riemannZeta s =
          TS297.Goldbach.xiZetaCompletionLogDerivative s -
            deriv TS282.Goldbach.riemannXiCandidate s /
              TS282.Goldbach.riemannXiCandidate s :=
        TS297.Goldbach.neg_riemannZeta_logDerivative_eq_completion_sub_xi
          hIm hZeta
      _ = TS297.Goldbach.xiZetaCompletionLogDerivative s -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T s +
            deriv (TS296.Goldbach.heightXiQuotient T) s /
              TS296.Goldbach.heightXiQuotient T s) := by rw [hXiIdentity]
      _ = _ := by
        simpa [s] using
          (congrArg
            (fun q : Complex =>
              TS297.Goldbach.xiZetaCompletionLogDerivative s -
                (TS295.Goldbach.finiteZeroLogDerivativeSum T s + q))
            hMacroBridge)
  change norm (-deriv riemannZeta s / riemannZeta s) <= _
  rw [hExact]
  have hLoad :
      norm (TS295.Goldbach.finiteZeroLogDerivativeSum T s) <=
        TS299.Goldbach.finiteGridClosedLoadEnvelope T := by
    have hRaw := TS295.Goldbach.finiteZeroLogDerivativeSum_norm_le_reciprocalLoad_bottom
      (TS299.Goldbach.finiteGridStrongPerronContourData T hT) sigma
    have hClosed := TS299.Goldbach.finiteGridStrongLoad_le_closed T hT
    have hRaw' :
        norm (TS295.Goldbach.finiteZeroLogDerivativeSum T s) <=
          TS295.Goldbach.reciprocalZeroLoad T
            (TS299.Goldbach.finiteGridStrongTau T) := by
      simpa [s, TS299.Goldbach.finiteGridStrongPerronContourData,
        TS300.Goldbach.finiteGridBottomHorizontalPoint] using hRaw
    exact hRaw'.trans hClosed
  have hCompletion := xiZetaCompletionLogDerivative_norm_le_bottom T hT sigma hSigma
  have hMacro :=
    TS303.Goldbach.xiMacroscopicQuotient_logDerivative_norm_le_linear_bottom
      T sigma hSigma
  have hCorrection :=
    TS302.Goldbach.xiMacroscopicHeightFiniteCorrection_norm_le_closedEnvelope_bottom
      T hT sigma
  unfold finiteGridClosedHorizontalLogDerivativeEnvelope
  calc
    norm
        (TS297.Goldbach.xiZetaCompletionLogDerivative s -
          (TS295.Goldbach.finiteZeroLogDerivativeSum T s +
            (deriv (TS301.Goldbach.xiMacroscopicQuotient T) s /
                TS301.Goldbach.xiMacroscopicQuotient T s +
              TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s))) <=
      norm (TS297.Goldbach.xiZetaCompletionLogDerivative s) +
        (norm (TS295.Goldbach.finiteZeroLogDerivativeSum T s) +
          (norm (deriv (TS301.Goldbach.xiMacroscopicQuotient T) s /
              TS301.Goldbach.xiMacroscopicQuotient T s) +
            norm (TS301.Goldbach.xiMacroscopicHeightFiniteCorrection T s))) := by
      exact (norm_sub_le _ _).trans
        (add_le_add_left
          ((norm_add_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)) _)
    _ <= completionClosedLogDerivativeEnvelope T +
        (TS299.Goldbach.finiteGridClosedLoadEnvelope T +
          (TS303.Goldbach.xiMacroscopicClosedLogDerivativeEnvelope T +
            TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope T)) := by
      exact add_le_add hCompletion
        (add_le_add hLoad (add_le_add hMacro hCorrection))
    _ = _ := by ring

/-! ## Closed decay and the complete horizontal Perron sides -/

noncomputable def completionClosedLogDerivativeDecayEnvelope (T : Nat) : Real :=
  80 * completionClosedEnvelopeConstant / (T : Real)

theorem completionClosedLogDerivativeEnvelope_div_sq_le_decay
    (T : Nat) (hT : 1 <= T) :
    completionClosedLogDerivativeEnvelope T / (T : Real) ^ 2 <=
      completionClosedLogDerivativeDecayEnvelope T := by
  have hTR : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hRatio : ((T : Real) + 4) / (T : Real) ^ 2 <= 5 / (T : Real) := by
    have hTone : 1 <= (T : Real) := by exact_mod_cast hT
    have hNumerator : ((T : Real) + 4) / (T : Real) <= 5 := by
      calc
        ((T : Real) + 4) / (T : Real) <=
            (5 * (T : Real)) / (T : Real) :=
          div_le_div_of_nonneg_right (by nlinarith) hTR.le
        _ = 5 := by field_simp [hTR.ne']
    rw [show (T : Real) ^ 2 = (T : Real) * (T : Real) by ring]
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hNumerator hTR.le
  unfold completionClosedLogDerivativeEnvelope
    completionClosedRealPartEnvelope completionClosedLogDerivativeDecayEnvelope
  calc
    16 * (completionClosedEnvelopeConstant * ((T : Real) + 4)) /
        (T : Real) ^ 2 =
      (16 * completionClosedEnvelopeConstant) *
        (((T : Real) + 4) / (T : Real) ^ 2) := by ring
    _ <= (16 * completionClosedEnvelopeConstant) * (5 / (T : Real)) :=
      mul_le_mul_of_nonneg_left hRatio
        (mul_nonneg (by norm_num) completionClosedEnvelopeConstant_pos.le)
    _ = 80 * completionClosedEnvelopeConstant / (T : Real) := by ring

theorem completionClosedLogDerivativeDecayEnvelope_tendsto_zero :
    Tendsto completionClosedLogDerivativeDecayEnvelope atTop (nhds 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul
    (80 * completionClosedEnvelopeConstant)
  convert h using 1
  case h.e'_3 =>
    funext T
    unfold completionClosedLogDerivativeDecayEnvelope
    ring
  case h.e'_5 => ring

theorem completionClosedLogDerivativeEnvelope_div_sq_tendsto_zero :
    Tendsto
      (fun T : Nat =>
        completionClosedLogDerivativeEnvelope T / (T : Real) ^ 2)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    completionClosedLogDerivativeDecayEnvelope_tendsto_zero
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg
      (mul_nonneg (by norm_num) (completionClosedRealPartEnvelope_pos T).le)
      (sq_nonneg (T : Real))
  next =>
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact completionClosedLogDerivativeEnvelope_div_sq_le_decay T hT

theorem finiteGridClosedHorizontalLogDerivativeEnvelope_div_sq_tendsto_zero :
    Tendsto
      (fun T : Nat =>
        finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2)
      atTop (nhds 0) := by
  have hCompletion := completionClosedLogDerivativeEnvelope_div_sq_tendsto_zero
  have hLoad := TS300.Goldbach.finiteGridClosedLoad_div_sq_tendsto_zero
  have hMacro :=
    TS303.Goldbach.xiMacroscopicClosedLogDerivativeEnvelope_div_sq_tendsto_zero
  have hCorrection :=
    TS302.Goldbach.xiMacroscopicCorrectionCountEnvelope_div_sq_tendsto_zero
  have hTotal := hCompletion.add (hLoad.add (hMacro.add hCorrection))
  convert hTotal using 1
  case h.e'_3 =>
    funext T
    unfold finiteGridClosedHorizontalLogDerivativeEnvelope
    ring
  case h.e'_5 => ring

noncomputable def finiteGridCompleteHorizontalComponent
    (x T : Nat) : Real :=
  (7 / 2 : Real) * TS298.Goldbach.rightLineScale x *
    (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2)

theorem finiteGridCompleteHorizontalComponent_nonnegative
    (x T : Nat) (hT : 1 <= T) :
    0 <= finiteGridCompleteHorizontalComponent x T := by
  unfold finiteGridCompleteHorizontalComponent
  exact mul_nonneg
    (mul_nonneg (by norm_num) (TS298.Goldbach.rightLineScale_nonnegative x))
    (div_nonneg
      (finiteGridClosedHorizontalLogDerivativeEnvelope_nonnegative T hT)
      (sq_nonneg (T : Real)))

theorem finiteGridCompleteHorizontalComponent_tendsto_zero
    (x : Nat) :
    Tendsto (finiteGridCompleteHorizontalComponent x) atTop (nhds 0) := by
  unfold finiteGridCompleteHorizontalComponent
  simpa using
    finiteGridClosedHorizontalLogDerivativeEnvelope_div_sq_tendsto_zero.const_mul
      ((7 / 2 : Real) * TS298.Goldbach.rightLineScale x)

theorem triangleSplinePerronIntegrand_norm_le_finiteGrid_top
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (TS293.Goldbach.triangleSplinePerronIntegrand x
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      TS298.Goldbach.rightLineScale x *
        (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hSq : (T : Real) ^ 2 <=
      (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
  have hInv : 1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
      1 / (T : Real) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hTPos) hSq
  have hEnvelope0 :=
    finiteGridClosedHorizontalLogDerivativeEnvelope_nonnegative T hT
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
  simp only [norm_mul]
  calc
    norm (-deriv riemannZeta
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma) /
        riemannZeta (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
        norm ((x : Complex) ^
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) *
        norm (TS257.Goldbach.triangleSplineMellinKernel
          (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma)) <=
      finiteGridClosedHorizontalLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst := mul_le_mul
        (neg_riemannZeta_logDerivative_norm_le_finiteGrid_top T hT sigma hSigma)
        (TS300.Goldbach.nat_cpow_finiteGridTop_norm_le_rightLineScale
          x T hT sigma hSigma.2)
        (norm_nonneg _) hEnvelope0
      exact mul_le_mul hFirst
        (TS300.Goldbach.triangleSplineMellinKernel_finiteGridTop_norm_le
          T hT sigma)
        (norm_nonneg _) (mul_nonneg hEnvelope0 hScale0)
    _ <= finiteGridClosedHorizontalLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hInv (mul_nonneg hEnvelope0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
        (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2) := by
      ring

theorem triangleSplinePerronIntegrand_norm_le_finiteGrid_bottom
    (x T : Nat) (hT : 1 <= T) (sigma : Real)
    (hSigma : Membership.mem
      (Set.Icc TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight)
      sigma) :
    norm (TS293.Goldbach.triangleSplinePerronIntegrand x
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      TS298.Goldbach.rightLineScale x *
        (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2) := by
  have hTau : (T : Real) <= TS299.Goldbach.finiteGridStrongTau T :=
    (TS299.Goldbach.finiteGridStrongTau_gt T).le
  have hTPos : 0 < (T : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have hSq : (T : Real) ^ 2 <=
      (TS299.Goldbach.finiteGridStrongTau T) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hTPos.le hTau
  have hInv : 1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2 <=
      1 / (T : Real) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hTPos) hSq
  have hEnvelope0 :=
    finiteGridClosedHorizontalLogDerivativeEnvelope_nonnegative T hT
  have hScale0 := TS298.Goldbach.rightLineScale_nonnegative x
  unfold TS293.Goldbach.triangleSplinePerronIntegrand
  simp only [norm_mul]
  calc
    norm (-deriv riemannZeta
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma) /
        riemannZeta (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
        norm ((x : Complex) ^
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) *
        norm (TS257.Goldbach.triangleSplineMellinKernel
          (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma)) <=
      finiteGridClosedHorizontalLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x *
          (1 / (TS299.Goldbach.finiteGridStrongTau T) ^ 2) := by
      have hFirst := mul_le_mul
        (neg_riemannZeta_logDerivative_norm_le_finiteGrid_bottom T hT sigma hSigma)
        (TS300.Goldbach.nat_cpow_finiteGridBottom_norm_le_rightLineScale
          x T hT sigma hSigma.2)
        (norm_nonneg _) hEnvelope0
      exact mul_le_mul hFirst
        (TS300.Goldbach.triangleSplineMellinKernel_finiteGridBottom_norm_le
          T hT sigma)
        (norm_nonneg _) (mul_nonneg hEnvelope0 hScale0)
    _ <= finiteGridClosedHorizontalLogDerivativeEnvelope T *
        TS298.Goldbach.rightLineScale x * (1 / (T : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hInv (mul_nonneg hEnvelope0 hScale0)
    _ = TS298.Goldbach.rightLineScale x *
        (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2) := by
      ring

theorem finiteGridPerronTopIntegral_norm_le_complete
    (x T : Nat) (hT : 1 <= T) :
    norm (TS293.Goldbach.perronTopForwardIntegral x
      (TS299.Goldbach.finiteGridStrongPerronContourData T hT).toPerronRectangle) <=
      finiteGridCompleteHorizontalComponent x T := by
  have hSide := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := TS294.Goldbach.fixedPerronLeft)
    (b := TS294.Goldbach.fixedPerronRight)
    (f := fun sigma : Real =>
      TS293.Goldbach.triangleSplinePerronIntegrand x
        (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma))
    (C := TS298.Goldbach.rightLineScale x *
      (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2))
    (by
      intro sigma hSigma
      have hOrder : TS294.Goldbach.fixedPerronLeft <=
          TS294.Goldbach.fixedPerronRight := by
        norm_num [TS294.Goldbach.fixedPerronLeft,
          TS294.Goldbach.fixedPerronRight]
      have hIoc : Membership.mem
          (Set.Ioc TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight) sigma := by
        simpa [Set.uIoc_of_le hOrder] using hSigma
      exact triangleSplinePerronIntegrand_norm_le_finiteGrid_top
        x T hT sigma (Set.Ioc_subset_Icc_self hIoc))
  change norm (intervalIntegral
    (fun sigma : Real => TS293.Goldbach.triangleSplinePerronIntegrand x
      (TS300.Goldbach.finiteGridTopHorizontalPoint T sigma))
    TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight
    (volume : Measure Real)) <= _
  have hWidth :
      |TS294.Goldbach.fixedPerronRight - TS294.Goldbach.fixedPerronLeft| =
        (7 / 2 : Real) := by
    norm_num [TS294.Goldbach.fixedPerronRight,
      TS294.Goldbach.fixedPerronLeft]
  rw [hWidth] at hSide
  unfold finiteGridCompleteHorizontalComponent
  nlinarith

theorem finiteGridPerronBottomIntegral_norm_le_complete
    (x T : Nat) (hT : 1 <= T) :
    norm (TS293.Goldbach.perronBottomIntegral x
      (TS299.Goldbach.finiteGridStrongPerronContourData T hT).toPerronRectangle) <=
      finiteGridCompleteHorizontalComponent x T := by
  have hSide := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := TS294.Goldbach.fixedPerronLeft)
    (b := TS294.Goldbach.fixedPerronRight)
    (f := fun sigma : Real =>
      TS293.Goldbach.triangleSplinePerronIntegrand x
        (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma))
    (C := TS298.Goldbach.rightLineScale x *
      (finiteGridClosedHorizontalLogDerivativeEnvelope T / (T : Real) ^ 2))
    (by
      intro sigma hSigma
      have hOrder : TS294.Goldbach.fixedPerronLeft <=
          TS294.Goldbach.fixedPerronRight := by
        norm_num [TS294.Goldbach.fixedPerronLeft,
          TS294.Goldbach.fixedPerronRight]
      have hIoc : Membership.mem
          (Set.Ioc TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight) sigma := by
        simpa [Set.uIoc_of_le hOrder] using hSigma
      exact triangleSplinePerronIntegrand_norm_le_finiteGrid_bottom
        x T hT sigma (Set.Ioc_subset_Icc_self hIoc))
  change norm (intervalIntegral
    (fun sigma : Real => TS293.Goldbach.triangleSplinePerronIntegrand x
      (TS300.Goldbach.finiteGridBottomHorizontalPoint T sigma))
    TS294.Goldbach.fixedPerronLeft TS294.Goldbach.fixedPerronRight
    (volume : Measure Real)) <= _
  have hWidth :
      |TS294.Goldbach.fixedPerronRight - TS294.Goldbach.fixedPerronLeft| =
        (7 / 2 : Real) := by
    norm_num [TS294.Goldbach.fixedPerronRight,
      TS294.Goldbach.fixedPerronLeft]
  rw [hWidth] at hSide
  unfold finiteGridCompleteHorizontalComponent
  nlinarith

noncomputable def finiteGridCanonicalTopHorizontalIntegral
    (x T : Nat) : Complex :=
  TS293.Goldbach.perronTopForwardIntegral x
    (TS299.Goldbach.finiteGridStrongPerronContourData (T + 1) (by omega)).toPerronRectangle

noncomputable def finiteGridCanonicalBottomHorizontalIntegral
    (x T : Nat) : Complex :=
  TS293.Goldbach.perronBottomIntegral x
    (TS299.Goldbach.finiteGridStrongPerronContourData (T + 1) (by omega)).toPerronRectangle

theorem finiteGridCanonicalTopHorizontalIntegral_norm_le
    (x T : Nat) :
    norm (finiteGridCanonicalTopHorizontalIntegral x T) <=
      finiteGridCompleteHorizontalComponent x (T + 1) := by
  unfold finiteGridCanonicalTopHorizontalIntegral
  exact finiteGridPerronTopIntegral_norm_le_complete x (T + 1) (by omega)

theorem finiteGridCanonicalBottomHorizontalIntegral_norm_le
    (x T : Nat) :
    norm (finiteGridCanonicalBottomHorizontalIntegral x T) <=
      finiteGridCompleteHorizontalComponent x (T + 1) := by
  unfold finiteGridCanonicalBottomHorizontalIntegral
  exact finiteGridPerronBottomIntegral_norm_le_complete x (T + 1) (by omega)

theorem finiteGridCanonicalTopHorizontalIntegral_tendsto_zero
    (x : Nat) :
    Tendsto (finiteGridCanonicalTopHorizontalIntegral x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_
    ((finiteGridCompleteHorizontalComponent_tendsto_zero x).comp
      (tendsto_add_atTop_nat 1))
  next =>
    exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  next =>
    exact Filter.Eventually.of_forall
      (finiteGridCanonicalTopHorizontalIntegral_norm_le x)

theorem finiteGridCanonicalBottomHorizontalIntegral_tendsto_zero
    (x : Nat) :
    Tendsto (finiteGridCanonicalBottomHorizontalIntegral x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_
    ((finiteGridCompleteHorizontalComponent_tendsto_zero x).comp
      (tendsto_add_atTop_nat 1))
  next =>
    exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  next =>
    exact Filter.Eventually.of_forall
      (finiteGridCanonicalBottomHorizontalIntegral_norm_le x)

theorem finiteGridCanonicalHorizontalPair_tendsto_zero
    (x : Nat) :
    Tendsto
      (fun T : Nat =>
        finiteGridCanonicalBottomHorizontalIntegral x T -
          finiteGridCanonicalTopHorizontalIntegral x T)
      atTop (nhds 0) := by
  simpa using
    (finiteGridCanonicalBottomHorizontalIntegral_tendsto_zero x).sub
      (finiteGridCanonicalTopHorizontalIntegral_tendsto_zero x)

/-! ## Audit ledger -/

structure ClosedCompletionCorrectionAndHorizontalDecayLedger where
  gamma_compact_upper_bound_proved : Prop
  gamma_reflection_lower_bound_proved : Prop
  completion_multiplier_upper_bound_proved : Prop
  completion_multiplier_center_lower_bound_proved : Prop
  centered_completion_log_constructed : Prop
  completion_real_part_envelope_closed : Prop
  completion_log_derivative_linear_bound_proved : Prop
  finite_grid_exact_zeta_decomposition_proved : Prop
  complete_horizontal_pointwise_bound_proved : Prop
  complete_top_integral_decay_proved : Prop
  complete_bottom_integral_decay_proved : Prop
  fixed_left_boundary_not_proved : Prop
  exceptional_residue_inventory_not_completed : Prop
  perron_inversion_not_proved : Prop
  meromorphic_rectangle_residue_theorem_not_proved : Prop
  infinite_explicit_formula_not_proved : Prop
  gallagher_not_proved : Prop
  otsa_not_proved : Prop
  goldbach_not_claimed : Prop

def closedCompletionCorrectionAndHorizontalDecayLedger :
    ClosedCompletionCorrectionAndHorizontalDecayLedger where
  gamma_compact_upper_bound_proved := True
  gamma_reflection_lower_bound_proved := True
  completion_multiplier_upper_bound_proved := True
  completion_multiplier_center_lower_bound_proved := True
  centered_completion_log_constructed := True
  completion_real_part_envelope_closed := True
  completion_log_derivative_linear_bound_proved := True
  finite_grid_exact_zeta_decomposition_proved := True
  complete_horizontal_pointwise_bound_proved := True
  complete_top_integral_decay_proved := True
  complete_bottom_integral_decay_proved := True
  fixed_left_boundary_not_proved := True
  exceptional_residue_inventory_not_completed := True
  perron_inversion_not_proved := True
  meromorphic_rectangle_residue_theorem_not_proved := True
  infinite_explicit_formula_not_proved := True
  gallagher_not_proved := True
  otsa_not_proved := True
  goldbach_not_claimed := True

end Goldbach
end TS304
