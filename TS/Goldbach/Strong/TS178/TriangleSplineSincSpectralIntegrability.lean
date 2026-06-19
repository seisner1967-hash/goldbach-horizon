import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import TS.Goldbach.Strong.TS177.TriangleSplineTimeELpNormValue

namespace TS178
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS178 - Triangle Spline Sinc Spectral Integrability

TS177 closes the time-side L2 value of the triangle spline.  TS178 moves to
the Fourier side and proves that the pi-scale squared-sinc candidate has finite
L2 energy as an `eLpNorm` object.

The proof is deliberately local:

* the real squared-sinc weight is measurable and nonnegative;
* it is bounded by `1`;
* it is globally dominated by `2 / (1 + xi^2)`;
* Mathlib already proves integrability of `(1 + xi^2)^-1`;
* the squared real weight is therefore integrable;
* the complexified spectral candidate has finite `eLpNorm` at exponent `2`.

TS178 does not prove Plancherel, does not evaluate the spectral norm, does not
open the Riemann-von Mangoldt explicit formula, and does not prove Goldbach.
-/

/-- Real pi-scale squared-sinc spectral weight. -/
noncomputable def triangleSplineSincRealWeight
    (xi : Real) :
    Real :=
  TS164.Goldbach.scaledSincSq
    TS165.Goldbach.mathlibFourierTargetScale xi

/-- Complex lift of the pi-scale squared-sinc spectral weight. -/
noncomputable def triangleSplineSincComplexWeight
    (xi : Real) :
    Complex :=
  (triangleSplineSincRealWeight xi : Complex)

/-- The real squared-sinc spectral weight is nonnegative. -/
theorem triangleSplineSincRealWeight_nonneg
    (xi : Real) :
    0 <= triangleSplineSincRealWeight xi := by
  unfold triangleSplineSincRealWeight
  exact
    TS164.Goldbach.scaledSincSq_nonneg
      TS165.Goldbach.mathlibFourierTargetScale xi

/-- The real squared-sinc spectral weight is measurable. -/
theorem triangleSplineSincRealWeight_measurable :
    Measurable triangleSplineSincRealWeight := by
  unfold triangleSplineSincRealWeight TS164.Goldbach.scaledSincSq
  exact
    Measurable.ite
      ((measurableSet_singleton (0 : Real)).preimage
        (measurable_const.mul measurable_id))
      measurable_const
      (((Real.continuous_sin.measurable.comp
        (measurable_const.mul measurable_id)).div
        (measurable_const.mul measurable_id)).pow_const 2)

/-- The real squared-sinc spectral weight is a.e. strongly measurable. -/
theorem triangleSplineSincRealWeight_aestronglyMeasurable :
    AEStronglyMeasurable
      triangleSplineSincRealWeight
      (volume : Measure Real) :=
  triangleSplineSincRealWeight_measurable.aestronglyMeasurable

/-- The complex squared-sinc spectral weight is a.e. strongly measurable. -/
theorem triangleSplineSincComplexWeight_aestronglyMeasurable :
    AEStronglyMeasurable
      triangleSplineSincComplexWeight
      (volume : Measure Real) := by
  unfold triangleSplineSincComplexWeight
  exact
    (Complex.continuous_ofReal.measurable.comp
      triangleSplineSincRealWeight_measurable).aestronglyMeasurable

/-- Pointwise bound: the pi-scale squared-sinc weight is at most `1`. -/
theorem triangleSplineSincRealWeight_le_one
    (xi : Real) :
    triangleSplineSincRealWeight xi <= 1 := by
  unfold triangleSplineSincRealWeight TS164.Goldbach.scaledSincSq
  unfold TS165.Goldbach.mathlibFourierTargetScale
  by_cases h : Real.pi * xi = 0
  case pos =>
    simp [h]
  case neg =>
    have hsq :
        (Real.sin (Real.pi * xi) / (Real.pi * xi)) ^ 2 <= 1 := by
      rw [sq_le_one_iff_abs_le_one]
      rw [abs_div]
      have hsin :
          |Real.sin (Real.pi * xi)| <= |Real.pi * xi| :=
        Real.abs_sin_le_abs
      calc
        |Real.sin (Real.pi * xi)| / |Real.pi * xi|
            <= |Real.pi * xi| / |Real.pi * xi| := by
              exact div_le_div_of_nonneg_right hsin (abs_nonneg _)
        _ = 1 := by
              exact div_self (abs_pos.mpr h).ne'
    simpa [h] using hsq

/--
Global domination by an integrable comparison kernel.

The near-origin region uses `sinc^2 <= 1`, while the tail uses
`sin^2 <= 1` and the elementary inequality
`1 + xi^2 <= 2 * (pi * xi)^2` for `|xi| >= 1`.
-/
theorem triangleSplineSincRealWeight_le_integrableBound
    (xi : Real) :
    triangleSplineSincRealWeight xi <=
      2 * (1 / (1 + xi ^ 2)) := by
  by_cases hsmall : |xi| <= 1
  case pos =>
    have hone :
        triangleSplineSincRealWeight xi <= 1 :=
      triangleSplineSincRealWeight_le_one xi
    have hxi_sq : xi ^ 2 <= 1 := by
      simpa [sq_abs] using (sq_le_one_iff_abs_le_one xi).mpr hsmall
    have hden_pos : 0 < 1 + xi ^ 2 := by positivity
    have htarget : 1 <= 2 * (1 / (1 + xi ^ 2)) := by
      have htarget_div : 1 <= 2 / (1 + xi ^ 2) := by
        rw [one_le_div hden_pos]
        linarith
      simpa [div_eq_mul_inv] using htarget_div
    exact hone.trans htarget
  case neg =>
    have hlarge_abs : 1 <= |xi| := le_of_not_ge hsmall
    have hxi_ne : Not (xi = 0) := by
      intro hzero
      simp [hzero] at hlarge_abs
      norm_num at hlarge_abs
    have harg_ne : Not (Real.pi * xi = 0) := by
      exact mul_ne_zero Real.pi_ne_zero hxi_ne
    have hxi_sq_ge : 1 <= xi ^ 2 := by
      have hsq_abs : 1 <= |xi| ^ 2 := by
        nlinarith [hlarge_abs, sq_nonneg |xi|]
      simpa [sq_abs] using hsq_abs
    have harg_sq_pos : 0 < (Real.pi * xi) ^ 2 :=
      sq_pos_of_ne_zero harg_ne
    have hsin_bound :
        (Real.sin (Real.pi * xi) / (Real.pi * xi)) ^ 2 <=
          1 / ((Real.pi * xi) ^ 2) := by
      have hsin_one :
          Real.sin (Real.pi * xi) ^ 2 <= 1 :=
        Real.sin_sq_le_one (Real.pi * xi)
      calc
        (Real.sin (Real.pi * xi) / (Real.pi * xi)) ^ 2
            = Real.sin (Real.pi * xi) ^ 2 / (Real.pi * xi) ^ 2 := by
              ring
        _ <= 1 / (Real.pi * xi) ^ 2 := by
              exact div_le_div_of_nonneg_right hsin_one (sq_nonneg _)
    have hpi_ge_one : 1 <= Real.pi := by
      linarith [Real.one_le_pi_div_two]
    have hpi_sq_ge_one : 1 <= Real.pi ^ 2 := by
      nlinarith [hpi_ge_one, sq_nonneg (Real.pi - 1)]
    have hden_compare :
        1 + xi ^ 2 <= 2 * ((Real.pi * xi) ^ 2) := by
      have hpi_x :
          xi ^ 2 <= (Real.pi * xi) ^ 2 := by
        nlinarith [hpi_sq_ge_one, hxi_sq_ge, sq_nonneg Real.pi,
          sq_nonneg xi]
      nlinarith
    have htarget :
        1 / ((Real.pi * xi) ^ 2) <= 2 * (1 / (1 + xi ^ 2)) := by
      have htarget_div :
          1 / ((Real.pi * xi) ^ 2) <= 2 / (1 + xi ^ 2) := by
        have hden_pos : 0 < 1 + xi ^ 2 := by positivity
        have hone_div :
            1 <=
              (2 * ((Real.pi * xi) ^ 2)) / (1 + xi ^ 2) := by
          rw [one_le_div hden_pos]
          exact hden_compare
        have hmul :
            1 <=
              (2 / (1 + xi ^ 2)) * ((Real.pi * xi) ^ 2) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            hone_div
        have htarget_mul :
            (1 / ((Real.pi * xi) ^ 2)) * ((Real.pi * xi) ^ 2) <=
              (2 / (1 + xi ^ 2)) * ((Real.pi * xi) ^ 2) := by
          simpa [harg_sq_pos.ne'] using hmul
        exact (mul_le_mul_right harg_sq_pos).mp htarget_mul
      simpa [div_eq_mul_inv] using htarget_div
    unfold triangleSplineSincRealWeight TS164.Goldbach.scaledSincSq
    unfold TS165.Goldbach.mathlibFourierTargetScale
    simpa [harg_ne] using hsin_bound.trans htarget

/-- The real squared-sinc spectral weight is integrable on the real line. -/
theorem triangleSplineSincRealWeight_integrable :
    Integrable
      triangleSplineSincRealWeight
      (volume : Measure Real) := by
  refine
    Integrable.mono'
      (by
        simpa [one_div] using
          (integrable_inv_one_add_sq.const_mul (2 : Real)))
      triangleSplineSincRealWeight_aestronglyMeasurable
      ?_
  exact Filter.Eventually.of_forall (by
    intro xi
    have hnon :
        0 <= triangleSplineSincRealWeight xi :=
      triangleSplineSincRealWeight_nonneg xi
    have hle :
        triangleSplineSincRealWeight xi <=
          2 * (1 / (1 + xi ^ 2)) :=
      triangleSplineSincRealWeight_le_integrableBound xi
    simpa [Real.norm_eq_abs, abs_of_nonneg hnon] using hle)

/-- The square of the real squared-sinc weight is integrable. -/
theorem triangleSplineSincRealWeight_sq_integrable :
    Integrable
      (fun xi : Real => triangleSplineSincRealWeight xi ^ 2)
      (volume : Measure Real) := by
  refine
    Integrable.mono'
      triangleSplineSincRealWeight_integrable
      ((triangleSplineSincRealWeight_measurable.pow_const 2).aestronglyMeasurable)
      ?_
  exact Filter.Eventually.of_forall (by
    intro xi
    have hnon :
        0 <= triangleSplineSincRealWeight xi :=
      triangleSplineSincRealWeight_nonneg xi
    have hle_one :
        triangleSplineSincRealWeight xi <= 1 :=
      triangleSplineSincRealWeight_le_one xi
    have hsquare :
        triangleSplineSincRealWeight xi ^ 2 <=
          triangleSplineSincRealWeight xi := by
      nlinarith [hnon, hle_one]
    have hsquare_nonneg :
        0 <= triangleSplineSincRealWeight xi ^ 2 := by
      exact sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hsquare_nonneg] using hsquare)

/-- The squared norm of the complex spectral weight is integrable. -/
theorem triangleSplineSincComplexNormSq_integrable :
    Integrable
      (fun xi : Real => norm (triangleSplineSincComplexWeight xi) ^ 2)
      (volume : Measure Real) := by
  exact triangleSplineSincRealWeight_sq_integrable.congr
    (Filter.Eventually.of_forall (by
      intro xi
      unfold triangleSplineSincComplexWeight
      have hnon :
          0 <= triangleSplineSincRealWeight xi :=
        triangleSplineSincRealWeight_nonneg xi
      simp [Complex.normSq, Complex.normSq_apply, hnon]))

/-- The complex spectral weight has finite L2 `eLpNorm`. -/
theorem triangleSplineSincComplexWeight_eLpNorm_lt_top :
    eLpNorm
      triangleSplineSincComplexWeight
      2
      (volume : Measure Real) <
        (Top.top : ENNReal) := by
  rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top
    (by norm_num : Not ((2 : ENNReal) = 0))
    ENNReal.two_ne_top]
  have hlintegral_ofReal :
      ENNReal.ofReal
        (integral
          (volume : Measure Real)
          (fun xi : Real =>
            norm (triangleSplineSincComplexWeight xi) ^ 2))
        =
      lintegral
        (volume : Measure Real)
        (fun xi : Real =>
          ENNReal.ofReal
            (norm (triangleSplineSincComplexWeight xi) ^ 2)) := by
    exact
      ofReal_integral_eq_lintegral_ofReal
        triangleSplineSincComplexNormSq_integrable
        (Filter.Eventually.of_forall (by
          intro xi
          positivity))
  have hcongr :
      lintegral
        (volume : Measure Real)
        (fun xi : Real =>
          (nnnorm (triangleSplineSincComplexWeight xi) :
            ENNReal) ^ (2 : ENNReal).toReal)
        =
      lintegral
        (volume : Measure Real)
        (fun xi : Real =>
          ENNReal.ofReal
            (norm (triangleSplineSincComplexWeight xi) ^ 2)) := by
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall (by
      intro xi
      change
        (nnnorm (triangleSplineSincComplexWeight xi) :
          ENNReal) ^ (2 : Real) =
          ENNReal.ofReal
            (norm (triangleSplineSincComplexWeight xi) ^ 2)
      rw [show
          (nnnorm (triangleSplineSincComplexWeight xi) :
            ENNReal) =
            ENNReal.ofReal
              (norm (triangleSplineSincComplexWeight xi)) from by
          exact
            (ofReal_norm_eq_coe_nnnorm
              (triangleSplineSincComplexWeight xi)).symm]
      rw [ENNReal.ofReal_rpow_of_nonneg
        (norm_nonneg _)
        (by norm_num : (0 : Real) <= 2)]
      norm_num)
  calc
    lintegral
        (volume : Measure Real)
        (fun xi : Real =>
          (nnnorm (triangleSplineSincComplexWeight xi) :
            ENNReal) ^ (2 : ENNReal).toReal)
        =
      ENNReal.ofReal
        (integral
          (volume : Measure Real)
          (fun xi : Real =>
            norm (triangleSplineSincComplexWeight xi) ^ 2)) := by
        rw [hcongr, hlintegral_ofReal.symm]
    _ < (Top.top : ENNReal) := ENNReal.ofReal_lt_top

/-- The TS174 squared-sinc energy is finite. -/
theorem triangleSplineSincL2Energy_lt_top :
    TS174.Goldbach.triangleSplineSincL2Energy <
      (Top.top : ENNReal) := by
  simpa [TS174.Goldbach.triangleSplineSincL2Energy,
    TS166.Goldbach.triangleSplineScaledSincCandidate,
    triangleSplineSincComplexWeight, triangleSplineSincRealWeight] using
      triangleSplineSincComplexWeight_eLpNorm_lt_top

/-- The TS174 squared-sinc energy is not infinite. -/
theorem triangleSplineSincL2Energy_ne_top :
    Not
      (TS174.Goldbach.triangleSplineSincL2Energy =
        (Top.top : ENNReal)) :=
  ne_of_lt triangleSplineSincL2Energy_lt_top

/-- Ledger for the TS178 spectral integrability discharge. -/
structure TriangleSplineSincSpectralIntegrabilityLedger where
  ts177_time_value :
    TS177.Goldbach.TriangleSplineTimeELpNormValueLedger

  real_weight_integrable :
    Integrable
      triangleSplineSincRealWeight
      (volume : Measure Real)

  real_weight_square_integrable :
    Integrable
      (fun xi : Real => triangleSplineSincRealWeight xi ^ 2)
      (volume : Measure Real)

  complex_norm_square_integrable :
    Integrable
      (fun xi : Real => norm (triangleSplineSincComplexWeight xi) ^ 2)
      (volume : Measure Real)

  sinc_l2_energy_finite :
    TS174.Goldbach.triangleSplineSincL2Energy <
      (Top.top : ENNReal)

  plancherel_not_claimed :
    True

  spectral_norm_value_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS178 spectral integrability ledger. -/
noncomputable def triangleSplineSincSpectralIntegrabilityLedger :
    TriangleSplineSincSpectralIntegrabilityLedger where
  ts177_time_value :=
    TS177.Goldbach.triangleSplineTimeELpNormValueLedger
  real_weight_integrable :=
    triangleSplineSincRealWeight_integrable
  real_weight_square_integrable :=
    triangleSplineSincRealWeight_sq_integrable
  complex_norm_square_integrable :=
    triangleSplineSincComplexNormSq_integrable
  sinc_l2_energy_finite :=
    triangleSplineSincL2Energy_lt_top
  plancherel_not_claimed := True.intro
  spectral_norm_value_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS178. -/
def TriangleSplineSincSpectralIntegrabilityTarget : Prop :=
  Nonempty TriangleSplineSincSpectralIntegrabilityLedger

/-- The TS178 spectral integrability target is populated. -/
theorem triangleSplineSincSpectralIntegrabilityTarget :
    TriangleSplineSincSpectralIntegrabilityTarget :=
  Nonempty.intro triangleSplineSincSpectralIntegrabilityLedger

end Goldbach
end TS178
