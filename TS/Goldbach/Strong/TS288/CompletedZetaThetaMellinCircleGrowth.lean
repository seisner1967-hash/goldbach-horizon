import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import TS.Goldbach.Strong.TS287.RiemannXiGrowthAPIProbe

/-!
# TS288 - Completed Zeta Theta-Mellin Circle Growth

TS287 reduced quantitative xi zero counting to a radial majorant for
Mathlib's entire regularized completed zeta function.  This sprint constructs
such a majorant directly from the theta-Mellin representation used by
Mathlib itself.

The modified theta kernel has a convergent Mellin transform at every complex
exponent.  On a circle `abs s = R`, the Mellin power is bounded pointwise by
the maximum of the two real endpoint powers with exponents
`R / 2 - 1` and `-R / 2 - 1`.  Both endpoint envelopes are integrable, so
their maximum gives a finite radial integral majorant.

This avoids a false reduction of the critical strip by the functional
equation: points with real part `1 / 2` remain on that line after reflection.
It also avoids separating Gamma from zeta across their cancelling poles.

The resulting radial integral fills the TS287 growth contract and is routed
through the complete xi/Jensen pipeline.  A closed elementary estimate for
the theta integral, an exponential `C * R * log (R + 2)` envelope, a
log-linear zero count, the explicit formula, Gallagher, OTSA, and Goldbach
are not claimed here.
-/

noncomputable section

namespace TS288
namespace Goldbach

open Complex Filter MeasureTheory Real Set

noncomputable def completedZetaModifiedThetaKernel : Real -> Complex :=
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

theorem completedRiemannZetaZero_eq_modifiedThetaMellin
    (s : Complex) :
    TS282.Goldbach.completedRiemannZetaZero s =
      mellin completedZetaModifiedThetaKernel (s / 2) / 2 := by
  rfl

theorem completedZetaModifiedThetaKernel_hasMellin
    (s : Complex) :
    HasMellin completedZetaModifiedThetaKernel s
      (mellin completedZetaModifiedThetaKernel s) := by
  exact (HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin s

noncomputable def thetaMellinRadialWeight
    (R x : Real) : Real :=
  max (x ^ (R / 2 - 1)) (x ^ (-R / 2 - 1))

theorem cpow_norm_le_thetaMellinRadialWeight
    {R x : Real}
    {s : Complex}
    (hx : 0 < x)
    (hz : Complex.abs s = R) :
    Complex.abs ((x : Complex) ^ (s / 2 - 1)) <=
      thetaMellinRadialWeight R x := by
  have hReAbs : |s.re| <= R := by
    rw [<- hz]
    exact Complex.abs_re_le_abs s
  have hReLower : -R <= s.re := (abs_le.mp hReAbs).1
  have hReUpper : s.re <= R := (abs_le.mp hReAbs).2
  rw [Complex.abs_cpow_eq_rpow_re_of_pos hx]
  have hExponent : (s / 2 - 1).re = s.re / 2 - 1 := by
    norm_num [div_eq_mul_inv]
  rw [hExponent]
  by_cases hxOne : x <= 1
  case pos =>
    apply le_trans (Real.rpow_le_rpow_of_exponent_ge hx hxOne ?_)
      (le_max_right _ _)
    linarith
  case neg =>
    apply le_trans (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hxOne) ?_)
      (le_max_left _ _)
    linarith

theorem completedZetaModifiedThetaKernel_aestronglyMeasurable :
    AEStronglyMeasurable completedZetaModifiedThetaKernel
      (volume.restrict (Ioi 0)) := by
  exact
    (HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hf_int
      |>.aestronglyMeasurable

theorem upperThetaMellinEnvelope_integrableOn
    (R : Real) :
    IntegrableOn
      (fun x : Real =>
        x ^ (R / 2 - 1) * norm (completedZetaModifiedThetaKernel x))
      (Ioi 0) := by
  have hMellin :=
    (completedZetaModifiedThetaKernel_hasMellin (R / 2 : Complex)).1
  have hNorm :=
    (mellin_convergent_iff_norm
      (f := completedZetaModifiedThetaKernel)
      (T := Ioi (0 : Real))
      (s := (R / 2 : Complex))
      (fun _ hx => hx)
      measurableSet_Ioi
      completedZetaModifiedThetaKernel_aestronglyMeasurable).mp hMellin
  simpa using hNorm

theorem lowerThetaMellinEnvelope_integrableOn
    (R : Real) :
    IntegrableOn
      (fun x : Real =>
        x ^ (-R / 2 - 1) * norm (completedZetaModifiedThetaKernel x))
      (Ioi 0) := by
  have hMellin :=
    (completedZetaModifiedThetaKernel_hasMellin (-R / 2 : Complex)).1
  have hNorm :=
    (mellin_convergent_iff_norm
      (f := completedZetaModifiedThetaKernel)
      (T := Ioi (0 : Real))
      (s := (-R / 2 : Complex))
      (fun _ hx => hx)
      measurableSet_Ioi
      completedZetaModifiedThetaKernel_aestronglyMeasurable).mp hMellin
  simpa using hNorm

theorem thetaMellinRadialEnvelope_integrableOn
    (R : Real) :
    IntegrableOn
      (fun x : Real =>
        thetaMellinRadialWeight R x *
          norm (completedZetaModifiedThetaKernel x))
      (Ioi 0) := by
  have hSup :=
    (upperThetaMellinEnvelope_integrableOn R).sup
      (lowerThetaMellinEnvelope_integrableOn R)
  simpa [thetaMellinRadialWeight, max_mul_of_nonneg] using hSup

noncomputable def completedZetaThetaMellinMajorant
    (R : Real) : Real :=
  integral
      (volume.restrict (Ioi 0))
      (fun x : Real =>
        thetaMellinRadialWeight R x *
          norm (completedZetaModifiedThetaKernel x)) / 2

theorem completedZetaThetaMellinMajorant_nonnegative
    (R : Real) :
    0 <= completedZetaThetaMellinMajorant R := by
  unfold completedZetaThetaMellinMajorant
  exact div_nonneg
    (integral_nonneg_of_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
        mul_nonneg
          ((Real.rpow_nonneg hx.le _).trans (le_max_left _ _))
          (norm_nonneg _)))
    (by norm_num)

theorem completedRiemannZetaZero_abs_le_thetaMellinMajorant
    (R : Real)
    (s : Complex)
    (hs : Complex.abs s = R) :
    Complex.abs (TS282.Goldbach.completedRiemannZetaZero s) <=
      completedZetaThetaMellinMajorant R := by
  rw [completedRiemannZetaZero_eq_modifiedThetaMellin]
  rw [<- Complex.norm_eq_abs, norm_div, Complex.norm_eq_abs]
  norm_num
  unfold completedZetaThetaMellinMajorant
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : Real) <= 2)
  unfold mellin
  rw [<- Complex.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    (thetaMellinRadialEnvelope_integrableOn R)
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => by
      rw [norm_smul, Complex.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (cpow_norm_le_thetaMellinRadialWeight hx hs)
        (norm_nonneg _))

def completedZetaThetaMellinCircleGrowth :
    TS287.Goldbach.CompletedZetaZeroCircleGrowthStatement
      completedZetaThetaMellinMajorant where
  norm_le := by
    intro R _ s hs
    exact completedRiemannZetaZero_abs_le_thetaMellinMajorant R s hs

/-- The radial theta integral provides an unconditional explicit boundary
statement for the concrete xi factorization. -/
noncomputable def xiThetaMellinBoundaryNormStatement
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
      (TS.Goldbach.MasterAPI.xi_factorization r hr)
      (TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
        completedZetaThetaMellinMajorant
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :=
  TS287.Goldbach.xi_explicitBoundaryNormStatement
    completedZetaThetaMellinCircleGrowth r hr hLarge

/-- Concrete finite Jensen boundary estimate using the radial theta
integral, with no remaining growth hypothesis. -/
theorem xi_finiteJensenBoundaryEstimate_thetaMellin
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      (TS.Goldbach.MasterAPI.xi_disk_data r hr)
      TS.Goldbach.MasterAPI.xi
      (TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
        completedZetaThetaMellinMajorant
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :=
  TS287.Goldbach.xi_finiteJensenBoundaryEstimate_explicit
    completedZetaThetaMellinCircleGrowth r hr hLarge

/-- Terminal TS288 facade: the finite xi-zero multiplicity count is bounded
by a fully specified radial theta-Mellin budget. -/
theorem xi_zero_count_le_thetaMellin_majorant
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (TS.Goldbach.MasterAPI.xi_disk_data r hr) : Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
            completedZetaThetaMellinMajorant
            (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius)
          (TS.Goldbach.MasterAPI.xi
            (TS.Goldbach.MasterAPI.xi_geometry r hr).center) /
        Real.log
          ((TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius /
            (TS.Goldbach.MasterAPI.xi_geometry r hr).innerRadius) :=
  TS287.Goldbach.xi_zero_count_le_explicit_completedZeta_majorant
    completedZetaThetaMellinCircleGrowth r hr hLarge

structure CompletedZetaThetaMellinCircleGrowthLedger where
  ts287_growth_routing : TS287.Goldbach.RiemannXiGrowthAPIProbeLedger
  mellin_representation_exact :
    forall s : Complex,
      TS282.Goldbach.completedRiemannZetaZero s =
        mellin completedZetaModifiedThetaKernel (s / 2) / 2
  radial_power_envelope :
    forall (R x : Real) (s : Complex),
      0 < x ->
      Complex.abs s = R ->
        Complex.abs ((x : Complex) ^ (s / 2 - 1)) <=
          thetaMellinRadialWeight R x
  radial_envelope_integrable :
    forall R : Real,
      IntegrableOn
        (fun x : Real =>
          thetaMellinRadialWeight R x *
            norm (completedZetaModifiedThetaKernel x))
        (Ioi 0)
  completed_zeta_circle_growth_proved :
    TS287.Goldbach.CompletedZetaZeroCircleGrowthStatement
      completedZetaThetaMellinMajorant
  closed_form_theta_integral_bound_not_proved : True
  exponential_radius_envelope_not_proved : True
  log_linear_zero_count_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def completedZetaThetaMellinCircleGrowthLedger :
    CompletedZetaThetaMellinCircleGrowthLedger where
  ts287_growth_routing := TS287.Goldbach.riemannXiGrowthAPIProbeLedger
  mellin_representation_exact := completedRiemannZetaZero_eq_modifiedThetaMellin
  radial_power_envelope := by
    intro R x s hx hs
    exact cpow_norm_le_thetaMellinRadialWeight hx hs
  radial_envelope_integrable := thetaMellinRadialEnvelope_integrableOn
  completed_zeta_circle_growth_proved := completedZetaThetaMellinCircleGrowth
  closed_form_theta_integral_bound_not_proved := True.intro
  exponential_radius_envelope_not_proved := True.intro
  log_linear_zero_count_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def CompletedZetaThetaMellinCircleGrowthTarget : Prop :=
  Nonempty CompletedZetaThetaMellinCircleGrowthLedger

theorem completedZetaThetaMellinCircleGrowthTarget :
    CompletedZetaThetaMellinCircleGrowthTarget :=
  Nonempty.intro completedZetaThetaMellinCircleGrowthLedger

end Goldbach
end TS288
