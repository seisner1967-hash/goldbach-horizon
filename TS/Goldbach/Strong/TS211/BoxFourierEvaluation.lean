import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import TS.Goldbach.Strong.TS210.BoxConvolutionTriangleEvidence

namespace TS211
namespace Goldbach

open MeasureTheory

/-!
# TS211 - Box Fourier Evaluation

TS210 proved the spatial convolution identity for the centered unit box.  TS211
attacks the second TS167 convolution-route input: the Mathlib Fourier transform
of the centered unit box.

This sprint keeps the target exactly aligned with TS167:

`Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
  scaledSinc Real.pi xi`.

The proof is a direct finite-interval Fourier calculation.  It first reduces
the global Fourier integral to the compact interval `[-1/2, 1/2]`, then
evaluates the zero-frequency and nonzero-frequency cases separately.

No Fourier-convolution exchange theorem, Plancherel theorem, explicit formula,
Gallagher comparison, or Goldbach theorem is claimed.
-/

/-- Explicit Mathlib Fourier integrand for the centered box. -/
noncomputable def unitBoxFourierIntegrand
    (xi x : Real) :
    Complex :=
  Complex.exp (((-2 * Real.pi * xi : Real) : Complex) * Complex.I * x) *
    TS167.Goldbach.unitBoxAsComplex x

/-- The pure exponential integrand used after restricting to the box support. -/
noncomputable def unitBoxPureFourierIntegrand
    (xi x : Real) :
    Complex :=
  Complex.exp (((-2 * Real.pi * xi : Real) : Complex) * Complex.I * x)

/-- Mathlib's Fourier integral of the box is the global integral of the explicit kernel. -/
theorem unitBoxFourier_eq_globalIntegral
    (xi : Real) :
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
      integral (volume : Measure Real)
        (fun x : Real => unitBoxFourierIntegrand xi x) := by
  unfold unitBoxFourierIntegrand
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  change
    Complex.exp (((-2 * Real.pi * x * xi : Real) : Complex) * Complex.I) *
        TS167.Goldbach.unitBoxAsComplex x =
      Complex.exp (((-2 * Real.pi * xi : Real) : Complex) * Complex.I * x) *
        TS167.Goldbach.unitBoxAsComplex x
  congr 1
  apply congrArg Complex.exp
  norm_num [Complex.ofReal_mul]
  ring

/-- The explicit box Fourier integrand vanishes outside the centered unit interval. -/
theorem unitBoxFourierIntegrand_eq_zero_of_not_mem_Icc
    (xi x : Real)
    (hx : Not (Set.Icc (-(1 / 2 : Real)) (1 / 2 : Real) x)) :
    unitBoxFourierIntegrand xi x = 0 := by
  unfold unitBoxFourierIntegrand TS167.Goldbach.unitBoxAsComplex
    TS167.Goldbach.unitBoxFunction
  have hbox_zero :
      (if -(1 / 2 : Real) <= x /\ x <= (1 / 2 : Real) then
          (1 : Real)
        else
          0) = 0 := by
    rw [if_neg]
    intro hmem
    apply hx
    exact And.intro hmem.1 hmem.2
  rw [hbox_zero]
  simp

/-- On the centered unit interval, the explicit box Fourier integrand is the pure kernel. -/
theorem unitBoxFourierIntegrand_eq_pure_of_mem_Icc
    (xi x : Real)
    (hx : Set.Icc (-(1 / 2 : Real)) (1 / 2 : Real) x) :
    unitBoxFourierIntegrand xi x =
      unitBoxPureFourierIntegrand xi x := by
  unfold unitBoxFourierIntegrand unitBoxPureFourierIntegrand
    TS167.Goldbach.unitBoxAsComplex TS167.Goldbach.unitBoxFunction
  have hbox : -(1 / 2 : Real) <= x /\ x <= (1 / 2 : Real) := by
    exact And.intro hx.1 hx.2
  have hbox_one :
      (if -(1 / 2 : Real) <= x /\ x <= (1 / 2 : Real) then
          (1 : Real)
        else
          0) = 1 := by
    rw [if_pos hbox]
  rw [hbox_one]
  simp

/-- The global box Fourier integral is the directed interval integral over the box support. -/
theorem unitBoxFourier_globalIntegral_eq_intervalIntegral
    (xi : Real) :
    integral (volume : Measure Real)
        (fun x : Real => unitBoxFourierIntegrand xi x) =
      intervalIntegral
        (fun x : Real => unitBoxPureFourierIntegrand xi x)
        (-(1 / 2 : Real))
        (1 / 2 : Real)
        (volume : Measure Real) := by
  have hrestrict :
      integral
          ((volume : Measure Real).restrict
            (Set.Icc (-(1 / 2 : Real)) (1 / 2 : Real)))
          (fun x : Real => unitBoxFourierIntegrand xi x) =
        integral (volume : Measure Real)
          (fun x : Real => unitBoxFourierIntegrand xi x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(1 / 2 : Real)) (1 / 2 : Real))
      (f := fun x : Real => unitBoxFourierIntegrand xi x)
      (by
        intro x hx
        exact unitBoxFourierIntegrand_eq_zero_of_not_mem_Icc xi x hx)
  calc
    integral (volume : Measure Real)
        (fun x : Real => unitBoxFourierIntegrand xi x) =
        integral
          ((volume : Measure Real).restrict
            (Set.Icc (-(1 / 2 : Real)) (1 / 2 : Real)))
          (fun x : Real => unitBoxFourierIntegrand xi x) := hrestrict.symm
    _ =
        integral
          ((volume : Measure Real).restrict
            (Set.Icc (-(1 / 2 : Real)) (1 / 2 : Real)))
          (fun x : Real => unitBoxPureFourierIntegrand xi x) := by
          apply integral_congr_ae
          exact (ae_restrict_iff' measurableSet_Icc).mpr (by
            filter_upwards with x hx
            exact unitBoxFourierIntegrand_eq_pure_of_mem_Icc xi x hx)
    _ =
        intervalIntegral
          (fun x : Real => unitBoxPureFourierIntegrand xi x)
          (-(1 / 2 : Real))
          (1 / 2 : Real)
          (volume : Measure Real) := by
          rw [integral_Icc_eq_integral_Ioc]
          rw [<- intervalIntegral.integral_of_le
            (by norm_num : (-(1 / 2 : Real)) <= (1 / 2 : Real))]

/-- Compact interval form of the box Fourier integral. -/
theorem unitBoxFourier_eq_intervalIntegral
    (xi : Real) :
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
      intervalIntegral
        (fun x : Real => unitBoxPureFourierIntegrand xi x)
        (-(1 / 2 : Real))
        (1 / 2 : Real)
        (volume : Measure Real) := by
  calc
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
        integral (volume : Measure Real)
          (fun x : Real => unitBoxFourierIntegrand xi x) :=
      unitBoxFourier_eq_globalIntegral xi
    _ =
        intervalIntegral
          (fun x : Real => unitBoxPureFourierIntegrand xi x)
          (-(1 / 2 : Real))
          (1 / 2 : Real)
          (volume : Measure Real) :=
      unitBoxFourier_globalIntegral_eq_intervalIntegral xi

/-- Zero-frequency evaluation of the centered box Fourier integral. -/
theorem unitBoxFourier_zero :
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex 0 = 1 := by
  rw [unitBoxFourier_eq_intervalIntegral]
  unfold unitBoxPureFourierIntegrand
  simp
  norm_num

/-- The complex exponential primitive gives the nonzero-frequency box integral. -/
theorem unitBoxPureFourier_intervalIntegral_nonzero
    (xi : Real)
    (hscale : TS165.Goldbach.mathlibFourierTargetScale * xi = 0 -> False) :
    intervalIntegral
        (fun x : Real => unitBoxPureFourierIntegrand xi x)
        (-(1 / 2 : Real))
        (1 / 2 : Real)
        (volume : Measure Real) =
      (TS167.Goldbach.scaledSinc
        TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
  let t : Real := Real.pi * xi
  let c : Complex := (((-2 * Real.pi * xi : Real) : Complex) * Complex.I)
  have ht : t = 0 -> False := by
    intro ht0
    apply hscale
    unfold TS165.Goldbach.mathlibFourierTargetScale
    exact ht0
  have hcoeff_ne :
      Not ((((-2 * Real.pi * xi : Real) : Complex) : Complex) = 0) := by
    intro hcoeff
    have hreal : (-2 * Real.pi * xi : Real) = 0 :=
      Complex.ofReal_eq_zero.mp hcoeff
    apply ht
    dsimp [t]
    nlinarith
  have hc : Not (c = 0) := by
    dsimp [c]
    exact mul_ne_zero hcoeff_ne Complex.I_ne_zero
  have h_integral :
      intervalIntegral
          (fun x : Real => unitBoxPureFourierIntegrand xi x)
          (-(1 / 2 : Real))
          (1 / 2 : Real)
          (volume : Measure Real) =
        (Complex.exp (c * (1 / 2 : Real)) -
            Complex.exp (c * (-(1 / 2 : Real)))) / c := by
    unfold unitBoxPureFourierIntegrand
    change
      intervalIntegral
          (fun x : Real => Complex.exp (c * x))
          (-(1 / 2 : Real))
          (1 / 2 : Real)
          (volume : Measure Real) =
        (Complex.exp (c * (1 / 2 : Real)) -
            Complex.exp (c * (-(1 / 2 : Real)))) / c
    simpa using
      (integral_exp_mul_complex
        (a := (-(1 / 2 : Real)))
        (b := (1 / 2 : Real))
        (c := c)
        hc)
  have h_closed :
      (Complex.exp (c * (1 / 2 : Real)) -
            Complex.exp (c * (-(1 / 2 : Real)))) / c =
        ((Real.sin t / t : Real) : Complex) := by
    have hc_pos :
        c * (1 / 2 : Real) = ((-t : Real) : Complex) * Complex.I := by
      dsimp [c, t]
      norm_num [Complex.ofReal_mul]
      ring
    have hc_neg :
        c * (-(1 / 2 : Real)) = (t : Complex) * Complex.I := by
      dsimp [c, t]
      norm_num [Complex.ofReal_mul]
      ring
    rw [hc_pos, hc_neg]
    dsimp [c]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.ofReal_cos, Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Complex.ofReal_neg]
    have ht_complex : Not (((t : Real) : Complex) = 0) := by
      exact Complex.ofReal_ne_zero.mpr ht
    have hpi_xi_complex :
        Not ((((Real.pi * xi : Real) : Complex) : Complex) = 0) := by
      dsimp [t] at ht_complex
      exact ht_complex
    have hxi : xi = 0 -> False := by
      intro hxi0
      apply ht
      dsimp [t]
      rw [hxi0]
      ring
    have hxi_complex : Not (((xi : Real) : Complex) = 0) := by
      exact Complex.ofReal_ne_zero.mpr hxi
    have hpi_complex : Not (((Real.pi : Real) : Complex) = 0) := by
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [ht, ht_complex, hpi_xi_complex, hxi_complex,
      hpi_complex, Complex.I_ne_zero]
    rw [Complex.ofReal_mul]
    ring_nf
  calc
    intervalIntegral
        (fun x : Real => unitBoxPureFourierIntegrand xi x)
        (-(1 / 2 : Real))
        (1 / 2 : Real)
        (volume : Measure Real) =
        (Complex.exp (c * (1 / 2 : Real)) -
            Complex.exp (c * (-(1 / 2 : Real)))) / c := h_integral
    _ =
        ((Real.sin t / t : Real) : Complex) := h_closed
    _ =
        (TS167.Goldbach.scaledSinc
          TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
        unfold TS167.Goldbach.scaledSinc
        rw [if_neg hscale]
        dsimp [TS165.Goldbach.mathlibFourierTargetScale, t]

/-- Nonzero-frequency evaluation of the centered box Fourier integral. -/
theorem unitBoxFourier_nonzero
    (xi : Real)
    (hscale : TS165.Goldbach.mathlibFourierTargetScale * xi = 0 -> False) :
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
      (TS167.Goldbach.scaledSinc
        TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
  rw [unitBoxFourier_eq_intervalIntegral]
  exact unitBoxPureFourier_intervalIntegral_nonzero xi hscale

/--
The centered unit box has Mathlib Fourier transform equal to the non-squared
pi-scaled sinc profile.
-/
theorem boxFourierEvaluation :
    TS167.Goldbach.BoxFourierEvaluationStatement := by
  intro xi
  by_cases hscale :
      TS165.Goldbach.mathlibFourierTargetScale * xi = 0
  case pos =>
    have hxi : xi = 0 := by
      unfold TS165.Goldbach.mathlibFourierTargetScale at hscale
      exact mul_eq_zero.mp hscale |>.elim
        (fun hpi => False.elim (Real.pi_ne_zero hpi))
        (fun hxi => hxi)
    rw [hxi]
    rw [unitBoxFourier_zero]
    unfold TS167.Goldbach.scaledSinc
    simp
  case neg =>
    exact unitBoxFourier_nonzero xi hscale

/-- Ledger recording the TS211 box Fourier evaluation. -/
structure BoxFourierEvaluationLedger where
  ts210_box_convolution :
    TS210.Goldbach.BoxConvolutionTriangleEvidenceLedger

  box_fourier_statement :
    Prop

  box_fourier_statement_eq :
    box_fourier_statement =
      TS167.Goldbach.BoxFourierEvaluationStatement

  box_fourier_statement_proved :
    box_fourier_statement

  zero_frequency_evaluation :
    Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex 0 = 1

  nonzero_frequency_evaluation :
    forall xi : Real,
      (TS165.Goldbach.mathlibFourierTargetScale * xi = 0 -> False) ->
        Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi =
          (TS167.Goldbach.scaledSinc
            TS165.Goldbach.mathlibFourierTargetScale xi : Complex)

  box_convolution_statement_proved :
    TS167.Goldbach.BoxConvolutionEqualsTriangleSplineStatement

  fourier_convolution_exchange_not_proved :
    True

  plancherel_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS211 box Fourier evaluation ledger. -/
noncomputable def boxFourierEvaluationLedger :
    BoxFourierEvaluationLedger where
  ts210_box_convolution :=
    TS210.Goldbach.boxConvolutionTriangleEvidenceLedger
  box_fourier_statement :=
    TS167.Goldbach.BoxFourierEvaluationStatement
  box_fourier_statement_eq := rfl
  box_fourier_statement_proved :=
    boxFourierEvaluation
  zero_frequency_evaluation :=
    unitBoxFourier_zero
  nonzero_frequency_evaluation :=
    unitBoxFourier_nonzero
  box_convolution_statement_proved :=
    TS210.Goldbach.boxConvolutionEqualsTriangleSpline
  fourier_convolution_exchange_not_proved := True.intro
  plancherel_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS211. -/
def BoxFourierEvaluationTarget : Prop :=
  Nonempty BoxFourierEvaluationLedger

/-- The TS211 box Fourier evaluation target is populated. -/
theorem boxFourierEvaluationTarget :
    BoxFourierEvaluationTarget :=
  Nonempty.intro boxFourierEvaluationLedger

end Goldbach
end TS211
