import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS256.RiemannZetaZeroTruncatedContribution

/-!
# TS257 - Triangle Spline Mellin Spectral Summand

TS256 introduced a finite zeta-zero sum with an abstract spectral summand.
This sprint defines the expected triangle-spline Mellin kernel and the
corresponding positive zero contribution under the TS206 sign convention.

The Mellin kernel is `1 / (s * (s + 1))`.  Thus the zero contribution stored
in TS255 is `X^rho / (rho * (rho + 1))`; TS206 applies the minus sign in the
explicit-formula identity.  The opposite contour-residue term is named
separately to prevent a double sign change.

The positive Mellin integral is defined, but its evaluation, conjugation
compatibility, contour interpretation, explicit-formula identity, and all
analytic bounds remain open.
-/

namespace TS257
namespace Goldbach

open MeasureTheory

/-- Meromorphic Mellin kernel of the unit positive triangle weight. -/
noncomputable def triangleSplineMellinKernel
    (s : Complex) :
    Complex :=
  1 / (s * (s + 1))

/--
Bochner interval integral representing the positive triangle Mellin transform.
Its evaluation is a separate analytic target.
-/
noncomputable def triangleSplinePositiveMellinIntegral
    (s : Complex) :
    Complex :=
  intervalIntegral
    (fun t : Real =>
      (((1 - t : Real) : Complex)) *
        ((t : Complex) ^ (s - 1)))
    (0 : Real)
    1
    (volume : Measure Real)

/-- Analytic target identifying the Mellin integral with its closed form. -/
def TriangleSplineMellinIntegralEvaluationStatement : Prop :=
  forall s : Complex,
    0 < s.re ->
      triangleSplinePositiveMellinIntegral s =
        triangleSplineMellinKernel s

/-- Algebraic partial-fraction form of the Mellin kernel. -/
theorem triangleSplineMellinKernel_eq_sub
    (s : Complex)
    (hs : Not (s = 0))
    (hs1 : Not (s + 1 = 0)) :
    triangleSplineMellinKernel s =
      1 / s - 1 / (s + 1) := by
  unfold triangleSplineMellinKernel
  field_simp

/-- A complex number with positive real part is nonzero. -/
theorem complex_ne_zero_of_re_pos
    (z : Complex)
    (hz : 0 < z.re) :
    Not (z = 0) := by
  intro hZero
  rw [hZero] at hz
  norm_num at hz

/-- A complex number with positive real part is not negative one. -/
theorem complex_add_one_ne_zero_of_re_pos
    (z : Complex)
    (hz : 0 < z.re) :
    Not (z + 1 = 0) := by
  intro hZero
  have hRe := congrArg Complex.re hZero
  norm_num at hRe
  linarith

/-- The Mellin denominator is nonzero in the positive-real-part half-plane. -/
theorem triangleSplineMellinKernel_denominator_ne_zero_of_re_pos
    (z : Complex)
    (hz : 0 < z.re) :
    Not (z * (z + 1) = 0) :=
  mul_ne_zero
    (complex_ne_zero_of_re_pos z hz)
    (complex_add_one_ne_zero_of_re_pos z hz)

/-- The Mellin denominator is nonzero at every TS185 nontrivial zero. -/
theorem triangleSplineMellinKernel_denominator_ne_zero_at_nontrivialZero
    (rho : Complex)
    (hZero : TS185.Goldbach.nontrivialRiemannZetaZeroPredicate rho) :
    Not (rho * (rho + 1) = 0) :=
  triangleSplineMellinKernel_denominator_ne_zero_of_re_pos
    rho hZero.2.1

/--
Positive zero contribution for the TS206 convention
`leftSide = mainTerm - zeroContribution + residualTerm`.
-/
noncomputable def triangleSplineZeroSpectralSummand :
    TS256.Goldbach.ZeroSpectralSummand :=
  fun X rho =>
    (X : Complex) ^ rho / (rho * (rho + 1))

/-- Closed form of the triangle-spline zero summand. -/
theorem triangleSplineZeroSpectralSummand_spec
    (X : Nat)
    (rho : Complex) :
    triangleSplineZeroSpectralSummand X rho =
      (X : Complex) ^ rho / (rho * (rho + 1)) :=
  rfl

/-- The zero summand is the scale factor times the Mellin kernel. -/
theorem triangleSplineZeroSpectralSummand_eq_scale_mul_kernel
    (X : Nat)
    (rho : Complex) :
    triangleSplineZeroSpectralSummand X rho =
      (X : Complex) ^ rho * triangleSplineMellinKernel rho := by
  unfold triangleSplineZeroSpectralSummand triangleSplineMellinKernel
  simp [div_eq_mul_inv]

/-- Opposite-signed term produced when the zero residue is moved left. -/
noncomputable def triangleSplineZeroContourResidueTerm
    (X : Nat)
    (rho : Complex) :
    Complex :=
  -triangleSplineZeroSpectralSummand X rho

/-- Closed form of the opposite-signed contour residue term. -/
theorem triangleSplineZeroContourResidueTerm_spec
    (X : Nat)
    (rho : Complex) :
    triangleSplineZeroContourResidueTerm X rho =
      -((X : Complex) ^ rho / (rho * (rho + 1))) :=
  rfl

/-- Future conjugation compatibility target for the concrete summand. -/
def TriangleSplineZeroSpectralSummandConjugationStatement : Prop :=
  forall (X : Nat) (rho : Complex),
    0 < X ->
      triangleSplineZeroSpectralSummand X (star rho) =
        star (triangleSplineZeroSpectralSummand X rho)

/-- TS255 zero function obtained from the concrete triangle-spline summand. -/
noncomputable def triangleSplineZeroContributionFunction
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C) :
    TS255.Goldbach.ZeroContributionFunction :=
  TS256.Goldbach.truncatedZeroContributionFunction
    C truncation triangleSplineZeroSpectralSummand

/-- Finite complex zero sum using the concrete triangle-spline summand. -/
noncomputable def triangleSplineZeroTruncatedComplexSum
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (X : Nat) :
    Complex :=
  TS256.Goldbach.zetaZeroTruncatedComplexSum
    C truncation triangleSplineZeroSpectralSummand X

/-- The concrete zero function satisfies the TS256 identification target. -/
theorem triangleSplineZeroContributionFunction_identification
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C) :
    TS256.Goldbach.TruncatedZeroContributionIdentificationStatement
      (triangleSplineZeroContributionFunction C truncation)
      C
      truncation
      triangleSplineZeroSpectralSummand :=
  rfl

/-- Ledger recording the Mellin kernel and concrete spectral summand. -/
structure TriangleSplineMellinSpectralSummandLedger where
  ts256_truncated_contribution :
    TS256.Goldbach.RiemannZetaZeroTruncatedContributionLedger

  mellin_kernel :
    Complex -> Complex

  mellin_kernel_eq :
    mellin_kernel = triangleSplineMellinKernel

  mellin_kernel_partial_fraction :
    forall s : Complex,
      Not (s = 0) ->
        Not (s + 1 = 0) ->
          mellin_kernel s = 1 / s - 1 / (s + 1)

  denominator_nonzero_at_nontrivial_zero :
    forall rho : Complex,
      TS185.Goldbach.nontrivialRiemannZetaZeroPredicate rho ->
        Not (rho * (rho + 1) = 0)

  zero_spectral_summand :
    TS256.Goldbach.ZeroSpectralSummand

  zero_spectral_summand_eq :
    zero_spectral_summand = triangleSplineZeroSpectralSummand

  zero_spectral_summand_spec :
    forall (X : Nat) (rho : Complex),
      zero_spectral_summand X rho =
        (X : Complex) ^ rho / (rho * (rho + 1))

  zero_contribution_function :
    forall C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract,
      TS256.Goldbach.RiemannZetaZeroTruncationData C ->
        TS255.Goldbach.ZeroContributionFunction

  mellin_integral_evaluation_not_proved : True
  mellin_fourier_equivalence_not_proved : True
  contour_residue_identification_not_proved : True
  summand_conjugation_not_proved : True
  truncated_sum_reality_not_proved : True
  explicit_formula_identity_not_proved : True
  named_zero_bound_not_proved : True
  named_residual_function_not_constructed : True
  named_residual_bound_not_proved : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS257 Mellin-summand ledger. -/
noncomputable def triangleSplineMellinSpectralSummandLedger :
    TriangleSplineMellinSpectralSummandLedger where
  ts256_truncated_contribution :=
    TS256.Goldbach.riemannZetaZeroTruncatedContributionLedger
  mellin_kernel :=
    triangleSplineMellinKernel
  mellin_kernel_eq :=
    rfl
  mellin_kernel_partial_fraction :=
    triangleSplineMellinKernel_eq_sub
  denominator_nonzero_at_nontrivial_zero :=
    triangleSplineMellinKernel_denominator_ne_zero_at_nontrivialZero
  zero_spectral_summand :=
    triangleSplineZeroSpectralSummand
  zero_spectral_summand_eq :=
    rfl
  zero_spectral_summand_spec :=
    triangleSplineZeroSpectralSummand_spec
  zero_contribution_function :=
    triangleSplineZeroContributionFunction
  mellin_integral_evaluation_not_proved := True.intro
  mellin_fourier_equivalence_not_proved := True.intro
  contour_residue_identification_not_proved := True.intro
  summand_conjugation_not_proved := True.intro
  truncated_sum_reality_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  named_zero_bound_not_proved := True.intro
  named_residual_function_not_constructed := True.intro
  named_residual_bound_not_proved := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS257. -/
def TriangleSplineMellinSpectralSummandTarget : Prop :=
  Nonempty TriangleSplineMellinSpectralSummandLedger

/-- TS257 target: the corrected Mellin summand normalization is installed. -/
theorem triangleSplineMellinSpectralSummandTarget :
    TriangleSplineMellinSpectralSummandTarget :=
  Nonempty.intro triangleSplineMellinSpectralSummandLedger

end Goldbach
end TS257
