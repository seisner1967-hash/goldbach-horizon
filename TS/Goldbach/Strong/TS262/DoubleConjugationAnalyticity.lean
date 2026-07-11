import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic
import TS.Goldbach.Strong.TS261.RiemannZetaVanishingOrderConjugationReduction

/-!
# TS262 - Double Conjugation Analyticity

TS261 reduced zeta order conjugation to two analytic inputs.  This sprint
discharges the generic input: if `f` is complex analytic at `z`, then
`w |-> star (f (star w))` is complex analytic at `star z`.

The proof works at the derivative level.  A complex derivative is restricted
to real scalars, composed on both sides with `Complex.conjCLE`, identified with
the real restriction of multiplication by the conjugate derivative, and then
lifted back to a complex derivative by `hasFDerivAt_of_restrictScalars`.

The local differentiability characterization of complex analyticity completes
the proof.  Schwarz reflection for `riemannZeta` remains the sole TS261 input.
-/

namespace TS262
namespace Goldbach

/-- Complex-linear continuous endomorphisms of the complex line. -/
abbrev ComplexLinearEnd :=
  ContinuousLinearMap (RingHom.id Complex) Complex Complex

/-- Real-linear continuous endomorphisms of the complex plane. -/
abbrev RealLinearEnd :=
  ContinuousLinearMap (RingHom.id Real) Complex Complex

/-- The real derivative obtained by conjugating input and output is complex
    multiplication by the conjugate derivative. -/
theorem doubleConjugation_realDerivative_eq
    (f' : Complex) :
    ((ContinuousLinearMap.smulRight
        (1 : ComplexLinearEnd)
        (star f')).restrictScalars Real) =
      (Complex.conjCLE : RealLinearEnd).comp
        ((SMul.smul f'
          (1 : RealLinearEnd)).comp
          (Complex.conjCLE : RealLinearEnd)) := by
  ext w
  simp [ContinuousLinearMap.coe_restrictScalars,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply]
  have hApply :
      (SMul.smul f' (1 : RealLinearEnd)) ((starRingEnd Complex) w) =
        f' * (starRingEnd Complex) w := by
    change f' * (starRingEnd Complex) w = f' * (starRingEnd Complex) w
    rfl
  rw [hApply]
  simpa using (mul_comm w (star f'))

/-- Exact derivative formula for the double-conjugated function. -/
theorem conjugatedFunction_hasDerivAt
    {f : Complex -> Complex}
    {f' z : Complex}
    (hf : HasDerivAt f f' z) :
    HasDerivAt
      (TS261.Goldbach.conjugatedFunction f)
      (star f')
      (star z) := by
  have hInput :
      HasFDerivAt
        (star : Complex -> Complex)
        (Complex.conjCLE : RealLinearEnd)
        (star z) := by
    simpa using
      (Complex.conjCLE : RealLinearEnd).hasFDerivAt
  have hMiddle :
      HasFDerivAt
        f
        (SMul.smul f' (1 : RealLinearEnd))
        z :=
    hf.complexToReal_fderiv
  have hInner :
      HasFDerivAt
        (fun w => f (star w))
        ((SMul.smul f' (1 : RealLinearEnd)).comp
          (Complex.conjCLE : RealLinearEnd))
        (star z) :=
    by
      have hMiddleAtStarStar :
          HasFDerivAt
            f
            (SMul.smul f' (1 : RealLinearEnd))
            (star (star z)) := by
        simpa using hMiddle
      exact hMiddleAtStarStar.comp (star z) hInput
  have hOutput :
      HasFDerivAt
        (fun w => star (f (star w)))
        ((Complex.conjCLE : RealLinearEnd).comp
          ((SMul.smul f'
            (1 : RealLinearEnd)).comp
            (Complex.conjCLE : RealLinearEnd)))
        (star z) := by
    simpa using
      (Complex.conjCLE : RealLinearEnd).hasFDerivAt.comp
        (star z) hInner
  have hComplex :
      HasFDerivAt
        (fun w => star (f (star w)))
        (ContinuousLinearMap.smulRight
          (1 : ComplexLinearEnd)
          (star f'))
        (star z) :=
    hasFDerivAt_of_restrictScalars Real hOutput
      (doubleConjugation_realDerivative_eq f')
  simpa [TS261.Goldbach.conjugatedFunction] using hComplex.hasDerivAt

/-- Complex differentiability is preserved by double conjugation. -/
theorem conjugatedFunction_differentiableAt
    {f : Complex -> Complex}
    {z : Complex}
    (hf : DifferentiableAt Complex f z) :
    DifferentiableAt Complex
      (TS261.Goldbach.conjugatedFunction f)
      (star z) :=
  (conjugatedFunction_hasDerivAt hf.hasDerivAt).differentiableAt

/-- Formula for the derivative of the double-conjugated function. -/
theorem deriv_conjugatedFunction
    {f : Complex -> Complex}
    {z : Complex}
    (hf : DifferentiableAt Complex f z) :
    deriv (TS261.Goldbach.conjugatedFunction f) (star z) =
      star (deriv f z) :=
  (conjugatedFunction_hasDerivAt hf.hasDerivAt).deriv

/-- Complex analyticity is preserved by double conjugation. -/
theorem conjugatedFunction_analyticAt
    {f : Complex -> Complex}
    {z : Complex}
    (hf : AnalyticAt Complex f z) :
    AnalyticAt Complex
      (TS261.Goldbach.conjugatedFunction f)
      (star z) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hPulled := TS261.Goldbach.eventually_precomp_star hf
  filter_upwards [hPulled] with w hw
  have hDiff :=
    conjugatedFunction_differentiableAt
      (f := f) (z := star w) hw
  simpa using hDiff

/-- Double conjugation gives an equivalence of local analyticity. -/
theorem conjugatedFunction_analyticAt_iff
    {f : Complex -> Complex}
    {z : Complex} :
    AnalyticAt Complex
        (TS261.Goldbach.conjugatedFunction f)
        (star z) <->
      AnalyticAt Complex f z := by
  constructor
  case mp =>
    intro hConjugated
    have hTwice :=
      conjugatedFunction_analyticAt
        (f := TS261.Goldbach.conjugatedFunction f)
        (z := star z)
        hConjugated
    simpa [TS261.Goldbach.conjugatedFunction_involutive] using hTwice
  case mpr =>
    intro hf
    exact conjugatedFunction_analyticAt hf

/-- The first TS261 analytic input is now discharged. -/
theorem conjugatedFunctionAnalyticityStatement :
    TS261.Goldbach.ConjugatedFunctionAnalyticityStatement := by
  intro f z hf
  exact conjugatedFunction_analyticAt hf

/-- A Schwarz-reflection proof now suffices to build the complete TS261 input. -/
noncomputable def ts261Inputs_of_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement) :
    TS261.Goldbach.RiemannZetaVanishingOrderConjugationInputContract where
  conjugated_function_analyticity :=
    conjugatedFunctionAnalyticityStatement
  riemann_zeta_schwarz_reflection := hSchwarz

/-- Schwarz reflection alone now discharges the TS260 zeta-order target. -/
theorem riemannZetaVanishingOrderConjugation_of_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement)
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract) :
    TS260.Goldbach.RiemannZetaVanishingOrderConjugationStatement C :=
  TS261.Goldbach.riemannZetaVanishingOrderConjugation_of_inputs
    (ts261Inputs_of_schwarzReflection hSchwarz) C

/-- Schwarz reflection and a realization give conjugate multiplicities. -/
theorem multiplicityConjugation_of_realization_and_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract) :
    TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement R.base :=
  TS261.Goldbach.multiplicityConjugation_of_realization_and_inputs
    (ts261Inputs_of_schwarzReflection hSchwarz) R

/-- Schwarz reflection and a realization build the TS259 extension. -/
noncomputable def ts259Extension_of_realization_and_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract) :
    TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract :=
  TS261.Goldbach.ts259Extension_of_realization_and_inputs
    (ts261Inputs_of_schwarzReflection hSchwarz) R

/-- Schwarz reflection routes a realization to finite-sum reality. -/
theorem realizedTruncation_zeroSumReality_of_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS261.Goldbach.realizedTruncation_zeroSumReality_of_inputs
    (ts261Inputs_of_schwarzReflection hSchwarz) R truncation

/-- Schwarz reflection routes a realization to lossless real projection. -/
theorem realizedTruncation_realProjectionLossless_of_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      R.base truncation X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        R.base truncation X :=
  TS261.Goldbach.realizedTruncation_realProjectionLossless_of_inputs
    (ts261Inputs_of_schwarzReflection hSchwarz) R truncation X

/-- Schwarz reflection routes a realization to exact absolute-value transport. -/
theorem realizedTruncation_realAbs_eq_complexAbs_of_schwarzReflection
    (hSchwarz : TS261.Goldbach.RiemannZetaSchwarzReflectionStatement)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          R.base truncation X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          R.base truncation X) :=
  TS261.Goldbach.realizedTruncation_realAbs_eq_complexAbs_of_inputs
    (ts261Inputs_of_schwarzReflection hSchwarz) R truncation X

/-- Ledger recording the generic analyticity discharge. -/
structure DoubleConjugationAnalyticityLedger where
  ts261_order_conjugation_reduction :
    TS261.Goldbach.RiemannZetaVanishingOrderConjugationReductionLedger

  derivative_transport :
    forall
      {f : Complex -> Complex}
      {f' z : Complex},
      HasDerivAt f f' z ->
        HasDerivAt
          (TS261.Goldbach.conjugatedFunction f)
          (star f')
          (star z)

  analytic_at_equivalence :
    forall
      {f : Complex -> Complex}
      {z : Complex},
      AnalyticAt Complex
          (TS261.Goldbach.conjugatedFunction f)
          (star z) <->
        AnalyticAt Complex f z

  conjugated_function_analyticity_proved :
    TS261.Goldbach.ConjugatedFunctionAnalyticityStatement

  remaining_schwarz_reflection_reduction :
    TS261.Goldbach.RiemannZetaSchwarzReflectionStatement ->
      forall C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract,
        TS260.Goldbach.RiemannZetaVanishingOrderConjugationStatement C

  schwarz_reflection_not_proved : True
  concrete_realization_not_constructed : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS262 ledger. -/
noncomputable def doubleConjugationAnalyticityLedger :
    DoubleConjugationAnalyticityLedger where
  ts261_order_conjugation_reduction :=
    TS261.Goldbach.riemannZetaVanishingOrderConjugationReductionLedger
  derivative_transport := conjugatedFunction_hasDerivAt
  analytic_at_equivalence := conjugatedFunction_analyticAt_iff
  conjugated_function_analyticity_proved :=
    conjugatedFunctionAnalyticityStatement
  remaining_schwarz_reflection_reduction :=
    riemannZetaVanishingOrderConjugation_of_schwarzReflection
  schwarz_reflection_not_proved := True.intro
  concrete_realization_not_constructed := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS262. -/
def DoubleConjugationAnalyticityTarget : Prop :=
  Nonempty DoubleConjugationAnalyticityLedger

/-- TS262 target: generic double-conjugation analyticity is proved. -/
theorem doubleConjugationAnalyticityTarget :
    DoubleConjugationAnalyticityTarget :=
  Nonempty.intro doubleConjugationAnalyticityLedger

end Goldbach
end TS262
