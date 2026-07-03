import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS214.CosSquareThirdDerivativeFormulaDischarge
import TS.Goldbach.Strong.TS219.CosSquareTripleIPPCutoffReformulation

namespace TS220
namespace Goldbach

open MeasureTheory

/-!
# TS220 - Cos-Square IPP Primitive Derivative Bridge

TS219 reformulated the triple integration-by-parts target as a finite cutoff
identity plus boundary terms.  This sprint proves the compact local calculus
core behind that identity.

Instead of applying `intervalIntegral.integral_by_parts` three times, TS220
defines the primitive

`P(x) = -f(x)/(3*x^3) - f'(x)/(6*x^2) - f''(x)/(6*x)`,

with `f(x) = (1 - cos x)^2`, and proves pointwise away from zero that

`P'(x) = f(x)/x^4 - (1/6) * f'''(x)/x`.

This is the derivative identity needed for the future finite-interval FTC
discharge of `TS219.Goldbach.CosSquareFiniteTripleIPPStatement`.

TS220 does not yet prove the finite IPP statement, the equality between this
primitive jump and the TS219 boundary sum, any boundary vanishing, any
Dirichlet cutoff value, the canonical `sinc^4` value, Plancherel, or Goldbach.
-/

/-- Model for the first derivative of `f(x) = (1 - cos x)^2`. -/
noncomputable def cosSquareFirstDerivativeModel
    (x : Real) :
    Real :=
  2 * (1 - Real.cos x) * Real.sin x

/-- Model for the second derivative of `f(x) = (1 - cos x)^2`. -/
noncomputable def cosSquareSecondDerivativeModel
    (x : Real) :
    Real :=
  2 * Real.sin x ^ 2 + 2 * (1 - Real.cos x) * Real.cos x

/-- Model for the third derivative of `f(x) = (1 - cos x)^2`. -/
noncomputable def cosSquareThirdDerivativeModel
    (x : Real) :
    Real :=
  -2 * Real.sin x + 4 * Real.sin (2 * x)

/-- The primitive used for the finite triple IPP calculation. -/
noncomputable def cosSquareIPPPrimitive
    (x : Real) :
    Real :=
  (-(1 / 3 : Real)) *
      TS213.Goldbach.cosSquareRemainder x * x ^ (-3 : Int) +
    (-(1 / 6 : Real)) *
      cosSquareFirstDerivativeModel x * x ^ (-2 : Int) +
      (-(1 / 6 : Real)) *
        cosSquareSecondDerivativeModel x * x ^ (-1 : Int)

/-- First derivative as a `HasDerivAt` statement, derived from TS214. -/
theorem cosSquareRemainder_hasDerivAt
    (x : Real) :
    HasDerivAt
      TS213.Goldbach.cosSquareRemainder
      (cosSquareFirstDerivativeModel x)
      x := by
  have hdiff :
      DifferentiableAt Real TS213.Goldbach.cosSquareRemainder x := by
    unfold TS213.Goldbach.cosSquareRemainder
    fun_prop
  have hderiv :
      deriv TS213.Goldbach.cosSquareRemainder x =
        cosSquareFirstDerivativeModel x := by
    simpa [cosSquareFirstDerivativeModel]
      using TS214.Goldbach.cosSquareRemainder_deriv x
  simpa [hderiv] using hdiff.hasDerivAt

/-- Second derivative as a `HasDerivAt` statement, derived from TS214. -/
theorem cosSquareFirstDerivativeModel_hasDerivAt
    (x : Real) :
    HasDerivAt
      cosSquareFirstDerivativeModel
      (cosSquareSecondDerivativeModel x)
      x := by
  have hdiff :
      DifferentiableAt Real cosSquareFirstDerivativeModel x := by
    unfold cosSquareFirstDerivativeModel
    fun_prop
  have hfirst :
      (fun y : Real =>
        deriv TS213.Goldbach.cosSquareRemainder y) =
        cosSquareFirstDerivativeModel := by
    funext y
    exact
      (TS214.Goldbach.cosSquareRemainder_deriv y).trans
        (by simp [cosSquareFirstDerivativeModel])
  have hderiv :
      deriv cosSquareFirstDerivativeModel x =
        cosSquareSecondDerivativeModel x := by
    simpa [hfirst, cosSquareSecondDerivativeModel]
      using TS214.Goldbach.cosSquareRemainder_second_deriv x
  simpa [hderiv] using hdiff.hasDerivAt

/-- Third derivative as a `HasDerivAt` statement, derived from TS214. -/
theorem cosSquareSecondDerivativeModel_hasDerivAt
    (x : Real) :
    HasDerivAt
      cosSquareSecondDerivativeModel
      (cosSquareThirdDerivativeModel x)
      x := by
  have hdiff :
      DifferentiableAt Real cosSquareSecondDerivativeModel x := by
    unfold cosSquareSecondDerivativeModel
    fun_prop
  have hsecond :
      (fun z : Real =>
        deriv
          (fun y : Real =>
            deriv TS213.Goldbach.cosSquareRemainder y) z) =
        cosSquareSecondDerivativeModel := by
    funext z
    exact
      (TS214.Goldbach.cosSquareRemainder_second_deriv z).trans
        (by simp [cosSquareSecondDerivativeModel])
  have hderiv :
      deriv cosSquareSecondDerivativeModel x =
        cosSquareThirdDerivativeModel x := by
    simpa [hsecond, cosSquareThirdDerivativeModel]
      using TS214.Goldbach.cosSquareRemainder_third_deriv x
  simpa [hderiv] using hdiff.hasDerivAt

private theorem normalizeLeft
    (x c s : Real) :
    -(c * x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 1296) -
          c * x ^ 5 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * s * 864 +
        c ^ 2 * x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 648 +
      x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 648 +
    x ^ 5 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * s * 216 =
      -(c * x ^ 16 * 1296) - c * x ^ 19 * s * 864 +
        c ^ 2 * x ^ 16 * 648 + x ^ 16 * 648 + x ^ 19 * s * 216 := by
  ring_nf

private theorem normalizeRight
    (x c s : Real) :
    -(c * x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 864) -
          c * x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 1296 +
        c ^ 2 * x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 648 +
      x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 216 +
    x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 648 =
      -(c * x ^ 16 * 1296) - c * x ^ 19 * s * 864 +
        c ^ 2 * x ^ 16 * 648 + x ^ 16 * 648 + x ^ 19 * s * 216 := by
  ring_nf

private theorem normalizeLeftTarget
    (x c s : Real) :
    -(c * x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 1296) -
            c * x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 864 +
          c ^ 2 * x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 648 +
        x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 648 +
      x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 216 =
    -(c * (x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2) * 1296) -
            c * (x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2) * 864 +
          c ^ 2 * (x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2) * 648 +
        x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 648 +
      x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 216 := by
  ring_nf

private theorem normalizeRightTarget
    (x c s : Real) :
    -(c * x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 864) -
            c * x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 1296 +
          c ^ 2 * x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 648 +
        x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 216 +
      x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 648 =
    -(c * (x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2) * 864) -
          c * (x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2) * 1296 +
        c ^ 2 * (x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2) * 648 +
      x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2 * 216 +
    x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2 * 648 := by
  ring_nf

/--
The local derivative identity for the primitive behind the finite triple IPP.

This is the compact calculus core of the TS219 finite cutoff statement.
-/
theorem cosSquareIPPPrimitive_hasDerivAt
    (x : Real) (hx : Ne x 0) :
    HasDerivAt
      cosSquareIPPPrimitive
      (TS213.Goldbach.cosSquareHaarKernel x -
        (1 / 6 : Real) * TS213.Goldbach.cosSquareThirdDerivativeKernel x)
      x := by
  have hz3 :
      HasDerivAt
        (fun y : Real => y ^ (-3 : Int))
        ((-3 : Real) * x ^ (-4 : Int))
        x := by
    simpa using hasDerivAt_zpow (-3 : Int) x (Or.inl hx)
  have hz2 :
      HasDerivAt
        (fun y : Real => y ^ (-2 : Int))
        ((-2 : Real) * x ^ (-3 : Int))
        x := by
    simpa using hasDerivAt_zpow (-2 : Int) x (Or.inl hx)
  have hz1 :
      HasDerivAt
        (fun y : Real => y ^ (-1 : Int))
        ((-1 : Real) * x ^ (-2 : Int))
        x := by
    simpa using hasDerivAt_zpow (-1 : Int) x (Or.inl hx)
  have hterm1 :
      HasDerivAt
        (fun y : Real =>
          (-(1 / 3 : Real)) *
            (TS213.Goldbach.cosSquareRemainder y * y ^ (-3 : Int)))
        ((-(1 / 3 : Real)) *
          (cosSquareFirstDerivativeModel x * x ^ (-3 : Int) +
            TS213.Goldbach.cosSquareRemainder x *
              ((-3 : Real) * x ^ (-4 : Int))))
        x := by
    exact HasDerivAt.const_mul (-(1 / 3 : Real))
      ((cosSquareRemainder_hasDerivAt x).mul hz3)
  have hterm2 :
      HasDerivAt
        (fun y : Real =>
          (-(1 / 6 : Real)) *
            (cosSquareFirstDerivativeModel y * y ^ (-2 : Int)))
        ((-(1 / 6 : Real)) *
          (cosSquareSecondDerivativeModel x * x ^ (-2 : Int) +
            cosSquareFirstDerivativeModel x *
              ((-2 : Real) * x ^ (-3 : Int))))
        x := by
    exact HasDerivAt.const_mul (-(1 / 6 : Real))
      ((cosSquareFirstDerivativeModel_hasDerivAt x).mul hz2)
  have hterm3 :
      HasDerivAt
        (fun y : Real =>
          (-(1 / 6 : Real)) *
            (cosSquareSecondDerivativeModel y * y ^ (-1 : Int)))
        ((-(1 / 6 : Real)) *
          (cosSquareThirdDerivativeModel x * x ^ (-1 : Int) +
            cosSquareSecondDerivativeModel x *
              ((-1 : Real) * x ^ (-2 : Int))))
        x := by
    exact HasDerivAt.const_mul (-(1 / 6 : Real))
      ((cosSquareSecondDerivativeModel_hasDerivAt x).mul hz1)
  convert hterm1.add (hterm2.add hterm3) using 1
  next =>
    funext y
    unfold cosSquareIPPPrimitive
    ring
  next =>
    unfold cosSquareFirstDerivativeModel
    unfold cosSquareSecondDerivativeModel
    unfold cosSquareThirdDerivativeModel
    unfold TS213.Goldbach.cosSquareRemainder
    unfold TS213.Goldbach.cosSquareHaarKernel
    unfold TS213.Goldbach.cosSquareThirdDerivativeKernel
    simp [hx, Real.sin_two_mul]
    simp [TS213.Goldbach.cosSquareRemainder, inv_pow]
    field_simp [hx]
    set c : Real := Real.cos x
    set s : Real := Real.sin x
    clear_value c
    clear_value s
    ring_nf
    set A : Real :=
      x ^ 2 * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2
    set B : Real :=
      x ^ 6 * (x ^ 3) ^ 2 * (x ^ 2) ^ 2
    set C : Real :=
      x ^ 5 * s * (x ^ 3) ^ 2 * x ^ 4 * (x ^ 2) ^ 2
    have hdiff :
        A - B = 0 := by
      unfold A B
      ring
    have htarget :
        -(c * A * 1296) - c * C * 864 +
              c ^ 2 * A * 648 + A * 648 + C * 216 =
          -(c * C * 864) - c * B * 1296 +
              c ^ 2 * B * 648 + C * 216 + B * 648 := by
      linear_combination ((-1296 * c + 648 * c ^ 2 + 648) * hdiff)
    convert htarget using 1
    next =>
      simp [A, B, C]
      exact normalizeLeftTarget x c s
    next =>
      simp [A, B, C]
      exact normalizeRightTarget x c s

/-- Ledger recording the TS220 primitive derivative bridge. -/
structure CosSquareIPPPrimitiveDerivativeBridgeLedger where
  ts219_cutoff_reformulation :
    TS219.Goldbach.CosSquareTripleIPPCutoffReformulationLedger

  primitive_defined :
    True

  primitive_has_deriv_at :
    forall x : Real,
      Ne x 0 ->
        HasDerivAt
          cosSquareIPPPrimitive
          (TS213.Goldbach.cosSquareHaarKernel x -
            (1 / 6 : Real) *
              TS213.Goldbach.cosSquareThirdDerivativeKernel x)
          x

  finite_triple_ipp_statement :
    Prop

  finite_triple_ipp_statement_eq :
    finite_triple_ipp_statement =
      TS219.Goldbach.CosSquareFiniteTripleIPPStatement

  finite_triple_ipp_not_proved :
    True

  primitive_jump_boundary_sum_not_proved :
    True

  boundary_vanishing_not_proved :
    True

  third_derivative_cutoff_value_not_proved :
    True

  dirichlet_cutoff_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS220 primitive derivative bridge ledger. -/
noncomputable def cosSquareIPPPrimitiveDerivativeBridgeLedger :
    CosSquareIPPPrimitiveDerivativeBridgeLedger where
  ts219_cutoff_reformulation :=
    TS219.Goldbach.cosSquareTripleIPPCutoffReformulationLedger
  primitive_defined := True.intro
  primitive_has_deriv_at :=
    cosSquareIPPPrimitive_hasDerivAt
  finite_triple_ipp_statement :=
    TS219.Goldbach.CosSquareFiniteTripleIPPStatement
  finite_triple_ipp_statement_eq := rfl
  finite_triple_ipp_not_proved := True.intro
  primitive_jump_boundary_sum_not_proved := True.intro
  boundary_vanishing_not_proved := True.intro
  third_derivative_cutoff_value_not_proved := True.intro
  dirichlet_cutoff_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS220. -/
def CosSquareIPPPrimitiveDerivativeBridgeTarget :
    Prop :=
  Nonempty CosSquareIPPPrimitiveDerivativeBridgeLedger

theorem cosSquareIPPPrimitiveDerivativeBridgeTarget :
    CosSquareIPPPrimitiveDerivativeBridgeTarget :=
  Nonempty.intro cosSquareIPPPrimitiveDerivativeBridgeLedger

end Goldbach
end TS220
