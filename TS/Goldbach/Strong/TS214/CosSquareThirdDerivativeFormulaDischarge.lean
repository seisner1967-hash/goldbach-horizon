import Mathlib.Tactic
import TS.Goldbach.Strong.TS213.CanonicalSincFourthDirectDirichletRoute

namespace TS214
namespace Goldbach

/-!
# TS214 - Cos-Square Third Derivative Formula Discharge

TS213 reduced the direct non-Plancherel route to the canonical `sinc^4`
identity to five scalar obligations.  TS214 discharges the first and most local
one: the third-derivative formula for

`f(x) = (1 - cos x)^2`.

The sprint proves the first, second, and third derivative formulae explicitly
and then populates `TS213.Goldbach.CosSquareThirdDerivativeFormulaStatement`.

No Dirichlet sine integral, improper integration by parts, scaling identity,
evenness identity, Plancherel theorem, or Goldbach theorem is claimed.
-/

/-- First derivative of `f(x) = (1 - cos x)^2`. -/
theorem cosSquareRemainder_deriv
    (x : Real) :
    deriv TS213.Goldbach.cosSquareRemainder x =
      2 * (1 - Real.cos x) * Real.sin x := by
  unfold TS213.Goldbach.cosSquareRemainder
  simp

/-- Second derivative of `f(x) = (1 - cos x)^2`. -/
theorem cosSquareRemainder_second_deriv
    (x : Real) :
    deriv
      (fun y : Real =>
        deriv TS213.Goldbach.cosSquareRemainder y) x =
      2 * Real.sin x ^ 2 +
        2 * (1 - Real.cos x) * Real.cos x := by
  have hfirst :
      (fun y : Real =>
        deriv TS213.Goldbach.cosSquareRemainder y) =
        fun y : Real => 2 * (1 - Real.cos y) * Real.sin y := by
    funext y
    exact cosSquareRemainder_deriv y
  rw [hfirst]
  have hleft :
      DifferentiableAt Real
        (fun y : Real => 2 * (1 - Real.cos y)) x := by
    fun_prop
  have hright :
      DifferentiableAt Real
        (fun y : Real => Real.sin y) x := by
    fun_prop
  rw [deriv_mul hleft hright]
  simp
  ring

/-- Third derivative of `f(x) = (1 - cos x)^2`. -/
theorem cosSquareRemainder_third_deriv
    (x : Real) :
    deriv
      (fun z : Real =>
        deriv
          (fun y : Real =>
            deriv TS213.Goldbach.cosSquareRemainder y) z) x =
      -2 * Real.sin x + 4 * Real.sin (2 * x) := by
  have hsecond :
      (fun z : Real =>
        deriv
          (fun y : Real =>
            deriv TS213.Goldbach.cosSquareRemainder y) z) =
        fun z : Real =>
          2 * Real.sin z ^ 2 +
            2 * (1 - Real.cos z) * Real.cos z := by
    funext z
    exact cosSquareRemainder_second_deriv z
  rw [hsecond]
  have hleft :
      DifferentiableAt Real
        (fun z : Real => 2 * Real.sin z ^ 2) x := by
    fun_prop
  have hright :
      DifferentiableAt Real
        (fun z : Real => 2 * (1 - Real.cos z) * Real.cos z) x := by
    fun_prop
  rw [deriv_add hleft hright]
  have hright_left :
      DifferentiableAt Real
        (fun z : Real => 2 * (1 - Real.cos z)) x := by
    fun_prop
  have hright_right :
      DifferentiableAt Real
        (fun z : Real => Real.cos z) x := by
    fun_prop
  rw [deriv_mul hright_left hright_right]
  simp [Real.sin_two_mul]
  ring

/-- TS214 discharges the TS213 third-derivative obligation. -/
theorem cosSquareThirdDerivativeFormula :
    TS213.Goldbach.CosSquareThirdDerivativeFormulaStatement := by
  intro x
  exact cosSquareRemainder_third_deriv x

/-- Ledger recording the TS214 derivative discharge. -/
structure CosSquareThirdDerivativeFormulaDischargeLedger where
  ts213_direct_dirichlet_route :
    TS213.Goldbach.CanonicalSincFourthDirectDirichletRouteLedger

  first_derivative_formula :
    forall x : Real,
      deriv TS213.Goldbach.cosSquareRemainder x =
        2 * (1 - Real.cos x) * Real.sin x

  second_derivative_formula :
    forall x : Real,
      deriv
        (fun y : Real =>
          deriv TS213.Goldbach.cosSquareRemainder y) x =
        2 * Real.sin x ^ 2 +
          2 * (1 - Real.cos x) * Real.cos x

  third_derivative_statement :
    Prop

  third_derivative_statement_eq :
    third_derivative_statement =
      TS213.Goldbach.CosSquareThirdDerivativeFormulaStatement

  third_derivative_statement_proved :
    third_derivative_statement

  dirichlet_sine_integral_not_proved :
    True

  improper_triple_ipp_not_proved :
    True

  scaling_identity_not_proved :
    True

  evenness_identity_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved :
    True

  plancherel_not_used :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS214 derivative-discharge ledger. -/
noncomputable def cosSquareThirdDerivativeFormulaDischargeLedger :
    CosSquareThirdDerivativeFormulaDischargeLedger where
  ts213_direct_dirichlet_route :=
    TS213.Goldbach.canonicalSincFourthDirectDirichletRouteLedger
  first_derivative_formula :=
    cosSquareRemainder_deriv
  second_derivative_formula :=
    cosSquareRemainder_second_deriv
  third_derivative_statement :=
    TS213.Goldbach.CosSquareThirdDerivativeFormulaStatement
  third_derivative_statement_eq := rfl
  third_derivative_statement_proved :=
    cosSquareThirdDerivativeFormula
  dirichlet_sine_integral_not_proved := True.intro
  improper_triple_ipp_not_proved := True.intro
  scaling_identity_not_proved := True.intro
  evenness_identity_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  plancherel_not_used := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS214. -/
def CosSquareThirdDerivativeFormulaDischargeTarget :
    Prop :=
  Nonempty CosSquareThirdDerivativeFormulaDischargeLedger

/-- The TS214 derivative-discharge target is populated. -/
theorem cosSquareThirdDerivativeFormulaDischargeTarget :
    CosSquareThirdDerivativeFormulaDischargeTarget :=
  Nonempty.intro cosSquareThirdDerivativeFormulaDischargeLedger

end Goldbach
end TS214
