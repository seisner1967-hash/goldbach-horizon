import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.ExpDecay
import TS.Goldbach.Strong.TS230.DampedDirichletEvaluationReduction

/-!
# TS231 - Laplace Sine Transform Discharge

TS230 reduced the damped Dirichlet evaluation to two analytic inputs.  This
sprint discharges the first input: the one-sided Laplace transform of `sin`.
-/

namespace TS231
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- Explicit primitive for `exp(-s*x) * sin x`. -/
noncomputable def laplaceSinePrimitive (s x : Real) : Real :=
  -Real.exp (-(s * x)) *
    (s * Real.sin x + Real.cos x) /
      (1 + s ^ 2)

/-- The denominator in the Laplace sine primitive is nonzero. -/
theorem one_add_sq_pos (s : Real) :
    0 < (1 + s ^ 2 : Real) := by
  nlinarith [sq_nonneg s]

/-- The denominator in the Laplace sine primitive is nonzero. -/
theorem one_add_sq_ne_zero (s : Real) :
    Ne (1 + s ^ 2 : Real) 0 := by
  exact ne_of_gt (one_add_sq_pos s)

/-- The explicit primitive differentiates to the Laplace sine kernel. -/
theorem hasDerivAt_laplaceSinePrimitive
    (s x : Real) :
    HasDerivAt
      (laplaceSinePrimitive s)
      (TS230.Goldbach.laplaceSineKernel s x)
      x := by
  have hden : Ne (1 + s ^ 2 : Real) 0 :=
    one_add_sq_ne_zero s
  have hExp :
      HasDerivAt
        (fun y : Real => Real.exp (-(s * y)))
        ((-s) * Real.exp (-(s * x)))
        x := by
    have hlin :
        HasDerivAt (fun y : Real => (-s) * y) (-s) x :=
      by
        simpa using (hasDerivAt_id x).const_mul (-s)
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hlin.exp
  have hTrig :
      HasDerivAt
        (fun y : Real => s * Real.sin y + Real.cos y)
        (s * Real.cos x - Real.sin x)
        x := by
    simpa [sub_eq_add_neg] using
      ((Real.hasDerivAt_sin x).const_mul s).add
        (Real.hasDerivAt_cos x)
  have hProd :
      HasDerivAt
        (fun y : Real =>
          Real.exp (-(s * y)) *
            (s * Real.sin y + Real.cos y))
        ((-s) * Real.exp (-(s * x)) *
            (s * Real.sin x + Real.cos x) +
          Real.exp (-(s * x)) *
            (s * Real.cos x - Real.sin x))
        x :=
    hExp.mul hTrig
  convert hProd.const_mul (-(1 / (1 + s ^ 2))) using 1
  next =>
    funext y
    unfold laplaceSinePrimitive
    field_simp [hden]
  next =>
    unfold TS230.Goldbach.laplaceSineKernel
    field_simp [hden]
    ring

/-- The finite partial Laplace sine integral has the expected boundary term. -/
theorem laplaceSinePartialIntegral_eq_boundary
    (s T : Real) :
    TS230.Goldbach.laplaceSinePartialIntegral s T =
      (1 : Real) / (1 + s ^ 2) -
        Real.exp (-(s * T)) *
          (s * Real.sin T + Real.cos T) /
            (1 + s ^ 2) := by
  have hcont :
      ContinuousOn
        (fun x : Real => TS230.Goldbach.laplaceSineKernel s x)
        (Set.uIcc 0 T) := by
    unfold TS230.Goldbach.laplaceSineKernel
    have hcont_all :
        Continuous
          (fun x : Real => Real.exp (-(s * x)) * Real.sin x) := by
      fun_prop
    exact hcont_all.continuousOn
  have hderiv :
      forall x : Real, Set.Mem (Set.uIcc 0 T) x ->
        HasDerivAt
          (laplaceSinePrimitive s)
          (TS230.Goldbach.laplaceSineKernel s x)
          x := by
    intro x hx
    exact hasDerivAt_laplaceSinePrimitive s x
  have hFTC :
      TS230.Goldbach.laplaceSinePartialIntegral s T =
        laplaceSinePrimitive s T - laplaceSinePrimitive s 0 := by
    unfold TS230.Goldbach.laplaceSinePartialIntegral
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  rw [hFTC]
  unfold laplaceSinePrimitive
  simp [one_add_sq_ne_zero s]
  ring

/-- The exponential boundary term vanishes at infinity for positive `s`. -/
theorem laplaceSineBoundaryTerm_tendsto_zero
    (s : Real) (hs : 0 < s) :
    Tendsto
      (fun T : Real =>
        Real.exp (-(s * T)) *
          (s * Real.sin T + Real.cos T) /
            (1 + s ^ 2))
      atTop
      (nhds (0 : Real)) := by
  have hExp :
      Tendsto (fun T : Real => Real.exp (-(s * T)))
        atTop (nhds (0 : Real)) := by
    have hlin :
        Tendsto (fun T : Real => (-s) * T) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hExp0 :
        Tendsto (fun T : Real => Real.exp ((-s) * T))
          atTop (nhds (0 : Real)) :=
      Real.tendsto_exp_atBot.comp hlin
    simpa [neg_mul] using hExp0
  have hCoeffBound :
      forall T : Real,
        |(s * Real.sin T + Real.cos T) / (1 + s ^ 2)| <=
          (s + 1) / (1 + s ^ 2) := by
    intro T
    have hden_pos : 0 < (1 + s ^ 2 : Real) :=
      one_add_sq_pos s
    have hsin : |Real.sin T| <= (1 : Real) :=
      Real.abs_sin_le_one T
    have hcos : |Real.cos T| <= (1 : Real) :=
      Real.abs_cos_le_one T
    have hs_abs : |s| = s := abs_of_pos hs
    have hnum :
        |s * Real.sin T + Real.cos T| <= s + 1 := by
      calc
        |s * Real.sin T + Real.cos T|
            <= |s * Real.sin T| + |Real.cos T| := abs_add _ _
        _ = |s| * |Real.sin T| + |Real.cos T| := by
          rw [abs_mul]
        _ <= s + 1 := by
          rw [hs_abs]
          nlinarith [hs, hsin, hcos, abs_nonneg (Real.sin T),
            abs_nonneg (Real.cos T)]
    rw [abs_div, abs_of_pos hden_pos]
    exact div_le_div_of_nonneg_right hnum hden_pos.le
  have hProd :
      Tendsto
        (fun T : Real =>
          ((s * Real.sin T + Real.cos T) / (1 + s ^ 2)) *
            Real.exp (-(s * T)))
        atTop
        (nhds (0 : Real)) := by
    exact
      bdd_le_mul_tendsto_zero'
        ((s + 1) / (1 + s ^ 2))
        (Eventually.of_forall hCoeffBound)
        hExp
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hProd

/-- The Laplace transform of the sine function on the positive half-line. -/
theorem laplaceSineTransform :
    TS230.Goldbach.LaplaceSineTransformStatement := by
  intro s hs
  have hBoundary :
      Tendsto
        (fun T : Real =>
          Real.exp (-(s * T)) *
            (s * Real.sin T + Real.cos T) /
              (1 + s ^ 2))
        atTop
        (nhds (0 : Real)) :=
    laplaceSineBoundaryTerm_tendsto_zero s hs
  have hValue :
      Tendsto
        (fun T : Real =>
          (1 : Real) / (1 + s ^ 2) -
            Real.exp (-(s * T)) *
              (s * Real.sin T + Real.cos T) /
                (1 + s ^ 2))
        atTop
        (nhds ((1 : Real) / (1 + s ^ 2) - 0)) := by
    exact tendsto_const_nhds.sub hBoundary
  simpa using
    hValue.congr'
      (Eventually.of_forall fun T =>
        (laplaceSinePartialIntegral_eq_boundary s T).symm)

/-- Ledger recording the TS231 Laplace sine transform discharge. -/
structure LaplaceSineTransformDischargeLedger where
  ts230_reduction :
    TS230.Goldbach.DampedDirichletEvaluationReductionEvidence

  laplace_sine_transform_statement : Prop
  laplace_sine_transform_statement_eq :
    laplace_sine_transform_statement =
      TS230.Goldbach.LaplaceSineTransformStatement
  laplace_sine_transform_proved :
    laplace_sine_transform_statement

  primitive_has_deriv :
    forall s x : Real,
      HasDerivAt
        (laplaceSinePrimitive s)
        (TS230.Goldbach.laplaceSineKernel s x)
        x
  finite_partial_integral_formula :
    forall s T : Real,
      TS230.Goldbach.laplaceSinePartialIntegral s T =
        (1 : Real) / (1 + s ^ 2) -
          Real.exp (-(s * T)) *
            (s * Real.sin T + Real.cos T) /
              (1 + s ^ 2)
  boundary_term_vanishing :
    forall s : Real, 0 < s ->
      Tendsto
        (fun T : Real =>
          Real.exp (-(s * T)) *
            (s * Real.sin T + Real.cos T) /
              (1 + s ^ 2))
        atTop
        (nhds (0 : Real))

  fubini_bridge_not_proved : True
  damped_dirichlet_evaluation_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  dirichlet_cutoff_value_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS231 ledger. -/
noncomputable def laplaceSineTransformDischargeLedger :
    LaplaceSineTransformDischargeLedger where
  ts230_reduction :=
    TS230.Goldbach.dampedDirichletEvaluationReductionEvidence
  laplace_sine_transform_statement :=
    TS230.Goldbach.LaplaceSineTransformStatement
  laplace_sine_transform_statement_eq := rfl
  laplace_sine_transform_proved := laplaceSineTransform
  primitive_has_deriv := hasDerivAt_laplaceSinePrimitive
  finite_partial_integral_formula := laplaceSinePartialIntegral_eq_boundary
  boundary_term_vanishing := laplaceSineBoundaryTerm_tendsto_zero
  fubini_bridge_not_proved := True.intro
  damped_dirichlet_evaluation_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  dirichlet_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS231. -/
def LaplaceSineTransformDischargeTarget : Prop :=
  Nonempty LaplaceSineTransformDischargeLedger

/-- TS231 target: the Laplace sine transform input from TS230 is discharged. -/
theorem laplaceSineTransformDischargeTarget :
    LaplaceSineTransformDischargeTarget :=
  Nonempty.intro laplaceSineTransformDischargeLedger

end Goldbach
end TS231
