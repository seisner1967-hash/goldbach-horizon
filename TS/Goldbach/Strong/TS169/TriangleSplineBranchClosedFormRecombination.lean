import Mathlib.Tactic
import TS.Goldbach.Strong.TS168.TriangleSplineBranchIntegralRouteProbe

namespace TS169
namespace Goldbach

/-!
# TS169 - Triangle Spline Branch Closed-Form Recombination

TS168 recorded the fallback branch-integration route for the triangle-spline
Fourier identity.  The final algebraic obligation in that route says that the
two intended branch closed forms recombine to the TS166 squared-sinc target.

This sprint discharges that algebraic recombination only.  It does not prove
the Fourier branch split, either branch integral evaluation, Plancherel, or
the explicit formula.
-/

/-- Euler recombination for the pair of opposite imaginary exponentials. -/
theorem exp_I_mul_add_exp_neg_I_mul
    (a : Complex) :
    Complex.exp (Complex.I * a) +
        Complex.exp (-(Complex.I * a)) =
      2 * Complex.cos a := by
  calc
    Complex.exp (Complex.I * a) +
        Complex.exp (-(Complex.I * a)) =
      Complex.exp (a * Complex.I) +
        Complex.exp ((-a) * Complex.I) := by
        ring_nf
    _ =
      (Complex.cos a + Complex.sin a * Complex.I) +
        (Complex.cos (-a) + Complex.sin (-a) * Complex.I) := by
        rw [Complex.exp_mul_I, Complex.exp_mul_I]
    _ =
      2 * Complex.cos a := by
        simp [Complex.cos_neg, Complex.sin_neg]
        ring

/-- Real half-angle algebra for the pi-scale squared sinc target. -/
theorem two_sub_two_mul_cos_two_mul_div_sq_eq_sinc_sq
    {t : Real}
    (ht : t = 0 -> False) :
    (2 - 2 * Real.cos (2 * t)) / (2 * t) ^ 2 =
      (Real.sin t / t) ^ 2 := by
  have hcos :
      Real.cos (2 * t) =
        1 - 2 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hcos]
  field_simp [ht]
  ring

/--
Nonzero-frequency recombination of the two TS168 branch closed forms.

This is the only algebraically delicate case.  The zero-frequency case is
handled separately in `branchClosedFormRecombination`.
-/
theorem branchClosedFormRecombination_nonzero
    (xi : Real)
    (hxi : 2 * Real.pi * xi = 0 -> False) :
    TS168.Goldbach.leftBranchClosedForm xi +
        TS168.Goldbach.rightBranchClosedForm xi =
      TS166.Goldbach.triangleSplineScaledSincCandidate xi := by
  let t : Real := Real.pi * xi
  have ht : t = 0 -> False := by
    intro ht0
    apply hxi
    dsimp [t] at ht0
    nlinarith
  have hscale : TS165.Goldbach.mathlibFourierTargetScale * xi = 0 -> False := by
    unfold TS165.Goldbach.mathlibFourierTargetScale
    exact ht
  have hfreq : (2 * Real.pi * xi : Real) = 2 * t := by
    dsimp [t]
    ring
  have hpi_or : (Real.pi = 0 \/ xi = 0) -> False := by
    intro h
    cases h with
    | inl hpi =>
        apply hxi
        rw [hpi]
        ring
    | inr hxi0 =>
        apply hxi
        rw [hxi0]
        ring
  have ha :
      TS168.Goldbach.branchAngularFrequency xi = 0 -> False := by
    unfold TS168.Goldbach.branchAngularFrequency
    exact Complex.ofReal_ne_zero.mpr hxi
  have hsum :
      TS168.Goldbach.leftBranchClosedForm xi +
          TS168.Goldbach.rightBranchClosedForm xi =
        (2 -
            (Complex.exp
                (Complex.I * TS168.Goldbach.branchAngularFrequency xi) +
              Complex.exp
                (-(Complex.I * TS168.Goldbach.branchAngularFrequency xi)))) /
          (TS168.Goldbach.branchAngularFrequency xi) ^ 2 := by
    unfold TS168.Goldbach.leftBranchClosedForm
      TS168.Goldbach.rightBranchClosedForm
    rw [if_neg hxi, if_neg hxi]
    field_simp [ha]
    ring_nf
  have hexp :
      Complex.exp
          (Complex.I * TS168.Goldbach.branchAngularFrequency xi) +
        Complex.exp
          (-(Complex.I * TS168.Goldbach.branchAngularFrequency xi)) =
        2 *
          Complex.cos (TS168.Goldbach.branchAngularFrequency xi) := by
    exact exp_I_mul_add_exp_neg_I_mul
      (TS168.Goldbach.branchAngularFrequency xi)
  have hreal :
      (2 - 2 * Real.cos (2 * t)) / (2 * t) ^ 2 =
        (Real.sin t / t) ^ 2 :=
    two_sub_two_mul_cos_two_mul_div_sq_eq_sinc_sq ht
  calc
    TS168.Goldbach.leftBranchClosedForm xi +
        TS168.Goldbach.rightBranchClosedForm xi =
      (2 -
          (Complex.exp
              (Complex.I * TS168.Goldbach.branchAngularFrequency xi) +
            Complex.exp
              (-(Complex.I * TS168.Goldbach.branchAngularFrequency xi)))) /
        (TS168.Goldbach.branchAngularFrequency xi) ^ 2 := hsum
    _ =
      (2 -
          2 * Complex.cos (TS168.Goldbach.branchAngularFrequency xi)) /
        (TS168.Goldbach.branchAngularFrequency xi) ^ 2 := by
        rw [hexp]
    _ =
      (((2 - 2 * Real.cos (2 * t)) / (2 * t) ^ 2 : Real) : Complex) := by
        unfold TS168.Goldbach.branchAngularFrequency
        rw [hfreq]
        simp [Complex.ofReal_cos]
    _ =
      (((Real.sin t / t) ^ 2 : Real) : Complex) := by
        rw [hreal]
    _ =
      TS166.Goldbach.triangleSplineScaledSincCandidate xi := by
        unfold TS166.Goldbach.triangleSplineScaledSincCandidate
          TS164.Goldbach.scaledSincSq
        have hsinc_real :
            (Real.sin t / t) ^ 2 =
              if TS165.Goldbach.mathlibFourierTargetScale * xi = 0 then
                1
              else
                (Real.sin
                    (TS165.Goldbach.mathlibFourierTargetScale * xi) /
                  (TS165.Goldbach.mathlibFourierTargetScale * xi)) ^ 2 := by
          rw [if_neg hscale]
          dsimp [TS165.Goldbach.mathlibFourierTargetScale, t]
        exact congrArg (fun r : Real => (r : Complex)) hsinc_real

/-- The TS168 branch closed forms recombine to the TS166 squared-sinc target. -/
theorem branchClosedFormRecombination :
    TS168.Goldbach.BranchClosedFormRecombinationStatement := by
  intro xi
  by_cases hxi : 2 * Real.pi * xi = 0
  case pos =>
    have hpi : Real.pi * xi = 0 := by
      nlinarith
    unfold TS168.Goldbach.leftBranchClosedForm
      TS168.Goldbach.rightBranchClosedForm
      TS166.Goldbach.triangleSplineScaledSincCandidate
      TS164.Goldbach.scaledSincSq
      TS165.Goldbach.mathlibFourierTargetScale
    simp [hxi, hpi]
    norm_num
  case neg =>
    exact branchClosedFormRecombination_nonzero xi hxi

/-- Ledger for the TS169 closed-form recombination discharge. -/
structure TriangleSplineBranchClosedFormRecombinationLedger where
  ts168_probe :
    TS168.Goldbach.TriangleSplineBranchIntegralRouteProbeLedger

  recombination :
    TS168.Goldbach.BranchClosedFormRecombinationStatement

  branch_split_not_claimed :
    True

  left_integral_evaluation_not_claimed :
    True

  right_integral_evaluation_not_claimed :
    True

  ts166_identification_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS169 closed-form recombination ledger. -/
noncomputable def triangleSplineBranchClosedFormRecombinationLedger :
    TriangleSplineBranchClosedFormRecombinationLedger where
  ts168_probe := TS168.Goldbach.triangleSplineBranchIntegralRouteProbeLedger
  recombination := branchClosedFormRecombination
  branch_split_not_claimed := True.intro
  left_integral_evaluation_not_claimed := True.intro
  right_integral_evaluation_not_claimed := True.intro
  ts166_identification_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS169. -/
def TriangleSplineBranchClosedFormRecombinationTarget : Prop :=
  Nonempty TriangleSplineBranchClosedFormRecombinationLedger

/-- The TS169 closed-form recombination target is populated. -/
theorem triangleSplineBranchClosedFormRecombinationTarget :
    TriangleSplineBranchClosedFormRecombinationTarget :=
  Nonempty.intro triangleSplineBranchClosedFormRecombinationLedger

end Goldbach
end TS169
