import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import TS.Goldbach.Strong.TS168.TriangleSplineBranchIntegralRouteProbe

namespace TS170
namespace Goldbach

open MeasureTheory

/-!
# TS170 - Triangle Spline Right Branch Integral Evaluation

TS169 discharged the closed-form recombination at the end of the TS168
branch-integration route.  This sprint discharges one analytic obligation in
that route: the right branch integral over `[0,1]`.

The proof is intentionally local.  It proves only
`RightBranchIntegralEvaluationStatement`, splitting zero frequency from
nonzero frequency and using an explicit elementary primitive for the nonzero
case.  It does not prove the left branch evaluation, the global branch split,
Plancherel, or the explicit formula.
-/

/-- Nonzero-frequency primitive parameter for the right branch. -/
noncomputable def rightBranchA
    (xi : Real) :
    Complex :=
  -(Complex.I * TS168.Goldbach.branchAngularFrequency xi)

/-- The primitive used for the nonzero right branch integral. -/
noncomputable def rightBranchPrimitive
    (a : Complex)
    (x : Real) :
    Complex :=
  Complex.exp (a * (x : Complex)) *
    (((1 - x : Real) : Complex) / a + 1 / (a ^ 2))

/-- The complex affine right branch has derivative `-1`. -/
theorem rightBranchAffine_hasDerivAt
    (x : Real) :
    HasDerivAt
      (fun y : Real => ((1 - y : Real) : Complex))
      (-1 : Complex)
      x := by
  simpa [Complex.ofReal_sub] using
    ((hasDerivAt_const (x := x) (c := (1 : Complex))).sub
      (Complex.ofRealCLM.hasDerivAt (x := x)))

/-- Derivative of the explicit nonzero-frequency primitive. -/
theorem rightBranchPrimitive_hasDerivAt
    (a : Complex)
    (ha : a = 0 -> False)
    (x : Real) :
    HasDerivAt
      (fun y : Real => rightBranchPrimitive a y)
      (Complex.exp (a * (x : Complex)) * ((1 - x : Real) : Complex))
      x := by
  have hlin :
      HasDerivAt (fun y : Real => a * (y : Complex)) a x := by
    simpa using
      (Complex.ofRealCLM.hasDerivAt.const_mul a :
        HasDerivAt
          (fun y : Real => a * ((Complex.ofRealCLM) y))
          (a * Complex.ofRealCLM 1)
          x)
  have hexp :
      HasDerivAt
        (fun y : Real => Complex.exp (a * (y : Complex)))
        (Complex.exp (a * (x : Complex)) * a)
        x := by
    simpa using hlin.cexp
  have hfactor :
      HasDerivAt
        (fun y : Real =>
          ((1 - y : Real) : Complex) / a + 1 / (a ^ 2))
        ((-1 : Complex) / a)
        x := by
    convert
      (rightBranchAffine_hasDerivAt x).div_const a |>.add
        (hasDerivAt_const x (1 / (a ^ 2))) using 1
    simp [one_div]
  have hprod := hexp.mul hfactor
  unfold rightBranchPrimitive
  convert hprod using 1
  field_simp [ha]
  ring_nf

/-- Elementary FTC evaluation of the abstract right-branch primitive. -/
theorem rightBranchPrimitive_intervalIntegral
    (a : Complex)
    (ha : a = 0 -> False) :
    intervalIntegral
      (fun x : Real =>
        Complex.exp (a * (x : Complex)) *
          ((1 - x : Real) : Complex))
      (0 : Real)
      1
      (volume : Measure Real)
      =
    Complex.exp a * (1 / (a ^ 2)) -
      (1 / a + 1 / (a ^ 2)) := by
  let F : Real -> Complex := fun x =>
    rightBranchPrimitive a x
  have hderiv :
      forall x : Real, (Set.uIcc (0 : Real) 1) x ->
        HasDerivAt F
          (Complex.exp (a * (x : Complex)) *
            ((1 - x : Real) : Complex))
          x := by
    intro x _hx
    dsimp [F]
    exact rightBranchPrimitive_hasDerivAt a ha x
  have hint :
      IntervalIntegrable
        (fun x : Real =>
          Complex.exp (a * (x : Complex)) *
            ((1 - x : Real) : Complex))
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : Real))
      (b := 1)
      (f := F)
      (f' := fun x : Real =>
        Complex.exp (a * (x : Complex)) *
          ((1 - x : Real) : Complex))
      hderiv
      hint
  simpa [F, rightBranchPrimitive] using hftc

/-- Zero-frequency right branch integral. -/
theorem rightBranchAffineIntegral_zero :
    intervalIntegral
      (fun x : Real => ((1 - x : Real) : Complex))
      (0 : Real)
      1
      (volume : Measure Real)
      =
    (1 / 2 : Complex) := by
  rw [intervalIntegral.integral_ofReal]
  have hconst :
      IntervalIntegrable
        (fun _x : Real => (1 : Real))
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  have hid :
      IntervalIntegrable
        (fun x : Real => x)
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  rw [intervalIntegral.integral_sub hconst hid]
  norm_num [integral_one, integral_id]

/-- At zero frequency, the TS168 right-branch integrand reduces to `1-x`. -/
theorem rightBranchFourierIntegral_zero
    (xi : Real)
    (hxi : 2 * Real.pi * xi = 0) :
    TS168.Goldbach.rightBranchFourierIntegral xi =
      intervalIntegral
        (fun x : Real => ((1 - x : Real) : Complex))
        (0 : Real)
        1
        (volume : Measure Real) := by
  unfold TS168.Goldbach.rightBranchFourierIntegral
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold TS168.Goldbach.rightBranchFourierIntegrand
    TS168.Goldbach.mathlibForwardFourierKernel
    TS168.Goldbach.rightTriangleSplineBranchAsComplex
  have harg : (-2 * Real.pi * x * xi : Real) = 0 := by
    calc
      (-2 * Real.pi * x * xi : Real) =
          -x * (2 * Real.pi * xi) := by
          ring
      _ = 0 := by
          rw [hxi]
          ring
  have hkernel :
      Complex.exp (((-2 * Real.pi * x * xi : Real) : Complex) *
          Complex.I) =
        1 := by
    rw [harg]
    simp
  have hkernel' :
      Complex.exp (-(2 * (Real.pi : Complex) * (x : Complex) *
          (xi : Complex) * Complex.I)) =
        1 := by
    have harg' :
        -(2 * (Real.pi : Complex) * (x : Complex) *
            (xi : Complex) * Complex.I) =
          (((-2 * Real.pi * x * xi : Real) : Complex) *
            Complex.I) := by
      norm_num [Complex.ofReal_mul]
    rw [harg', hkernel]
  simp [hkernel']

/-- The real angular frequency is nonzero in the nonzero case. -/
theorem branchAngularFrequency_ne_zero
    (xi : Real)
    (hxi : 2 * Real.pi * xi = 0 -> False) :
    TS168.Goldbach.branchAngularFrequency xi = 0 -> False := by
  unfold TS168.Goldbach.branchAngularFrequency
  exact Complex.ofReal_ne_zero.mpr hxi

/-- The primitive parameter `-i*omega` is nonzero when `omega` is nonzero. -/
theorem rightBranchA_ne_zero
    (xi : Real)
    (hxi : 2 * Real.pi * xi = 0 -> False) :
    rightBranchA xi = 0 -> False := by
  intro ha
  apply hxi
  unfold rightBranchA TS168.Goldbach.branchAngularFrequency at ha
  have hmul :
      Complex.I * ((2 * Real.pi * xi : Real) : Complex) = 0 := by
    exact neg_eq_zero.mp ha
  cases mul_eq_zero.mp hmul with
  | inl hI =>
      exact False.elim (Complex.I_ne_zero hI)
  | inr hfreq =>
      exact Complex.ofReal_eq_zero.mp hfreq

/-- The TS168 right-branch integral is the abstract primitive integral. -/
theorem rightBranchFourierIntegral_eq_primitiveIntegral
    (xi : Real) :
    TS168.Goldbach.rightBranchFourierIntegral xi =
      intervalIntegral
        (fun x : Real =>
          Complex.exp (rightBranchA xi * (x : Complex)) *
            ((1 - x : Real) : Complex))
        (0 : Real)
        1
        (volume : Measure Real) := by
  unfold TS168.Goldbach.rightBranchFourierIntegral
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold TS168.Goldbach.rightBranchFourierIntegrand
    TS168.Goldbach.mathlibForwardFourierKernel
    TS168.Goldbach.rightTriangleSplineBranchAsComplex
    rightBranchA
    TS168.Goldbach.branchAngularFrequency
  have harg :
      (((-2 * Real.pi * x * xi : Real) : Complex) * Complex.I) =
        -(Complex.I * ((2 * Real.pi * xi : Real) : Complex)) *
          (x : Complex) := by
    norm_num [Complex.ofReal_mul]
    ring
  rw [harg]

/-- The abstract primitive value matches the TS168 right closed form. -/
theorem rightBranchPrimitive_value_eq_closedForm
    (omega : Complex)
    (homega : omega = 0 -> False) :
    let a : Complex := -(Complex.I * omega)
    Complex.exp a * (1 / (a ^ 2)) - (1 / a + 1 / (a ^ 2)) =
      -(Complex.I / omega) +
        (1 - Complex.exp (-(Complex.I * omega))) / omega ^ 2 := by
  intro a
  have ha : a = 0 -> False := by
    intro hz
    apply homega
    dsimp [a] at hz
    have hmul : Complex.I * omega = 0 := by
      exact neg_eq_zero.mp hz
    cases mul_eq_zero.mp hmul with
    | inl hI =>
        exact False.elim (Complex.I_ne_zero hI)
    | inr hw =>
        exact hw
  dsimp [a]
  field_simp [homega, ha, Complex.I_ne_zero]
  ring_nf
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    norm_num [pow_succ, Complex.I_sq]
  have hI5 : Complex.I ^ 5 = Complex.I := by
    norm_num [show (5 : Nat) = 4 + 1 by norm_num, pow_succ,
      Complex.I_pow_four]
  have hI6 : Complex.I ^ 6 = -1 := by
    rw [show (6 : Nat) = 4 + 2 by norm_num, pow_add,
      Complex.I_pow_four, Complex.I_sq]
    norm_num
  rw [hI3, Complex.I_pow_four, hI5, hI6]
  ring_nf

/-- Discharge of the TS168 right branch integral evaluation. -/
theorem rightBranchIntegralEvaluation :
    TS168.Goldbach.RightBranchIntegralEvaluationStatement := by
  intro xi
  by_cases hxi : 2 * Real.pi * xi = 0
  case pos =>
    calc
      TS168.Goldbach.rightBranchFourierIntegral xi =
          intervalIntegral
            (fun x : Real => ((1 - x : Real) : Complex))
            (0 : Real)
            1
            (volume : Measure Real) := by
            exact rightBranchFourierIntegral_zero xi hxi
      _ = (1 / 2 : Complex) := rightBranchAffineIntegral_zero
      _ = TS168.Goldbach.rightBranchClosedForm xi := by
            unfold TS168.Goldbach.rightBranchClosedForm
            rw [if_pos hxi]
  case neg =>
    have homega :
        TS168.Goldbach.branchAngularFrequency xi = 0 -> False :=
      branchAngularFrequency_ne_zero xi hxi
    have ha : rightBranchA xi = 0 -> False :=
      rightBranchA_ne_zero xi hxi
    calc
      TS168.Goldbach.rightBranchFourierIntegral xi =
          intervalIntegral
            (fun x : Real =>
              Complex.exp (rightBranchA xi * (x : Complex)) *
                ((1 - x : Real) : Complex))
            (0 : Real)
            1
            (volume : Measure Real) := by
            exact rightBranchFourierIntegral_eq_primitiveIntegral xi
      _ =
          Complex.exp (rightBranchA xi) *
              (1 / ((rightBranchA xi) ^ 2)) -
            (1 / rightBranchA xi + 1 / ((rightBranchA xi) ^ 2)) := by
            exact rightBranchPrimitive_intervalIntegral (rightBranchA xi) ha
      _ =
          -(Complex.I / TS168.Goldbach.branchAngularFrequency xi) +
            (1 -
              Complex.exp
                (-(Complex.I *
                  TS168.Goldbach.branchAngularFrequency xi))) /
              (TS168.Goldbach.branchAngularFrequency xi) ^ 2 := by
            simpa [rightBranchA] using
              rightBranchPrimitive_value_eq_closedForm
                (TS168.Goldbach.branchAngularFrequency xi)
                homega
      _ = TS168.Goldbach.rightBranchClosedForm xi := by
            unfold TS168.Goldbach.rightBranchClosedForm
            rw [if_neg hxi]

/-- Ledger for the TS170 right-branch integral evaluation discharge. -/
structure TriangleSplineRightBranchIntegralEvaluationLedger where
  ts168_probe :
    TS168.Goldbach.TriangleSplineBranchIntegralRouteProbeLedger

  right_branch_evaluation :
    TS168.Goldbach.RightBranchIntegralEvaluationStatement

  branch_split_not_claimed :
    True

  left_integral_evaluation_not_claimed :
    True

  ts166_identification_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS170 right-branch evaluation ledger. -/
noncomputable def triangleSplineRightBranchIntegralEvaluationLedger :
    TriangleSplineRightBranchIntegralEvaluationLedger where
  ts168_probe := TS168.Goldbach.triangleSplineBranchIntegralRouteProbeLedger
  right_branch_evaluation := rightBranchIntegralEvaluation
  branch_split_not_claimed := True.intro
  left_integral_evaluation_not_claimed := True.intro
  ts166_identification_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS170. -/
def TriangleSplineRightBranchIntegralEvaluationTarget : Prop :=
  Nonempty TriangleSplineRightBranchIntegralEvaluationLedger

/-- The TS170 right-branch evaluation target is populated. -/
theorem triangleSplineRightBranchIntegralEvaluationTarget :
    TriangleSplineRightBranchIntegralEvaluationTarget :=
  Nonempty.intro triangleSplineRightBranchIntegralEvaluationLedger

end Goldbach
end TS170
