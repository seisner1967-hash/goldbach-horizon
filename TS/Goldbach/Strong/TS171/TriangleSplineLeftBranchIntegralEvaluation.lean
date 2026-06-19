import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import TS.Goldbach.Strong.TS170.TriangleSplineRightBranchIntegralEvaluation

namespace TS171
namespace Goldbach

open MeasureTheory

/-!
# TS171 - Triangle Spline Left Branch Integral Evaluation

TS170 discharged the right branch integral evaluation.  This sprint discharges
the symmetric left branch over `[-1,0]`.

The proof is intentionally local.  It proves only
`LeftBranchIntegralEvaluationStatement`, splitting zero frequency from nonzero
frequency and using an explicit elementary primitive for the nonzero case.  It
does not prove the global branch split, the full TS166 Fourier identification,
Plancherel, or the explicit formula.
-/

/-- Nonzero-frequency primitive parameter for the left branch. -/
noncomputable def leftBranchA
    (xi : Real) :
    Complex :=
  -(Complex.I * TS168.Goldbach.branchAngularFrequency xi)

/-- The primitive used for the nonzero left branch integral. -/
noncomputable def leftBranchPrimitive
    (a : Complex)
    (x : Real) :
    Complex :=
  Complex.exp (a * (x : Complex)) *
    (((1 + x : Real) : Complex) / a - 1 / (a ^ 2))

/-- The complex affine left branch has derivative `1`. -/
theorem leftBranchAffine_hasDerivAt
    (x : Real) :
    HasDerivAt
      (fun y : Real => ((1 + y : Real) : Complex))
      (1 : Complex)
      x := by
  simpa [Complex.ofReal_add] using
    ((hasDerivAt_const (x := x) (c := (1 : Complex))).add
      (Complex.ofRealCLM.hasDerivAt (x := x)))

/-- Derivative of the explicit nonzero-frequency primitive. -/
theorem leftBranchPrimitive_hasDerivAt
    (a : Complex)
    (ha : a = 0 -> False)
    (x : Real) :
    HasDerivAt
      (fun y : Real => leftBranchPrimitive a y)
      (Complex.exp (a * (x : Complex)) * ((1 + x : Real) : Complex))
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
          ((1 + y : Real) : Complex) / a - 1 / (a ^ 2))
        ((1 : Complex) / a)
        x := by
    convert
      (leftBranchAffine_hasDerivAt x).div_const a |>.sub
        (hasDerivAt_const x (1 / (a ^ 2))) using 1
    simp [one_div]
  have hprod := hexp.mul hfactor
  unfold leftBranchPrimitive
  convert hprod using 1
  field_simp [ha]
  ring_nf

/-- Elementary FTC evaluation of the abstract left-branch primitive. -/
theorem leftBranchPrimitive_intervalIntegral
    (a : Complex)
    (ha : a = 0 -> False) :
    intervalIntegral
      (fun x : Real =>
        Complex.exp (a * (x : Complex)) *
          ((1 + x : Real) : Complex))
      (-1 : Real)
      0
      (volume : Measure Real)
      =
    (1 / a - 1 / (a ^ 2)) +
      Complex.exp (-a) * (1 / (a ^ 2)) := by
  let F : Real -> Complex := fun x =>
    leftBranchPrimitive a x
  have hderiv :
      forall x : Real, (Set.uIcc (-1 : Real) 0) x ->
        HasDerivAt F
          (Complex.exp (a * (x : Complex)) *
            ((1 + x : Real) : Complex))
          x := by
    intro x _hx
    dsimp [F]
    exact leftBranchPrimitive_hasDerivAt a ha x
  have hint :
      IntervalIntegrable
        (fun x : Real =>
          Complex.exp (a * (x : Complex)) *
            ((1 + x : Real) : Complex))
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (-1 : Real))
      (b := 0)
      (f := F)
      (f' := fun x : Real =>
        Complex.exp (a * (x : Complex)) *
          ((1 + x : Real) : Complex))
      hderiv
      hint
  simpa [F, leftBranchPrimitive] using hftc

/-- Zero-frequency left branch integral. -/
theorem leftBranchAffineIntegral_zero :
    intervalIntegral
      (fun x : Real => ((1 + x : Real) : Complex))
      (-1 : Real)
      0
      (volume : Measure Real)
      =
    (1 / 2 : Complex) := by
  rw [intervalIntegral.integral_ofReal]
  have hconst :
      IntervalIntegrable
        (fun _x : Real => (1 : Real))
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  have hid :
      IntervalIntegrable
        (fun x : Real => x)
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  rw [intervalIntegral.integral_add hconst hid]
  norm_num [integral_one, integral_id]

/-- At zero frequency, the TS168 left-branch integrand reduces to `1+x`. -/
theorem leftBranchFourierIntegral_zero
    (xi : Real)
    (hxi : 2 * Real.pi * xi = 0) :
    TS168.Goldbach.leftBranchFourierIntegral xi =
      intervalIntegral
        (fun x : Real => ((1 + x : Real) : Complex))
        (-1 : Real)
        0
        (volume : Measure Real) := by
  unfold TS168.Goldbach.leftBranchFourierIntegral
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold TS168.Goldbach.leftBranchFourierIntegrand
    TS168.Goldbach.mathlibForwardFourierKernel
    TS168.Goldbach.leftTriangleSplineBranchAsComplex
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

/-- The primitive parameter `-i*omega` is nonzero when `omega` is nonzero. -/
theorem leftBranchA_ne_zero
    (xi : Real)
    (hxi : 2 * Real.pi * xi = 0 -> False) :
    leftBranchA xi = 0 -> False := by
  intro ha
  apply hxi
  unfold leftBranchA TS168.Goldbach.branchAngularFrequency at ha
  have hmul :
      Complex.I * ((2 * Real.pi * xi : Real) : Complex) = 0 := by
    exact neg_eq_zero.mp ha
  cases mul_eq_zero.mp hmul with
  | inl hI =>
      exact False.elim (Complex.I_ne_zero hI)
  | inr hfreq =>
      exact Complex.ofReal_eq_zero.mp hfreq

/-- The TS168 left-branch integral is the abstract primitive integral. -/
theorem leftBranchFourierIntegral_eq_primitiveIntegral
    (xi : Real) :
    TS168.Goldbach.leftBranchFourierIntegral xi =
      intervalIntegral
        (fun x : Real =>
          Complex.exp (leftBranchA xi * (x : Complex)) *
            ((1 + x : Real) : Complex))
        (-1 : Real)
        0
        (volume : Measure Real) := by
  unfold TS168.Goldbach.leftBranchFourierIntegral
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold TS168.Goldbach.leftBranchFourierIntegrand
    TS168.Goldbach.mathlibForwardFourierKernel
    TS168.Goldbach.leftTriangleSplineBranchAsComplex
    leftBranchA
    TS168.Goldbach.branchAngularFrequency
  have harg :
      (((-2 * Real.pi * x * xi : Real) : Complex) * Complex.I) =
        -(Complex.I * ((2 * Real.pi * xi : Real) : Complex)) *
          (x : Complex) := by
    norm_num [Complex.ofReal_mul]
    ring
  rw [harg]

/-- The abstract primitive value matches the TS168 left closed form. -/
theorem leftBranchPrimitive_value_eq_closedForm
    (omega : Complex)
    (homega : omega = 0 -> False) :
    let a : Complex := -(Complex.I * omega)
    (1 / a - 1 / (a ^ 2)) + Complex.exp (-a) * (1 / (a ^ 2)) =
      Complex.I / omega +
        (1 - Complex.exp (Complex.I * omega)) / omega ^ 2 := by
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

/-- Discharge of the TS168 left branch integral evaluation. -/
theorem leftBranchIntegralEvaluation :
    TS168.Goldbach.LeftBranchIntegralEvaluationStatement := by
  intro xi
  by_cases hxi : 2 * Real.pi * xi = 0
  case pos =>
    calc
      TS168.Goldbach.leftBranchFourierIntegral xi =
          intervalIntegral
            (fun x : Real => ((1 + x : Real) : Complex))
            (-1 : Real)
            0
            (volume : Measure Real) := by
            exact leftBranchFourierIntegral_zero xi hxi
      _ = (1 / 2 : Complex) := leftBranchAffineIntegral_zero
      _ = TS168.Goldbach.leftBranchClosedForm xi := by
            unfold TS168.Goldbach.leftBranchClosedForm
            rw [if_pos hxi]
  case neg =>
    have homega :
        TS168.Goldbach.branchAngularFrequency xi = 0 -> False :=
      TS170.Goldbach.branchAngularFrequency_ne_zero xi hxi
    have ha : leftBranchA xi = 0 -> False :=
      leftBranchA_ne_zero xi hxi
    calc
      TS168.Goldbach.leftBranchFourierIntegral xi =
          intervalIntegral
            (fun x : Real =>
              Complex.exp (leftBranchA xi * (x : Complex)) *
                ((1 + x : Real) : Complex))
            (-1 : Real)
            0
            (volume : Measure Real) := by
            exact leftBranchFourierIntegral_eq_primitiveIntegral xi
      _ =
          (1 / leftBranchA xi - 1 / ((leftBranchA xi) ^ 2)) +
            Complex.exp (-(leftBranchA xi)) *
              (1 / ((leftBranchA xi) ^ 2)) := by
            exact leftBranchPrimitive_intervalIntegral (leftBranchA xi) ha
      _ =
          Complex.I / TS168.Goldbach.branchAngularFrequency xi +
            (1 -
              Complex.exp
                (Complex.I *
                  TS168.Goldbach.branchAngularFrequency xi)) /
              (TS168.Goldbach.branchAngularFrequency xi) ^ 2 := by
            simpa [leftBranchA] using
              leftBranchPrimitive_value_eq_closedForm
                (TS168.Goldbach.branchAngularFrequency xi)
                homega
      _ = TS168.Goldbach.leftBranchClosedForm xi := by
            unfold TS168.Goldbach.leftBranchClosedForm
            rw [if_neg hxi]

/-- Ledger for the TS171 left-branch integral evaluation discharge. -/
structure TriangleSplineLeftBranchIntegralEvaluationLedger where
  ts170_discharge :
    TS170.Goldbach.TriangleSplineRightBranchIntegralEvaluationLedger

  left_branch_evaluation :
    TS168.Goldbach.LeftBranchIntegralEvaluationStatement

  branch_split_not_claimed :
    True

  ts166_identification_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS171 left-branch evaluation ledger. -/
noncomputable def triangleSplineLeftBranchIntegralEvaluationLedger :
    TriangleSplineLeftBranchIntegralEvaluationLedger where
  ts170_discharge :=
    TS170.Goldbach.triangleSplineRightBranchIntegralEvaluationLedger
  left_branch_evaluation := leftBranchIntegralEvaluation
  branch_split_not_claimed := True.intro
  ts166_identification_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS171. -/
def TriangleSplineLeftBranchIntegralEvaluationTarget : Prop :=
  Nonempty TriangleSplineLeftBranchIntegralEvaluationLedger

/-- The TS171 left-branch evaluation target is populated. -/
theorem triangleSplineLeftBranchIntegralEvaluationTarget :
    TriangleSplineLeftBranchIntegralEvaluationTarget :=
  Nonempty.intro triangleSplineLeftBranchIntegralEvaluationLedger

end Goldbach
end TS171
