import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS166.TriangleSplineFourierIdentificationReduction

namespace TS168
namespace Goldbach

open MeasureTheory

/-!
# TS168 - Triangle Spline Branch Integral Route Probe

TS166 fixed the exact Fourier-identification target for the triangle spline,
and TS167 probed the primary convolution route.  This sprint records the
fallback route: split the Fourier integral over the two affine branches
`[-1, 0]` and `[0, 1]`, evaluate those directed interval integrals, and
recombine the closed forms into the TS166 squared-sinc target.

The sprint compiles the branch functions, branch integrals, closed-form
targets, and the logical implication from those local obligations to the
TS166 Fourier-identification statement.

No branch split theorem, branch integral evaluation, closed-form
recombination, Plancherel theorem, or explicit formula is claimed here.
-/

/-- Current status of the branch-integral fallback route. -/
inductive BranchIntegralRouteStatus where
  /-- The route has been stated and type-checked, but its analytic facts remain open. -/
  | apiProbe
  /-- Future status: the directed interval-integral route is usable. -/
  | branchIntegrationAvailable
  /-- Future status: the route should be replaced by a different analytic proof. -/
  | fallbackRequired
  deriving DecidableEq, Repr

/-- Left affine branch of the triangle spline, complex-valued. -/
noncomputable def leftTriangleSplineBranchAsComplex
    (x : Real) :
    Complex :=
  ((1 + x : Real) : Complex)

/-- Right affine branch of the triangle spline, complex-valued. -/
noncomputable def rightTriangleSplineBranchAsComplex
    (x : Real) :
    Complex :=
  ((1 - x : Real) : Complex)

/--
The Mathlib forward Fourier kernel on the real line, written explicitly using
the TS165 convention `exp(-2*pi*i*x*xi)`.
-/
noncomputable def mathlibForwardFourierKernel
    (xi x : Real) :
    Complex :=
  Complex.exp (((-2 * Real.pi * x * xi : Real) : Complex) * Complex.I)

/-- Left branch Fourier integrand on `[-1, 0]`. -/
noncomputable def leftBranchFourierIntegrand
    (xi x : Real) :
    Complex :=
  mathlibForwardFourierKernel xi x *
    leftTriangleSplineBranchAsComplex x

/-- Right branch Fourier integrand on `[0, 1]`. -/
noncomputable def rightBranchFourierIntegrand
    (xi x : Real) :
    Complex :=
  mathlibForwardFourierKernel xi x *
    rightTriangleSplineBranchAsComplex x

/-- Directed interval integral over the left affine branch `[-1, 0]`. -/
noncomputable def leftBranchFourierIntegral
    (xi : Real) :
    Complex :=
  intervalIntegral
    (leftBranchFourierIntegrand xi)
    (-1 : Real)
    0
    (volume : Measure Real)

/-- Directed interval integral over the right affine branch `[0, 1]`. -/
noncomputable def rightBranchFourierIntegral
    (xi : Real) :
    Complex :=
  intervalIntegral
    (rightBranchFourierIntegrand xi)
    (0 : Real)
    1
    (volume : Measure Real)

/-- The real angular frequency `2*pi*xi`, lifted to `Complex`. -/
noncomputable def branchAngularFrequency
    (xi : Real) :
    Complex :=
  ((2 * Real.pi * xi : Real) : Complex)

/--
Closed-form target for the left branch integral.

At zero frequency the left branch contributes `1/2`.  Away from zero it is the
direct elementary antiderivative target for
`integral_{-1}^{0} (1+x) * exp(-2*pi*i*x*xi) dx`.
-/
noncomputable def leftBranchClosedForm
    (xi : Real) :
    Complex :=
  if 2 * Real.pi * xi = 0 then
    (1 / 2 : Complex)
  else
    Complex.I / branchAngularFrequency xi +
      (1 - Complex.exp (Complex.I * branchAngularFrequency xi)) /
        (branchAngularFrequency xi) ^ 2

/--
Closed-form target for the right branch integral.

At zero frequency the right branch contributes `1/2`.  Away from zero it is
the direct elementary antiderivative target for
`integral_{0}^{1} (1-x) * exp(-2*pi*i*x*xi) dx`.
-/
noncomputable def rightBranchClosedForm
    (xi : Real) :
    Complex :=
  if 2 * Real.pi * xi = 0 then
    (1 / 2 : Complex)
  else
    -(Complex.I / branchAngularFrequency xi) +
      (1 - Complex.exp (-(Complex.I * branchAngularFrequency xi))) /
        (branchAngularFrequency xi) ^ 2

/--
Branch split statement for the fallback route.

TS168 only states that Mathlib's Fourier integral of the triangle spline is
the sum of the two directed branch integrals.
-/
def BranchSplitFourierStatement : Prop :=
  forall xi : Real,
    TS166.Goldbach.triangleSplineMathlibFourier xi =
      leftBranchFourierIntegral xi +
        rightBranchFourierIntegral xi

/-- Evaluation statement for the left branch integral. -/
def LeftBranchIntegralEvaluationStatement : Prop :=
  forall xi : Real,
    leftBranchFourierIntegral xi =
      leftBranchClosedForm xi

/-- Evaluation statement for the right branch integral. -/
def RightBranchIntegralEvaluationStatement : Prop :=
  forall xi : Real,
    rightBranchFourierIntegral xi =
      rightBranchClosedForm xi

/--
Closed-form recombination statement.

This keeps the algebraic simplification from branch closed forms to the TS166
squared-sinc target as its own future obligation.
-/
def BranchClosedFormRecombinationStatement : Prop :=
  forall xi : Real,
    leftBranchClosedForm xi +
      rightBranchClosedForm xi =
        TS166.Goldbach.triangleSplineScaledSincCandidate xi

/-- The branch-integral route, if discharged, implies the TS166 Fourier target. -/
def BranchIntegralRouteImpliesTS166Statement : Prop :=
  BranchSplitFourierStatement ->
    LeftBranchIntegralEvaluationStatement ->
      RightBranchIntegralEvaluationStatement ->
        BranchClosedFormRecombinationStatement ->
          TS166.Goldbach.TriangleSplineFourierIdentificationStatement

/--
The compiled branch obligations are sufficient for the TS166 target.

This theorem proves only the logical wiring of the route.  It does not prove
the analytic branch split, either branch evaluation, or the final closed-form
recombination.
-/
theorem branchIntegralRoute_implies_ts166 :
    BranchIntegralRouteImpliesTS166Statement := by
  intro h_split h_left h_right h_recombine xi
  calc
    TS166.Goldbach.triangleSplineMathlibFourier xi =
        leftBranchFourierIntegral xi +
          rightBranchFourierIntegral xi := by
          exact h_split xi
    _ =
        leftBranchClosedForm xi +
          rightBranchClosedForm xi := by
          rw [h_left xi, h_right xi]
    _ =
        TS166.Goldbach.triangleSplineScaledSincCandidate xi := by
          exact h_recombine xi

/-- Ledger for the TS168 branch-integral fallback route probe. -/
structure TriangleSplineBranchIntegralRouteProbeLedger where
  status :
    BranchIntegralRouteStatus

  status_eq :
    status = BranchIntegralRouteStatus.apiProbe

  left_branch_defined :
    True

  right_branch_defined :
    True

  forward_kernel_defined :
    True

  left_integral_defined :
    True

  right_integral_defined :
    True

  left_closed_form_defined :
    True

  right_closed_form_defined :
    True

  branch_split_statement :
    Prop

  branch_split_statement_eq :
    branch_split_statement =
      BranchSplitFourierStatement

  left_evaluation_statement :
    Prop

  left_evaluation_statement_eq :
    left_evaluation_statement =
      LeftBranchIntegralEvaluationStatement

  right_evaluation_statement :
    Prop

  right_evaluation_statement_eq :
    right_evaluation_statement =
      RightBranchIntegralEvaluationStatement

  recombination_statement :
    Prop

  recombination_statement_eq :
    recombination_statement =
      BranchClosedFormRecombinationStatement

  route_implication_statement :
    Prop

  route_implication_statement_eq :
    route_implication_statement =
      BranchIntegralRouteImpliesTS166Statement

  route_implication_proof :
    BranchIntegralRouteImpliesTS166Statement

  branch_split_not_claimed :
    True

  left_integral_evaluation_not_claimed :
    True

  right_integral_evaluation_not_claimed :
    True

  closed_form_recombination_not_claimed :
    True

  ts166_identification_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS168 branch-integral route probe ledger. -/
noncomputable def triangleSplineBranchIntegralRouteProbeLedger :
    TriangleSplineBranchIntegralRouteProbeLedger where
  status := BranchIntegralRouteStatus.apiProbe
  status_eq := rfl
  left_branch_defined := True.intro
  right_branch_defined := True.intro
  forward_kernel_defined := True.intro
  left_integral_defined := True.intro
  right_integral_defined := True.intro
  left_closed_form_defined := True.intro
  right_closed_form_defined := True.intro
  branch_split_statement := BranchSplitFourierStatement
  branch_split_statement_eq := rfl
  left_evaluation_statement := LeftBranchIntegralEvaluationStatement
  left_evaluation_statement_eq := rfl
  right_evaluation_statement := RightBranchIntegralEvaluationStatement
  right_evaluation_statement_eq := rfl
  recombination_statement := BranchClosedFormRecombinationStatement
  recombination_statement_eq := rfl
  route_implication_statement := BranchIntegralRouteImpliesTS166Statement
  route_implication_statement_eq := rfl
  route_implication_proof := branchIntegralRoute_implies_ts166
  branch_split_not_claimed := True.intro
  left_integral_evaluation_not_claimed := True.intro
  right_integral_evaluation_not_claimed := True.intro
  closed_form_recombination_not_claimed := True.intro
  ts166_identification_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS168. -/
def TriangleSplineBranchIntegralRouteProbeTarget : Prop :=
  Nonempty TriangleSplineBranchIntegralRouteProbeLedger

/-- The TS168 branch-integral route probe target is populated. -/
theorem triangleSplineBranchIntegralRouteProbeTarget :
    TriangleSplineBranchIntegralRouteProbeTarget :=
  Nonempty.intro triangleSplineBranchIntegralRouteProbeLedger

end Goldbach
end TS168
