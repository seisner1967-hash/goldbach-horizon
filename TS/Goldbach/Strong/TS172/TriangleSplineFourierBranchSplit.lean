import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS171.TriangleSplineLeftBranchIntegralEvaluation
import TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
import TS.Goldbach.Strong.TS162.TriangleSplineTraceKernelInstantiation

namespace TS172
namespace Goldbach

open MeasureTheory

/-!
# TS172 - Triangle Spline Fourier Branch Split

TS169, TS170, and TS171 discharged the algebraic recombination and both branch
integral evaluations in the TS168 fallback route.  This sprint discharges the
remaining topological obligation: Mathlib's global Fourier integral of the
triangle spline splits into the two directed affine branch integrals over
`[-1,0]` and `[0,1]`.

The proof converts `Real.fourierIntegral` to Mathlib's explicit global
Bochner integral, restricts it to the support `(-1,1]`, uses interval
additivity at `0`, and then identifies the two interval integrals with the
left and right TS168 branch integrals.  It does not claim Plancherel or the
Riemann-von Mangoldt explicit formula.
-/

/-- The global Fourier integrand for the triangle spline using the TS168 kernel. -/
noncomputable def globalBranchIntegrand
    (xi x : Real) :
    Complex :=
  TS168.Goldbach.mathlibForwardFourierKernel xi x *
    TS166.Goldbach.triangleSplineAsComplex x

/-- Mathlib's Fourier integral is the global integral of the explicit TS168 kernel. -/
theorem triangleSplineMathlibFourier_eq_globalIntegral
    (xi : Real) :
    TS166.Goldbach.triangleSplineMathlibFourier xi =
      MeasureTheory.integral (volume : Measure Real)
        (fun x : Real => globalBranchIntegrand xi x) := by
  unfold TS166.Goldbach.triangleSplineMathlibFourier
    globalBranchIntegrand
    TS166.Goldbach.triangleSplineAsComplex
    TS168.Goldbach.mathlibForwardFourierKernel
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  simp [Circle.smul_def, Real.fourierChar_apply, Complex.ofReal_mul]

/-- The explicit global integrand vanishes outside the spline support `(-1,1]`. -/
theorem globalBranchIntegrand_eq_zero_of_not_mem_Ioc
    (xi x : Real)
    (hx : Not ((Set.Ioc (-1 : Real) 1) x)) :
    globalBranchIntegrand xi x = 0 := by
  have h_abs : 1 <= |x| := by
    by_cases hxleft : x <= -1
    case pos =>
      have hneg : 1 <= -x := by
        linarith
      exact hneg.trans (neg_le_abs x)
    case neg =>
      have hgt_left : -1 < x := lt_of_not_ge hxleft
      have hgt_right : 1 < x := by
        by_contra hnot
        have hxright : x <= 1 := le_of_not_gt hnot
        exact hx (And.intro hgt_left hxright)
      exact (le_of_lt hgt_right).trans (le_abs_self x)
  unfold globalBranchIntegrand TS166.Goldbach.triangleSplineAsComplex
  rw [TS162.Goldbach.triangleSpline_eq_zero_of_one_le_abs h_abs]
  simp

/-- The global integral is the directed interval integral over `[-1,1]`. -/
theorem globalIntegral_eq_intervalIntegral
    (xi : Real) :
    MeasureTheory.integral (volume : Measure Real)
        (fun x : Real => globalBranchIntegrand xi x) =
      intervalIntegral
        (globalBranchIntegrand xi)
        (-1 : Real)
        1
        (volume : Measure Real) := by
  have hrestrict :
      MeasureTheory.integral
          ((volume : Measure Real).restrict (Set.Ioc (-1 : Real) 1))
          (fun x : Real => globalBranchIntegrand xi x) =
        MeasureTheory.integral (volume : Measure Real)
          (fun x : Real => globalBranchIntegrand xi x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Ioc (-1 : Real) 1)
      (f := globalBranchIntegrand xi)
      (by
        intro x hx
        exact globalBranchIntegrand_eq_zero_of_not_mem_Ioc xi x hx)
  calc
    MeasureTheory.integral (volume : Measure Real)
        (fun x : Real => globalBranchIntegrand xi x) =
        MeasureTheory.integral
          ((volume : Measure Real).restrict (Set.Ioc (-1 : Real) 1))
          (fun x : Real => globalBranchIntegrand xi x) := hrestrict.symm
    _ =
        intervalIntegral
          (globalBranchIntegrand xi)
          (-1 : Real)
          1
          (volume : Measure Real) := by
          rw [<- intervalIntegral.integral_of_le (by norm_num : (-1 : Real) <= 1)]

/-- The left affine branch integrand is continuous. -/
theorem leftBranchFourierIntegrand_continuous
    (xi : Real) :
    Continuous (TS168.Goldbach.leftBranchFourierIntegrand xi) := by
  unfold TS168.Goldbach.leftBranchFourierIntegrand
    TS168.Goldbach.mathlibForwardFourierKernel
    TS168.Goldbach.leftTriangleSplineBranchAsComplex
  continuity

/-- The right affine branch integrand is continuous. -/
theorem rightBranchFourierIntegrand_continuous
    (xi : Real) :
    Continuous (TS168.Goldbach.rightBranchFourierIntegrand xi) := by
  unfold TS168.Goldbach.rightBranchFourierIntegrand
    TS168.Goldbach.mathlibForwardFourierKernel
    TS168.Goldbach.rightTriangleSplineBranchAsComplex
  continuity

/-- The global integrand is interval-integrable on the left branch. -/
theorem globalBranchIntegrand_intervalIntegrable_left
    (xi : Real) :
    IntervalIntegrable
      (globalBranchIntegrand xi)
      volume
      (-1 : Real)
      0 := by
  have hleft :
      IntervalIntegrable
        (TS168.Goldbach.leftBranchFourierIntegrand xi)
        volume
        (-1 : Real)
        0 :=
    (leftBranchFourierIntegrand_continuous xi).intervalIntegrable (-1) 0
  refine hleft.congr ?_
  exact (ae_restrict_iff' measurableSet_uIoc).mpr (by
    filter_upwards with x hx
    unfold TS168.Goldbach.leftBranchFourierIntegrand
      TS168.Goldbach.leftTriangleSplineBranchAsComplex
      globalBranchIntegrand
      TS166.Goldbach.triangleSplineAsComplex
    have hxmem : (Set.Ioc (-1 : Real) 0) x := by
      simpa using hx
    have hx_left : -1 <= x := by
      exact le_of_lt hxmem.1
    have hx_right : x <= 0 := by
      exact hxmem.2
    rw [TS56.MellinJackson.triangleSpline_eq_one_add_of_left hx_left hx_right])

/-- The global integrand is interval-integrable on the right branch. -/
theorem globalBranchIntegrand_intervalIntegrable_right
    (xi : Real) :
    IntervalIntegrable
      (globalBranchIntegrand xi)
      volume
      (0 : Real)
      1 := by
  have hright :
      IntervalIntegrable
        (TS168.Goldbach.rightBranchFourierIntegrand xi)
        volume
        (0 : Real)
        1 :=
    (rightBranchFourierIntegrand_continuous xi).intervalIntegrable 0 1
  refine hright.congr ?_
  exact (ae_restrict_iff' measurableSet_uIoc).mpr (by
    filter_upwards with x hx
    unfold TS168.Goldbach.rightBranchFourierIntegrand
      TS168.Goldbach.rightTriangleSplineBranchAsComplex
      globalBranchIntegrand
      TS166.Goldbach.triangleSplineAsComplex
    have hxmem : (Set.Ioc (0 : Real) 1) x := by
      simpa using hx
    have hx_left : 0 <= x := by
      exact le_of_lt hxmem.1
    have hx_right : x <= 1 := by
      exact hxmem.2
    rw [TS56.MellinJackson.triangleSpline_eq_one_sub_of_right hx_left hx_right])

/-- On the left interval, the global integrand is the TS168 left branch integrand. -/
theorem globalIntervalIntegral_left_eq_leftBranch
    (xi : Real) :
    intervalIntegral
      (globalBranchIntegrand xi)
      (-1 : Real)
      0
      (volume : Measure Real)
      =
    TS168.Goldbach.leftBranchFourierIntegral xi := by
  unfold TS168.Goldbach.leftBranchFourierIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  unfold globalBranchIntegrand
    TS166.Goldbach.triangleSplineAsComplex
    TS168.Goldbach.leftBranchFourierIntegrand
    TS168.Goldbach.leftTriangleSplineBranchAsComplex
  have hxmem : (Set.Icc (-1 : Real) 0) x := by
    simpa using hx
  rw [TS56.MellinJackson.triangleSpline_eq_one_add_of_left hxmem.1 hxmem.2]

/-- On the right interval, the global integrand is the TS168 right branch integrand. -/
theorem globalIntervalIntegral_right_eq_rightBranch
    (xi : Real) :
    intervalIntegral
      (globalBranchIntegrand xi)
      (0 : Real)
      1
      (volume : Measure Real)
      =
    TS168.Goldbach.rightBranchFourierIntegral xi := by
  unfold TS168.Goldbach.rightBranchFourierIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  unfold globalBranchIntegrand
    TS166.Goldbach.triangleSplineAsComplex
    TS168.Goldbach.rightBranchFourierIntegrand
    TS168.Goldbach.rightTriangleSplineBranchAsComplex
  have hxmem : (Set.Icc (0 : Real) 1) x := by
    simpa using hx
  rw [TS56.MellinJackson.triangleSpline_eq_one_sub_of_right hxmem.1 hxmem.2]

/-- Discharge of the TS168 branch split for the Fourier integral. -/
theorem branchSplitFourier :
    TS168.Goldbach.BranchSplitFourierStatement := by
  intro xi
  calc
    TS166.Goldbach.triangleSplineMathlibFourier xi =
        MeasureTheory.integral (volume : Measure Real)
          (fun x : Real => globalBranchIntegrand xi x) := by
        exact triangleSplineMathlibFourier_eq_globalIntegral xi
    _ =
        intervalIntegral
          (globalBranchIntegrand xi)
          (-1 : Real)
          1
          (volume : Measure Real) := by
          exact globalIntegral_eq_intervalIntegral xi
    _ =
        intervalIntegral
          (globalBranchIntegrand xi)
          (-1 : Real)
          0
          (volume : Measure Real) +
        intervalIntegral
          (globalBranchIntegrand xi)
          (0 : Real)
          1
          (volume : Measure Real) := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              (globalBranchIntegrand_intervalIntegrable_left xi)
              (globalBranchIntegrand_intervalIntegrable_right xi)).symm
    _ =
        TS168.Goldbach.leftBranchFourierIntegral xi +
          TS168.Goldbach.rightBranchFourierIntegral xi := by
          rw [globalIntervalIntegral_left_eq_leftBranch,
            globalIntervalIntegral_right_eq_rightBranch]

/-- Ledger for the TS172 branch-split discharge. -/
structure TriangleSplineFourierBranchSplitLedger where
  ts171_discharge :
    TS171.Goldbach.TriangleSplineLeftBranchIntegralEvaluationLedger

  branch_split :
    TS168.Goldbach.BranchSplitFourierStatement

  ts166_identification_not_claimed :
    True

  plancherel_not_claimed :
    True

  explicit_formula_not_claimed :
    True

/-- Concrete TS172 branch-split ledger. -/
noncomputable def triangleSplineFourierBranchSplitLedger :
    TriangleSplineFourierBranchSplitLedger where
  ts171_discharge :=
    TS171.Goldbach.triangleSplineLeftBranchIntegralEvaluationLedger
  branch_split := branchSplitFourier
  ts166_identification_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro

/-- Target proposition for TS172. -/
def TriangleSplineFourierBranchSplitTarget : Prop :=
  Nonempty TriangleSplineFourierBranchSplitLedger

/-- The TS172 branch-split target is populated. -/
theorem triangleSplineFourierBranchSplitTarget :
    TriangleSplineFourierBranchSplitTarget :=
  Nonempty.intro triangleSplineFourierBranchSplitLedger

end Goldbach
end TS172
