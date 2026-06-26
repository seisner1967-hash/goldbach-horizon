import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.SetIntegral
import TS.Goldbach.Strong.TS167.TriangleSplineConvolutionRouteProbe
import TS.Goldbach.Strong.TS209.TriangleSplineSincFourthScaleReduction

namespace TS210
namespace Goldbach

open MeasureTheory
open Set

/-!
# TS210 - Box Convolution Triangle Evidence

TS167 named the primary convolution route toward the triangle-spline Fourier
identification:

1. the centered unit box convolved with itself is the triangle spline;
2. the Fourier transform of the box is the non-squared sinc;
3. Fourier exchanges convolution with multiplication.

TS210 proves the first item. It evaluates the manual Bochner convolution from
TS167 pointwise by computing the length of the overlap of the two unit boxes.

No Fourier transform evaluation, Fourier-convolution exchange, Plancherel
theorem, explicit formula, Gallagher comparison, or Goldbach theorem is
claimed.
-/

/-- The box product integrand vanishes on the far-left exterior branch. -/
theorem unitBoxConvolutionIntegrand_eq_zero_of_lt_neg_one
    {x y : Real}
    (hx : x < -1) :
    TS167.Goldbach.unitBoxAsComplex y *
      TS167.Goldbach.unitBoxAsComplex (x - y) =
        0 := by
  unfold TS167.Goldbach.unitBoxAsComplex TS167.Goldbach.unitBoxFunction
  by_cases hy : -(1 / 2 : Real) <= y /\ y <= (1 / 2 : Real)
  case pos =>
    have hxy_not :
        Not (-(1 / 2 : Real) <= x - y /\ x - y <= (1 / 2 : Real)) := by
      intro hxy
      have hsum : -1 <= x := by
        linarith [hy.1, hxy.1]
      linarith
    simp only [hy, hxy_not, if_true, if_false, Complex.ofReal_one,
      Complex.ofReal_zero, one_mul, mul_zero]
  case neg =>
    simp only [hy, if_false, Complex.ofReal_zero, zero_mul]

/-- The box product integrand vanishes on the far-right exterior branch. -/
theorem unitBoxConvolutionIntegrand_eq_zero_of_gt_one
    {x y : Real}
    (hx : 1 < x) :
    TS167.Goldbach.unitBoxAsComplex y *
      TS167.Goldbach.unitBoxAsComplex (x - y) =
        0 := by
  unfold TS167.Goldbach.unitBoxAsComplex TS167.Goldbach.unitBoxFunction
  by_cases hy : -(1 / 2 : Real) <= y /\ y <= (1 / 2 : Real)
  case pos =>
    have hxy_not :
        Not (-(1 / 2 : Real) <= x - y /\ x - y <= (1 / 2 : Real)) := by
      intro hxy
      have hsum : x <= 1 := by
        linarith [hy.2, hxy.2]
      linarith
    simp only [hy, hxy_not, if_true, if_false, Complex.ofReal_one,
      Complex.ofReal_zero, one_mul, mul_zero]
  case neg =>
    simp only [hy, if_false, Complex.ofReal_zero, zero_mul]

/--
On the left branch `-1 <= x <= 0`, the overlap of the two unit boxes is
`[-1/2, x + 1/2]`.
-/
theorem unitBoxConvolutionIntegrand_left
    {x y : Real}
    (_hx_left : -1 <= x)
    (hx_right : x <= 0) :
    TS167.Goldbach.unitBoxAsComplex y *
      TS167.Goldbach.unitBoxAsComplex (x - y) =
        (Icc (-(1 / 2 : Real)) (x + 1 / 2)).indicator
          (fun _ : Real => (1 : Complex)) y := by
  unfold TS167.Goldbach.unitBoxAsComplex TS167.Goldbach.unitBoxFunction
  by_cases hy_overlap :
      Membership.mem (Icc (-(1 / 2 : Real)) (x + 1 / 2)) y
  case pos =>
    have hy_box :
        -(1 / 2 : Real) <= y /\ y <= (1 / 2 : Real) := by
      exact And.intro hy_overlap.1 (by linarith [hy_overlap.2, hx_right])
    have hxy_box :
        -(1 / 2 : Real) <= x - y /\ x - y <= (1 / 2 : Real) := by
      exact And.intro (by linarith [hy_overlap.2])
        (by linarith [hy_overlap.1, hx_right])
    rw [indicator_of_mem hy_overlap, if_pos hy_box, if_pos hxy_box]
    norm_num
  case neg =>
    have hnot_or :
        y < -(1 / 2 : Real) \/ x + 1 / 2 < y := by
      have hnot :
          Not (-(1 / 2 : Real) <= y /\ y <= x + 1 / 2) := by
        simpa [mem_Icc] using hy_overlap
      by_cases hleft : -(1 / 2 : Real) <= y
      case pos =>
        right
        exact lt_of_not_ge (by
          intro hy_upper
          exact hnot (And.intro hleft hy_upper))
      case neg =>
        left
        exact lt_of_not_ge hleft
    rw [indicator_of_not_mem hy_overlap]
    cases hnot_or with
    | inl hy_low =>
        have hy_box_not :
            Not (-(1 / 2 : Real) <= y /\ y <= (1 / 2 : Real)) := by
          intro hy_box
          linarith [hy_box.1]
        simp only [hy_box_not, if_false, Complex.ofReal_zero, zero_mul]
    | inr hy_high =>
        have hxy_box_not :
            Not (-(1 / 2 : Real) <= x - y /\ x - y <= (1 / 2 : Real)) := by
          intro hxy_box
          linarith [hxy_box.1, hy_high]
        simp only [hxy_box_not, if_false, Complex.ofReal_zero, mul_zero]

/--
On the right branch `0 <= x <= 1`, the overlap of the two unit boxes is
`[x - 1/2, 1/2]`.
-/
theorem unitBoxConvolutionIntegrand_right
    {x y : Real}
    (hx_left : 0 <= x)
    (_hx_right : x <= 1) :
    TS167.Goldbach.unitBoxAsComplex y *
      TS167.Goldbach.unitBoxAsComplex (x - y) =
        (Icc (x - 1 / 2) (1 / 2 : Real)).indicator
          (fun _ : Real => (1 : Complex)) y := by
  unfold TS167.Goldbach.unitBoxAsComplex TS167.Goldbach.unitBoxFunction
  by_cases hy_overlap :
      Membership.mem (Icc (x - 1 / 2) (1 / 2 : Real)) y
  case pos =>
    have hy_box :
        -(1 / 2 : Real) <= y /\ y <= (1 / 2 : Real) := by
      exact And.intro (by linarith [hy_overlap.1, hx_left]) hy_overlap.2
    have hxy_box :
        -(1 / 2 : Real) <= x - y /\ x - y <= (1 / 2 : Real) := by
      exact And.intro (by linarith [hy_overlap.2])
        (by linarith [hy_overlap.1])
    rw [indicator_of_mem hy_overlap, if_pos hy_box, if_pos hxy_box]
    norm_num
  case neg =>
    have hnot_or :
        y < x - 1 / 2 \/ (1 / 2 : Real) < y := by
      have hnot :
          Not (x - 1 / 2 <= y /\ y <= (1 / 2 : Real)) := by
        simpa [mem_Icc] using hy_overlap
      by_cases hleft : x - 1 / 2 <= y
      case pos =>
        right
        exact lt_of_not_ge (by
          intro hy_upper
          exact hnot (And.intro hleft hy_upper))
      case neg =>
        left
        exact lt_of_not_ge hleft
    rw [indicator_of_not_mem hy_overlap]
    cases hnot_or with
    | inl hy_low =>
        have hxy_box_not :
            Not (-(1 / 2 : Real) <= x - y /\ x - y <= (1 / 2 : Real)) := by
          intro hxy_box
          linarith [hxy_box.2, hy_low]
        simp only [hxy_box_not, if_false, Complex.ofReal_zero, mul_zero]
    | inr hy_high =>
        have hy_box_not :
            Not (-(1 / 2 : Real) <= y /\ y <= (1 / 2 : Real)) := by
          intro hy_box
          linarith [hy_box.2]
        simp only [hy_box_not, if_false, Complex.ofReal_zero, zero_mul]

/-- On the far-left branch, the manual box convolution is zero. -/
theorem unitBoxSelfConvolution_eq_zero_of_lt_neg_one
    {x : Real}
    (hx : x < -1) :
    TS167.Goldbach.unitBoxSelfConvolution x = 0 := by
  unfold TS167.Goldbach.unitBoxSelfConvolution
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall (by
    intro y
    exact unitBoxConvolutionIntegrand_eq_zero_of_lt_neg_one hx))

/-- On the far-right branch, the manual box convolution is zero. -/
theorem unitBoxSelfConvolution_eq_zero_of_gt_one
    {x : Real}
    (hx : 1 < x) :
    TS167.Goldbach.unitBoxSelfConvolution x = 0 := by
  unfold TS167.Goldbach.unitBoxSelfConvolution
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall (by
    intro y
    exact unitBoxConvolutionIntegrand_eq_zero_of_gt_one hx))

/-- On the left branch, the manual box convolution has value `1 + x`. -/
theorem unitBoxSelfConvolution_eq_one_add_of_left
    {x : Real}
    (hx_left : -1 <= x)
    (hx_right : x <= 0) :
    TS167.Goldbach.unitBoxSelfConvolution x =
      (1 + x : Complex) := by
  unfold TS167.Goldbach.unitBoxSelfConvolution
  calc
    integral
        (volume : Measure Real)
        (fun y : Real =>
          TS167.Goldbach.unitBoxAsComplex y *
            TS167.Goldbach.unitBoxAsComplex (x - y))
        =
      integral
        (volume : Measure Real)
        (fun y : Real =>
          (Icc (-(1 / 2 : Real)) (x + 1 / 2)).indicator
            (fun _ : Real => (1 : Complex)) y) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (by
          intro y
          exact unitBoxConvolutionIntegrand_left hx_left hx_right)
    _ =
      (1 + x : Complex) := by
        have hconst :
            integral
              (volume : Measure Real)
              (fun y : Real =>
                (Icc (-(1 / 2 : Real)) (x + 1 / 2)).indicator
                  (fun _ : Real => (1 : Complex)) y)
            =
              ((volume (Icc (-(1 / 2 : Real)) (x + 1 / 2))).toReal : Real) *
                (1 : Complex) := by
          rw [integral_indicator_const (1 : Complex) measurableSet_Icc]
          simp [smul_eq_mul]
        rw [hconst, Real.volume_Icc]
        have hlen_nonneg :
            0 <= x + 1 / 2 - (-(1 / 2 : Real)) := by
          linarith
        rw [ENNReal.toReal_ofReal hlen_nonneg]
        simp
        ring_nf

/-- On the right branch, the manual box convolution has value `1 - x`. -/
theorem unitBoxSelfConvolution_eq_one_sub_of_right
    {x : Real}
    (hx_left : 0 <= x)
    (hx_right : x <= 1) :
    TS167.Goldbach.unitBoxSelfConvolution x =
      (1 - x : Complex) := by
  unfold TS167.Goldbach.unitBoxSelfConvolution
  calc
    integral
        (volume : Measure Real)
        (fun y : Real =>
          TS167.Goldbach.unitBoxAsComplex y *
            TS167.Goldbach.unitBoxAsComplex (x - y))
        =
      integral
        (volume : Measure Real)
        (fun y : Real =>
          (Icc (x - 1 / 2) (1 / 2 : Real)).indicator
            (fun _ : Real => (1 : Complex)) y) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (by
          intro y
          exact unitBoxConvolutionIntegrand_right hx_left hx_right)
    _ =
      (1 - x : Complex) := by
        have hconst :
            integral
              (volume : Measure Real)
              (fun y : Real =>
                (Icc (x - 1 / 2) (1 / 2 : Real)).indicator
                  (fun _ : Real => (1 : Complex)) y)
            =
              ((volume (Icc (x - 1 / 2) (1 / 2 : Real))).toReal : Real) *
                (1 : Complex) := by
          rw [integral_indicator_const (1 : Complex) measurableSet_Icc]
          simp [smul_eq_mul]
        rw [hconst, Real.volume_Icc]
        have hlen_nonneg :
            0 <= (1 / 2 : Real) - (x - 1 / 2) := by
          linarith
        rw [ENNReal.toReal_ofReal hlen_nonneg]
        simp
        ring_nf

/--
The centered unit box self-convolution is exactly the TS166 triangle spline as
a complex-valued function.
-/
theorem boxConvolutionEqualsTriangleSpline :
    TS167.Goldbach.BoxConvolutionEqualsTriangleSplineStatement := by
  intro x
  by_cases hx_left_exterior : x < -1
  case pos =>
    calc
      TS167.Goldbach.unitBoxSelfConvolution x = 0 :=
        unitBoxSelfConvolution_eq_zero_of_lt_neg_one hx_left_exterior
      _ = TS166.Goldbach.triangleSplineAsComplex x := by
        unfold TS166.Goldbach.triangleSplineAsComplex
        have hzero :
            TS42.MellinJackson.triangleSpline x = 0 :=
          TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc (by
            intro hxmem
            exact not_le_of_gt hx_left_exterior hxmem.1)
        rw [hzero]
        norm_num
  case neg =>
    by_cases hx_right_exterior : 1 < x
    case pos =>
      calc
        TS167.Goldbach.unitBoxSelfConvolution x = 0 :=
          unitBoxSelfConvolution_eq_zero_of_gt_one hx_right_exterior
        _ = TS166.Goldbach.triangleSplineAsComplex x := by
          unfold TS166.Goldbach.triangleSplineAsComplex
          have hzero :
              TS42.MellinJackson.triangleSpline x = 0 :=
            TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc (by
              intro hxmem
              exact not_le_of_gt hx_right_exterior hxmem.2)
          rw [hzero]
          norm_num
    case neg =>
      have hx_ge_neg_one : -1 <= x := le_of_not_gt hx_left_exterior
      have hx_le_one : x <= 1 := le_of_not_gt hx_right_exterior
      by_cases hx_nonpos : x <= 0
      case pos =>
        calc
          TS167.Goldbach.unitBoxSelfConvolution x =
              (1 + x : Complex) :=
            unitBoxSelfConvolution_eq_one_add_of_left
              hx_ge_neg_one hx_nonpos
          _ = TS166.Goldbach.triangleSplineAsComplex x := by
            unfold TS166.Goldbach.triangleSplineAsComplex
            rw [TS56.MellinJackson.triangleSpline_eq_one_add_of_left
              hx_ge_neg_one hx_nonpos]
            rw [Complex.ofReal_add]
            norm_num
      case neg =>
        have hx_nonneg : 0 <= x := le_of_lt (lt_of_not_ge hx_nonpos)
        calc
          TS167.Goldbach.unitBoxSelfConvolution x =
              (1 - x : Complex) :=
            unitBoxSelfConvolution_eq_one_sub_of_right
              hx_nonneg hx_le_one
          _ = TS166.Goldbach.triangleSplineAsComplex x := by
            unfold TS166.Goldbach.triangleSplineAsComplex
            rw [TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
              hx_nonneg hx_le_one]
            rw [Complex.ofReal_sub]
            norm_num

/-- Ledger recording the TS210 box-convolution evidence. -/
structure BoxConvolutionTriangleEvidenceLedger where
  ts167_convolution_route :
    TS167.Goldbach.TriangleSplineConvolutionRouteProbeLedger

  ts209_sinc_fourth_scale_reduction :
    TS209.Goldbach.TriangleSplineSincFourthScaleReductionLedger

  box_convolution_statement :
    Prop

  box_convolution_statement_eq :
    box_convolution_statement =
      TS167.Goldbach.BoxConvolutionEqualsTriangleSplineStatement

  box_convolution_statement_proved :
    box_convolution_statement

  box_fourier_evaluation_not_proved :
    True

  fourier_convolution_exchange_not_proved :
    True

  plancherel_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS210 box-convolution evidence ledger. -/
noncomputable def boxConvolutionTriangleEvidenceLedger :
    BoxConvolutionTriangleEvidenceLedger where
  ts167_convolution_route :=
    TS167.Goldbach.triangleSplineConvolutionRouteProbeLedger
  ts209_sinc_fourth_scale_reduction :=
    TS209.Goldbach.triangleSplineSincFourthScaleReductionLedger
  box_convolution_statement :=
    TS167.Goldbach.BoxConvolutionEqualsTriangleSplineStatement
  box_convolution_statement_eq := rfl
  box_convolution_statement_proved :=
    boxConvolutionEqualsTriangleSpline
  box_fourier_evaluation_not_proved := True.intro
  fourier_convolution_exchange_not_proved := True.intro
  plancherel_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS210. -/
def BoxConvolutionTriangleEvidenceTarget : Prop :=
  Nonempty BoxConvolutionTriangleEvidenceLedger

/-- The TS210 box-convolution evidence target is populated. -/
theorem boxConvolutionTriangleEvidenceTarget :
    BoxConvolutionTriangleEvidenceTarget :=
  Nonempty.intro boxConvolutionTriangleEvidenceLedger

end Goldbach
end TS210
