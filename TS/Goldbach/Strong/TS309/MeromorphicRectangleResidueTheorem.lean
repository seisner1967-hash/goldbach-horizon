import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic
import TS.Goldbach.Strong.TS308.CompletePerronSingularityCensus

noncomputable section

namespace TS309
namespace Goldbach

open Complex Filter MeasureTheory Metric Set
open scoped BigOperators Interval

/-! ## Rectangle boundary integral -/

noncomputable def rectangleBoundaryIntegral
  (f : Complex -> Complex)
    (a b c d : Real) : Complex :=
  intervalIntegral (fun x : Real => f ((x : Complex) + (c : Complex) * I))
      a b (volume : Measure Real) -
    intervalIntegral (fun x : Real => f ((x : Complex) + (d : Complex) * I))
      a b (volume : Measure Real) +
      I * intervalIntegral (fun y : Real => f ((b : Complex) + (y : Complex) * I))
        c d (volume : Measure Real) -
        I * intervalIntegral (fun y : Real => f ((a : Complex) + (y : Complex) * I))
          c d (volume : Measure Real)

theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    (f : Complex -> Complex)
    (a b c d : Real)
    (hf : DifferentiableOn Complex f
      (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d))) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((a : Complex) + (c : Complex) * I)
      ((b : Complex) + (d : Complex) * I) (by
        simpa using hf)
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using h

theorem rectangleBoundaryIntegral_vertical_split
    (f : Complex -> Complex)
    (a u b c d : Real)
    (hBottomLeft : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (c : Complex) * I)) volume a u)
    (hBottomRight : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (c : Complex) * I)) volume u b)
    (hTopLeft : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (d : Complex) * I)) volume a u)
    (hTopRight : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (d : Complex) * I)) volume u b) :
    rectangleBoundaryIntegral f a b c d =
      rectangleBoundaryIntegral f a u c d +
        rectangleBoundaryIntegral f u b c d := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hBottomLeft hBottomRight]
  rw [← intervalIntegral.integral_add_adjacent_intervals hTopLeft hTopRight]
  ring

theorem rectangleBoundaryIntegral_horizontal_split
    (f : Complex -> Complex)
    (a b c v d : Real)
    (hLeftBottom : IntervalIntegrable
      (fun y : Real => f ((a : Complex) + (y : Complex) * I)) volume c v)
    (hLeftTop : IntervalIntegrable
      (fun y : Real => f ((a : Complex) + (y : Complex) * I)) volume v d)
    (hRightBottom : IntervalIntegrable
      (fun y : Real => f ((b : Complex) + (y : Complex) * I)) volume c v)
    (hRightTop : IntervalIntegrable
      (fun y : Real => f ((b : Complex) + (y : Complex) * I)) volume v d) :
    rectangleBoundaryIntegral f a b c d =
      rectangleBoundaryIntegral f a b c v +
        rectangleBoundaryIntegral f a b v d := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hLeftBottom hLeftTop]
  rw [← intervalIntegral.integral_add_adjacent_intervals hRightBottom hRightTop]
  ring

/-! ## The simple-pole kernel -/

noncomputable def simplePoleKernel
    (p z : Complex) : Complex :=
  1 / (z - p)

theorem simplePoleKernel_analyticAt
    {p z : Complex}
    (hz : Not (z = p)) :
    AnalyticAt Complex (simplePoleKernel p) z := by
  unfold simplePoleKernel
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hz)

theorem simplePoleKernel_horizontal_intervalIntegrable
    (p : Complex)
    (y a b : Real)
    (hy : Not (y = p.im)) :
    IntervalIntegrable
      (fun x : Real => simplePoleKernel p
        ((x : Complex) + (y : Complex) * I)) volume a b := by
  apply Continuous.intervalIntegrable
  rw [continuous_iff_continuousAt]
  intro x
  have hDen : Not
      (((x : Complex) + (y : Complex) * I) - p = 0) := by
    intro h
    have hIm := congrArg Complex.im h
    apply hy
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re,
      mul_one, mul_zero, zero_add, Complex.zero_im] at hIm
    linarith
  unfold simplePoleKernel
  exact continuousAt_const.div (by fun_prop) hDen

theorem simplePoleKernel_vertical_intervalIntegrable
    (p : Complex)
    (x c d : Real)
    (hx : Not (x = p.re)) :
    IntervalIntegrable
      (fun y : Real => simplePoleKernel p
        ((x : Complex) + (y : Complex) * I)) volume c d := by
  apply Continuous.intervalIntegrable
  rw [continuous_iff_continuousAt]
  intro y
  have hDen : Not
      (((x : Complex) + (y : Complex) * I) - p = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    apply hx
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, mul_one, add_zero, Complex.zero_re] at hRe
    linarith
  unfold simplePoleKernel
  exact continuousAt_const.div (by fun_prop) hDen

theorem simplePoleKernel_differentiableOn_of_avoids
    (p : Complex)
    (S : Set Complex)
    (hp : forall z : Complex, Membership.mem S z -> Not (z = p)) :
    DifferentiableOn Complex (simplePoleKernel p) S := by
  intro z hz
  exact (simplePoleKernel_analyticAt (hp z hz)).differentiableAt.differentiableWithinAt

theorem integral_radius_div_sq_add_sq
    (r : Real)
    (hr : 0 < r) :
    intervalIntegral (fun t : Real => r / (t ^ 2 + r ^ 2))
      (-r) r (volume : Measure Real) = Real.pi / 2 := by
  have hr0 : Not (r = 0) := ne_of_gt hr
  have hDeriv : forall t : Real,
      HasDerivAt (fun u : Real => Real.arctan (u / r))
        (r / (t ^ 2 + r ^ 2)) t := by
    intro t
    convert (Real.hasDerivAt_arctan (t / r)).comp t
      ((hasDerivAt_id t).div_const r) using 1
    all_goals field_simp
    all_goals ring
  have hInt : IntervalIntegrable
      (fun t : Real => r / (t ^ 2 + r ^ 2)) volume (-r) r := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
      (continuous_pow 2 |>.add continuous_const)
    intro t
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hDeriv t) hInt]
  simp only [neg_div, neg_neg, div_self hr0]
  rw [Real.arctan_one, Real.arctan_neg, Real.arctan_one]
  ring

theorem integral_odd_complex_ratio
    (r : Real) :
    intervalIntegral
      (fun t : Real => (t : Complex) /
        ((t ^ 2 + r ^ 2 : Real) : Complex))
      (-r) r (volume : Measure Real) = 0 := by
  let f : Real -> Complex := fun t => (t : Complex) /
    ((t ^ 2 + r ^ 2 : Real) : Complex)
  have hComp := intervalIntegral.integral_comp_neg
    (f := f) (a := -r) (b := r)
  have hOdd : forall t : Real, f (-t) = -f t := by
    intro t
    unfold f
    push_cast
    rw [neg_sq]
    exact neg_div _ _
  simp only [neg_neg] at hComp
  rw [intervalIntegral.integral_congr (fun t _ => hOdd t)] at hComp
  rw [intervalIntegral.integral_neg] at hComp
  change intervalIntegral f (-r) r volume = 0
  exact CharZero.neg_eq_self_iff.mp hComp

theorem simplePoleKernel_zero_bottom_integral
    (r : Real)
    (hr : 0 < r) :
    intervalIntegral
      (fun t : Real => simplePoleKernel 0
        ((t : Complex) - (r : Complex) * I))
      (-r) r (volume : Measure Real) = I * (Real.pi / 2) := by
  have hr0 : Not (r = 0) := ne_of_gt hr
  have hPoint : forall t : Real,
      simplePoleKernel 0 ((t : Complex) - (r : Complex) * I) =
        (t : Complex) / ((t ^ 2 + r ^ 2 : Real) : Complex) +
          I * ((r / (t ^ 2 + r ^ 2) : Real) : Complex) := by
    intro t
    have hLinear : Not ((t : Complex) - (r : Complex) * I = 0) := by
      intro h
      have hIm := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
        mul_zero, sub_eq_zero, Complex.zero_im] at hIm
      exact hr0 (by linarith)
    have hQuad : Not (t ^ 2 + r ^ 2 = 0) := by positivity
    have hQuadC : Not (((t ^ 2 + r ^ 2 : Real) : Complex) = 0) := by
      exact_mod_cast hQuad
    unfold simplePoleKernel
    simp only [sub_zero]
    field_simp [hLinear, hQuadC]
    ring_nf
    rw [show I ^ 2 = (-1 : Complex) by norm_num]
    ring_nf
    rw [<- add_mul]
    have hCast : (t : Complex) ^ 2 + (r : Complex) ^ 2 =
        ((t ^ 2 + r ^ 2 : Real) : Complex) := by
      push_cast
      rfl
    rw [hCast]
    exact (mul_inv_cancel₀ hQuadC).symm
  have hOddInt : IntervalIntegrable
      (fun t : Real => (t : Complex) /
        ((t ^ 2 + r ^ 2 : Real) : Complex)) volume (-r) r := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact_mod_cast (show Not (t ^ 2 + r ^ 2 = 0) by positivity)
  have hRadInt : IntervalIntegrable
      (fun t : Real => I * ((r / (t ^ 2 + r ^ 2) : Real) : Complex))
      volume (-r) r := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Complex.continuous_ofReal.comp
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    positivity
  rw [intervalIntegral.integral_congr (fun t _ => hPoint t)]
  rw [intervalIntegral.integral_add hOddInt hRadInt]
  rw [integral_odd_complex_ratio]
  simp only [zero_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  rw [integral_radius_div_sq_add_sq r hr]
  push_cast
  rfl

theorem complexRadiusRatio_intervalIntegrable
    (r : Real)
    (hr : 0 < r)
    (a b : Real) :
    IntervalIntegrable
      (fun t : Real => ((r / (t ^ 2 + r ^ 2) : Real) : Complex))
      volume a b := by
  apply Continuous.intervalIntegrable
  apply Complex.continuous_ofReal.comp
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  positivity

theorem oddComplexRatio_intervalIntegrable
    (r : Real)
    (hr : 0 < r)
    (a b : Real) :
    IntervalIntegrable
      (fun t : Real => (t : Complex) /
        ((t ^ 2 + r ^ 2 : Real) : Complex))
      volume a b := by
  apply Continuous.intervalIntegrable
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact_mod_cast (show Not (t ^ 2 + r ^ 2 = 0) by positivity)

theorem integral_complex_radius_div_sq_add_sq
    (r : Real)
    (hr : 0 < r) :
    intervalIntegral
      (fun t : Real => ((r / (t ^ 2 + r ^ 2) : Real) : Complex))
      (-r) r (volume : Measure Real) = (Real.pi / 2 : Real) := by
  rw [intervalIntegral.integral_ofReal]
  rw [integral_radius_div_sq_add_sq r hr]

theorem simplePoleKernel_zero_top_point
    (r t : Real)
    (hr : 0 < r) :
    simplePoleKernel 0 ((t : Complex) + (r : Complex) * I) =
      (t : Complex) / ((t ^ 2 + r ^ 2 : Real) : Complex) -
        I * ((r / (t ^ 2 + r ^ 2) : Real) : Complex) := by
  have hr0 : Not (r = 0) := ne_of_gt hr
  have hLinear : Not ((t : Complex) + (r : Complex) * I = 0) := by
    intro h
    have hIm := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
      mul_zero, zero_add, Complex.zero_im] at hIm
    exact hr0 (by linarith)
  have hQuad : Not (t ^ 2 + r ^ 2 = 0) := by positivity
  have hQuadC : Not (((t ^ 2 + r ^ 2 : Real) : Complex) = 0) := by
    exact_mod_cast hQuad
  unfold simplePoleKernel
  simp only [sub_zero]
  field_simp [hLinear, hQuadC]
  ring_nf
  rw [show I ^ 2 = (-1 : Complex) by norm_num]
  ring_nf
  rw [<- add_mul]
  have hCast : (t : Complex) ^ 2 + (r : Complex) ^ 2 =
      ((t ^ 2 + r ^ 2 : Real) : Complex) := by
    push_cast
    rfl
  rw [hCast]
  exact (mul_inv_cancel₀ hQuadC).symm

theorem simplePoleKernel_zero_right_point
    (r t : Real)
    (hr : 0 < r) :
    simplePoleKernel 0 ((r : Complex) + (t : Complex) * I) =
      ((r / (t ^ 2 + r ^ 2) : Real) : Complex) -
        I * ((t : Complex) /
          ((t ^ 2 + r ^ 2 : Real) : Complex)) := by
  have hr0 : Not (r = 0) := ne_of_gt hr
  have hLinear : Not ((r : Complex) + (t : Complex) * I = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
      mul_one, add_zero, Complex.zero_re] at hRe
    exact hr0 (by linarith)
  have hQuad : Not (t ^ 2 + r ^ 2 = 0) := by positivity
  have hQuadC : Not (((t ^ 2 + r ^ 2 : Real) : Complex) = 0) := by
    exact_mod_cast hQuad
  unfold simplePoleKernel
  simp only [sub_zero]
  field_simp [hLinear, hQuadC]
  ring_nf
  rw [show I ^ 2 = (-1 : Complex) by norm_num]
  ring_nf
  rw [<- add_mul]
  have hCast : (t : Complex) ^ 2 + (r : Complex) ^ 2 =
      ((t ^ 2 + r ^ 2 : Real) : Complex) := by
    push_cast
    rfl
  rw [add_comm ((r : Complex) ^ 2) ((t : Complex) ^ 2), hCast]
  exact (mul_inv_cancel₀ hQuadC).symm

theorem simplePoleKernel_zero_left_point
    (r t : Real)
    (hr : 0 < r) :
    simplePoleKernel 0 (-(r : Complex) + (t : Complex) * I) =
      -((r / (t ^ 2 + r ^ 2) : Real) : Complex) -
        I * ((t : Complex) /
          ((t ^ 2 + r ^ 2 : Real) : Complex)) := by
  have hr0 : Not (r = 0) := ne_of_gt hr
  have hLinear : Not (-(r : Complex) + (t : Complex) * I = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, mul_one, add_zero, Complex.zero_re] at hRe
    exact hr0 (by linarith)
  have hQuad : Not (t ^ 2 + r ^ 2 = 0) := by positivity
  have hQuadC : Not (((t ^ 2 + r ^ 2 : Real) : Complex) = 0) := by
    exact_mod_cast hQuad
  unfold simplePoleKernel
  simp only [sub_zero]
  field_simp [hLinear, hQuadC]
  ring_nf
  rw [show I ^ 2 = (-1 : Complex) by norm_num]
  ring_nf
  rw [<- add_mul]
  have hCast : (t : Complex) ^ 2 + (r : Complex) ^ 2 =
      ((t ^ 2 + r ^ 2 : Real) : Complex) := by
    push_cast
    rfl
  rw [add_comm ((r : Complex) ^ 2) ((t : Complex) ^ 2), hCast]
  exact (mul_inv_cancel₀ hQuadC).symm

theorem simplePoleKernel_zero_top_integral
    (r : Real)
    (hr : 0 < r) :
    intervalIntegral
      (fun t : Real => simplePoleKernel 0
        ((t : Complex) + (r : Complex) * I))
      (-r) r (volume : Measure Real) = -(I * (Real.pi / 2)) := by
  have hOdd := oddComplexRatio_intervalIntegrable r hr (-r) r
  have hRad := complexRadiusRatio_intervalIntegrable r hr (-r) r
  have hIRad : IntervalIntegrable
      (fun t : Real => I * ((r / (t ^ 2 + r ^ 2) : Real) : Complex))
      volume (-r) r := hRad.const_mul I
  rw [intervalIntegral.integral_congr
    (fun t _ => simplePoleKernel_zero_top_point r t hr)]
  rw [intervalIntegral.integral_sub hOdd hIRad]
  rw [integral_odd_complex_ratio]
  simp only [zero_sub, intervalIntegral.integral_const_mul]
  rw [integral_complex_radius_div_sq_add_sq r hr]
  push_cast
  rfl

theorem simplePoleKernel_zero_right_integral
    (r : Real)
    (hr : 0 < r) :
    intervalIntegral
      (fun t : Real => simplePoleKernel 0
        ((r : Complex) + (t : Complex) * I))
      (-r) r (volume : Measure Real) = (Real.pi / 2 : Real) := by
  have hOdd := oddComplexRatio_intervalIntegrable r hr (-r) r
  have hRad := complexRadiusRatio_intervalIntegrable r hr (-r) r
  have hIOdd : IntervalIntegrable
      (fun t : Real => I * ((t : Complex) /
        ((t ^ 2 + r ^ 2 : Real) : Complex)))
      volume (-r) r := hOdd.const_mul I
  rw [intervalIntegral.integral_congr
    (fun t _ => simplePoleKernel_zero_right_point r t hr)]
  rw [intervalIntegral.integral_sub hRad hIOdd]
  rw [intervalIntegral.integral_const_mul, integral_odd_complex_ratio]
  simp only [mul_zero, sub_zero]
  exact integral_complex_radius_div_sq_add_sq r hr

theorem simplePoleKernel_zero_left_integral
    (r : Real)
    (hr : 0 < r) :
    intervalIntegral
      (fun t : Real => simplePoleKernel 0
        (-(r : Complex) + (t : Complex) * I))
      (-r) r (volume : Measure Real) = -(Real.pi / 2 : Real) := by
  have hOdd := oddComplexRatio_intervalIntegrable r hr (-r) r
  have hRad := complexRadiusRatio_intervalIntegrable r hr (-r) r
  have hNegRad : IntervalIntegrable
      (fun t : Real => -((r / (t ^ 2 + r ^ 2) : Real) : Complex))
      volume (-r) r := hRad.neg
  have hIOdd : IntervalIntegrable
      (fun t : Real => I * ((t : Complex) /
        ((t ^ 2 + r ^ 2 : Real) : Complex)))
      volume (-r) r := hOdd.const_mul I
  rw [intervalIntegral.integral_congr
    (fun t _ => simplePoleKernel_zero_left_point r t hr)]
  rw [intervalIntegral.integral_sub hNegRad hIOdd]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, integral_odd_complex_ratio]
  simp only [mul_zero, sub_zero]
  rw [integral_complex_radius_div_sq_add_sq r hr]

theorem simplePoleKernel_zero_square_boundaryIntegral
    (r : Real)
    (hr : 0 < r) :
    rectangleBoundaryIntegral (simplePoleKernel 0) (-r) r (-r) r =
      2 * Real.pi * I := by
  unfold rectangleBoundaryIntegral
  push_cast
  have hBottom :
      (fun x : Real => simplePoleKernel 0
        ((x : Complex) + -(r : Complex) * I)) =
        (fun x : Real => simplePoleKernel 0
          ((x : Complex) - (r : Complex) * I)) := by
    funext x
    congr 2
    ring
  rw [hBottom]
  rw [simplePoleKernel_zero_bottom_integral r hr]
  rw [simplePoleKernel_zero_top_integral r hr]
  rw [simplePoleKernel_zero_right_integral r hr]
  rw [simplePoleKernel_zero_left_integral r hr]
  push_cast
  ring

theorem simplePoleKernel_translate
    (p z : Complex) :
    simplePoleKernel p z = simplePoleKernel 0 (z - p) := by
  simp [simplePoleKernel]

set_option maxHeartbeats 1000000 in
theorem simplePoleKernel_centered_square_boundaryIntegral
    (p : Complex)
    (r : Real)
    (hr : 0 < r) :
    rectangleBoundaryIntegral (simplePoleKernel p)
      (p.re - r) (p.re + r) (p.im - r) (p.im + r) =
        2 * Real.pi * I := by
  have hBottom :
      intervalIntegral
        (fun x : Real => simplePoleKernel p
          ((x : Complex) + ((p.im - r : Real) : Complex) * I))
        (p.re - r) (p.re + r) (volume : Measure Real) =
      intervalIntegral
        (fun u : Real => simplePoleKernel 0
          ((u : Complex) - (r : Complex) * I))
        (-r) r (volume : Measure Real) := by
    calc
      _ = intervalIntegral
          (fun x : Real => simplePoleKernel 0
            (((x - p.re : Real) : Complex) - (r : Complex) * I))
          (p.re - r) (p.re + r) volume := by
            apply intervalIntegral.integral_congr
            intro x _
            change simplePoleKernel p
              ((x : Complex) + ((p.im - r : Real) : Complex) * I) = _
            unfold simplePoleKernel
            apply congrArg (fun w : Complex => 1 / w)
            apply Complex.ext <;> simp
      _ = _ := by
        have hShift := intervalIntegral.integral_comp_sub_right
          (a := p.re - r) (b := p.re + r)
          (fun u : Real => simplePoleKernel 0
            ((u : Complex) - (r : Complex) * I)) p.re
        convert hShift using 1
        all_goals ring
  have hTop :
      intervalIntegral
        (fun x : Real => simplePoleKernel p
          ((x : Complex) + ((p.im + r : Real) : Complex) * I))
        (p.re - r) (p.re + r) (volume : Measure Real) =
      intervalIntegral
        (fun u : Real => simplePoleKernel 0
          ((u : Complex) + (r : Complex) * I))
        (-r) r (volume : Measure Real) := by
    calc
      _ = intervalIntegral
          (fun x : Real => simplePoleKernel 0
            (((x - p.re : Real) : Complex) + (r : Complex) * I))
          (p.re - r) (p.re + r) volume := by
            apply intervalIntegral.integral_congr
            intro x _
            change simplePoleKernel p
              ((x : Complex) + ((p.im + r : Real) : Complex) * I) = _
            unfold simplePoleKernel
            apply congrArg (fun w : Complex => 1 / w)
            apply Complex.ext <;> simp
      _ = _ := by
        have hShift := intervalIntegral.integral_comp_sub_right
          (a := p.re - r) (b := p.re + r)
          (fun u : Real => simplePoleKernel 0
            ((u : Complex) + (r : Complex) * I)) p.re
        convert hShift using 1
        all_goals ring
  have hRight :
      intervalIntegral
        (fun y : Real => simplePoleKernel p
          (((p.re + r : Real) : Complex) + (y : Complex) * I))
        (p.im - r) (p.im + r) (volume : Measure Real) =
      intervalIntegral
        (fun u : Real => simplePoleKernel 0
          ((r : Complex) + (u : Complex) * I))
        (-r) r (volume : Measure Real) := by
    calc
      _ = intervalIntegral
          (fun y : Real => simplePoleKernel 0
            ((r : Complex) + ((y - p.im : Real) : Complex) * I))
          (p.im - r) (p.im + r) volume := by
            apply intervalIntegral.integral_congr
            intro y _
            change simplePoleKernel p
              (((p.re + r : Real) : Complex) + (y : Complex) * I) = _
            unfold simplePoleKernel
            apply congrArg (fun w : Complex => 1 / w)
            apply Complex.ext <;> simp
      _ = _ := by
        have hShift := intervalIntegral.integral_comp_sub_right
          (a := p.im - r) (b := p.im + r)
          (fun u : Real => simplePoleKernel 0
            ((r : Complex) + (u : Complex) * I)) p.im
        convert hShift using 1
        all_goals ring
  have hLeft :
      intervalIntegral
        (fun y : Real => simplePoleKernel p
          (((p.re - r : Real) : Complex) + (y : Complex) * I))
        (p.im - r) (p.im + r) (volume : Measure Real) =
      intervalIntegral
        (fun u : Real => simplePoleKernel 0
          (-(r : Complex) + (u : Complex) * I))
        (-r) r (volume : Measure Real) := by
    calc
      _ = intervalIntegral
          (fun y : Real => simplePoleKernel 0
            (-(r : Complex) + ((y - p.im : Real) : Complex) * I))
          (p.im - r) (p.im + r) volume := by
            apply intervalIntegral.integral_congr
            intro y _
            change simplePoleKernel p
              (((p.re - r : Real) : Complex) + (y : Complex) * I) = _
            unfold simplePoleKernel
            apply congrArg (fun w : Complex => 1 / w)
            apply Complex.ext <;> simp
      _ = _ := by
        have hShift := intervalIntegral.integral_comp_sub_right
          (a := p.im - r) (b := p.im + r)
          (fun u : Real => simplePoleKernel 0
            (-(r : Complex) + (u : Complex) * I)) p.im
        convert hShift using 1
        all_goals ring
  unfold rectangleBoundaryIntegral
  rw [hBottom, hTop, hRight, hLeft]
  simpa [rectangleBoundaryIntegral] using
    simplePoleKernel_zero_square_boundaryIntegral r hr

set_option maxHeartbeats 800000 in
theorem simplePoleKernel_rectangleBoundaryIntegral_of_inner_square
    (p : Complex)
    (a b c d r : Real)
    (hr : 0 < r)
    (ha : a < p.re - r)
    (hb : p.re + r < b)
    (hc : c < p.im - r)
    (hd : p.im + r < d) :
    rectangleBoundaryIntegral (simplePoleKernel p) a b c d =
      2 * Real.pi * I := by
  let A : Real := p.re - r
  let B : Real := p.re + r
  let C : Real := p.im - r
  let D : Real := p.im + r
  have hAB : A < B := by dsimp [A, B]; linarith
  have hCD : C < D := by dsimp [C, D]; linarith
  have hac : a < A := by simpa [A] using ha
  have hbb : B < b := by simpa [B] using hb
  have hcc : c < C := by simpa [C] using hc
  have hdd : D < d := by simpa [D] using hd
  have hcNe : Not (c = p.im) := by dsimp [C] at hcc; linarith
  have hdNe : Not (d = p.im) := by dsimp [D] at hdd; linarith
  have hANe : Not (A = p.re) := by dsimp [A]; linarith
  have hBNe : Not (B = p.re) := by dsimp [B]; linarith
  have hLeftZero :
      rectangleBoundaryIntegral (simplePoleKernel p) a A c d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    apply simplePoleKernel_differentiableOn_of_avoids
    intro z hz hzp
    subst z
    rw [Complex.mem_reProdIm] at hz
    have hzRe : p.re ∈ Set.Icc a A := by
      simpa [Set.uIcc_of_le hac.le] using hz.1
    have hRe : p.re <= A := hzRe.2
    dsimp [A] at hRe
    linarith
  have hRightZero :
      rectangleBoundaryIntegral (simplePoleKernel p) B b c d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    apply simplePoleKernel_differentiableOn_of_avoids
    intro z hz hzp
    subst z
    rw [Complex.mem_reProdIm] at hz
    have hzRe : p.re ∈ Set.Icc B b := by
      simpa [Set.uIcc_of_le hbb.le] using hz.1
    have hRe : B <= p.re := hzRe.1
    dsimp [B] at hRe
    linarith
  have hBottomZero :
      rectangleBoundaryIntegral (simplePoleKernel p) A B c C = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    apply simplePoleKernel_differentiableOn_of_avoids
    intro z hz hzp
    subst z
    rw [Complex.mem_reProdIm] at hz
    have hzIm : p.im ∈ Set.Icc c C := by
      simpa [Set.uIcc_of_le hcc.le] using hz.2
    have hIm : p.im <= C := hzIm.2
    dsimp [C] at hIm
    linarith
  have hTopZero :
      rectangleBoundaryIntegral (simplePoleKernel p) A B D d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    apply simplePoleKernel_differentiableOn_of_avoids
    intro z hz hzp
    subst z
    rw [Complex.mem_reProdIm] at hz
    have hzIm : p.im ∈ Set.Icc D d := by
      simpa [Set.uIcc_of_le hdd.le] using hz.2
    have hIm : D <= p.im := hzIm.1
    dsimp [D] at hIm
    linarith
  have hOuterAtA := rectangleBoundaryIntegral_vertical_split
    (simplePoleKernel p) a A b c d
    (simplePoleKernel_horizontal_intervalIntegrable p c a A hcNe)
    (simplePoleKernel_horizontal_intervalIntegrable p c A b hcNe)
    (simplePoleKernel_horizontal_intervalIntegrable p d a A hdNe)
    (simplePoleKernel_horizontal_intervalIntegrable p d A b hdNe)
  have hRestAtB := rectangleBoundaryIntegral_vertical_split
    (simplePoleKernel p) A B b c d
    (simplePoleKernel_horizontal_intervalIntegrable p c A B hcNe)
    (simplePoleKernel_horizontal_intervalIntegrable p c B b hcNe)
    (simplePoleKernel_horizontal_intervalIntegrable p d A B hdNe)
    (simplePoleKernel_horizontal_intervalIntegrable p d B b hdNe)
  have hMiddleAtC := rectangleBoundaryIntegral_horizontal_split
    (simplePoleKernel p) A B c C d
    (simplePoleKernel_vertical_intervalIntegrable p A c C hANe)
    (simplePoleKernel_vertical_intervalIntegrable p A C d hANe)
    (simplePoleKernel_vertical_intervalIntegrable p B c C hBNe)
    (simplePoleKernel_vertical_intervalIntegrable p B C d hBNe)
  have hRestAtD := rectangleBoundaryIntegral_horizontal_split
    (simplePoleKernel p) A B C D d
    (simplePoleKernel_vertical_intervalIntegrable p A C D hANe)
    (simplePoleKernel_vertical_intervalIntegrable p A D d hANe)
    (simplePoleKernel_vertical_intervalIntegrable p B C D hBNe)
    (simplePoleKernel_vertical_intervalIntegrable p B D d hBNe)
  calc
    rectangleBoundaryIntegral (simplePoleKernel p) a b c d =
        rectangleBoundaryIntegral (simplePoleKernel p) a A c d +
          rectangleBoundaryIntegral (simplePoleKernel p) A b c d := hOuterAtA
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A b c d := by
      rw [hLeftZero, zero_add]
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A B c d +
        rectangleBoundaryIntegral (simplePoleKernel p) B b c d := hRestAtB
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A B c d := by
      rw [hRightZero, add_zero]
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A B c C +
        rectangleBoundaryIntegral (simplePoleKernel p) A B C d := hMiddleAtC
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A B C d := by
      rw [hBottomZero, zero_add]
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A B C D +
        rectangleBoundaryIntegral (simplePoleKernel p) A B D d := hRestAtD
    _ = rectangleBoundaryIntegral (simplePoleKernel p) A B C D := by
      rw [hTopZero, add_zero]
    _ = 2 * Real.pi * I := by
      simpa [A, B, C, D] using
        simplePoleKernel_centered_square_boundaryIntegral p r hr

theorem simplePoleKernel_rectangleBoundaryIntegral
    (p : Complex)
    (a b c d : Real)
    (ha : a < p.re)
    (hb : p.re < b)
    (hc : c < p.im)
    (hd : p.im < d) :
    rectangleBoundaryIntegral (simplePoleKernel p) a b c d =
      2 * Real.pi * I := by
  let gap : Real := min (p.re - a)
    (min (b - p.re) (min (p.im - c) (d - p.im)))
  let r : Real := gap / 2
  have hgap : 0 < gap := by
    dsimp [gap]
    simp only [lt_min_iff]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hgapA : gap <= p.re - a := by
    dsimp [gap]
    exact min_le_left _ _
  have hgapB : gap <= b - p.re := by
    dsimp [gap]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hgapC : gap <= p.im - c := by
    dsimp [gap]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgapD : gap <= d - p.im := by
    dsimp [gap]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  apply simplePoleKernel_rectangleBoundaryIntegral_of_inner_square
    p a b c d r
  · dsimp [r]
    linarith
  · dsimp [r]
    change a < p.re - gap / 2
    linarith
  · dsimp [r]
    change p.re + gap / 2 < b
    linarith
  · dsimp [r]
    change c < p.im - gap / 2
    linarith
  · dsimp [r]
    change p.im + gap / 2 < d
    linarith

/-! ## Finite simple-pole regularization -/

noncomputable def certifiedPoleResidue
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    (p : Complex) : Complex :=
  if hp : Membership.mem S p then (data ⟨p, hp⟩).residue else 0

noncomputable def finiteCertifiedPrincipalPart
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    (z : Complex) : Complex :=
  Finset.sum S (fun p =>
    certifiedPoleResidue x S data p * simplePoleKernel p z)

noncomputable def finiteCertifiedPrincipalPartExcept
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    (p z : Complex) : Complex :=
  Finset.sum (S.erase p) (fun q =>
    certifiedPoleResidue x S data q * simplePoleKernel q z)

noncomputable def finitePoleRegularization
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    (z : Complex) : Complex :=
  if hz : Membership.mem S z then
    (data ⟨z, hz⟩).regularPart z -
      finiteCertifiedPrincipalPartExcept x S data z z
  else
    TS293.Goldbach.triangleSplinePerronIntegrand x z -
      finiteCertifiedPrincipalPart x S data z

theorem certifiedPoleResidue_of_mem
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    {p : Complex}
    (hp : Membership.mem S p) :
    certifiedPoleResidue x S data p = (data ⟨p, hp⟩).residue := by
  simp [certifiedPoleResidue, hp]

theorem finiteCertifiedPrincipalPart_eq_add_except
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    {p : Complex}
    (hp : Membership.mem S p)
    (z : Complex) :
    finiteCertifiedPrincipalPart x S data z =
      (data ⟨p, hp⟩).residue * simplePoleKernel p z +
        finiteCertifiedPrincipalPartExcept x S data p z := by
  unfold finiteCertifiedPrincipalPart finiteCertifiedPrincipalPartExcept
  rw [<- Finset.add_sum_erase S
    (fun q => certifiedPoleResidue x S data q * simplePoleKernel q z) hp]
  simp [certifiedPoleResidue, hp]

theorem finiteCertifiedPrincipalPartExcept_analyticAt
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    (p : Complex) :
    AnalyticAt Complex
      (finiteCertifiedPrincipalPartExcept x S data p) p := by
  unfold finiteCertifiedPrincipalPartExcept
  apply Finset.analyticAt_sum
  intro q hq
  have hqp : Not (q = p) := by
    exact (Finset.mem_erase.mp hq).1
  exact analyticAt_const.mul
    (simplePoleKernel_analyticAt (fun h => hqp h.symm))

theorem finiteCertifiedPrincipalPart_analyticAt_of_not_mem
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    {z : Complex}
    (hz : Not (Membership.mem S z)) :
    AnalyticAt Complex (finiteCertifiedPrincipalPart x S data) z := by
  unfold finiteCertifiedPrincipalPart
  apply Finset.analyticAt_sum
  intro p hp
  have hzp : Not (z = p) := by
    intro h
    apply hz
    rwa [h]
  exact analyticAt_const.mul (simplePoleKernel_analyticAt hzp)

set_option maxHeartbeats 800000 in
theorem finitePoleRegularization_analyticAt_of_mem
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    {p : Complex}
    (hp : Membership.mem S p) :
    AnalyticAt Complex (finitePoleRegularization x S data) p := by
  let P := data ⟨p, hp⟩
  let candidate : Complex -> Complex := fun z =>
    P.regularPart z - finiteCertifiedPrincipalPartExcept x S data p z
  have hCandidate : AnalyticAt Complex candidate p := by
    exact P.regularPart_analytic.sub
      (finiteCertifiedPrincipalPartExcept_analyticAt x S data p)
  apply hCandidate.congr
  have hAvoidSet : Filter.Eventually
      (fun z => Not (Membership.mem (S.erase p) z)) (nhds p) := by
    have hpCompl : p ∈ ((S.erase p : Finset Complex) : Set Complex)ᶜ := by
      simp
    exact (S.erase p).isClosed.isOpen_compl.mem_nhds hpCompl
  have hPrincipal : Filter.Eventually
      (fun z => Not (z = p) ->
        TS293.Goldbach.triangleSplinePerronIntegrand x z =
          P.residue / (z - p) + P.regularPart z) (nhds p) := by
    exact mem_nhdsWithin_iff_eventually.mp P.principal_part
  filter_upwards [hAvoidSet, hPrincipal] with z hzAvoid hzPrincipal
  by_cases hzp : z = p
  · subst z
    simp [finitePoleRegularization, hp, candidate, P]
  · have hzNotMem : Not (Membership.mem S z) := by
      intro hzMem
      apply hzAvoid
      exact Finset.mem_erase.mpr ⟨hzp, hzMem⟩
    rw [finitePoleRegularization]
    simp only [dif_neg hzNotMem]
    rw [hzPrincipal hzp]
    rw [finiteCertifiedPrincipalPart_eq_add_except x S data hp z]
    unfold simplePoleKernel candidate P
    ring

theorem finitePoleRegularization_analyticAt_of_not_mem
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    {z : Complex}
    (hz : Not (Membership.mem S z))
    (hf : AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x) z) :
    AnalyticAt Complex (finitePoleRegularization x S data) z := by
  have hCandidate : AnalyticAt Complex
      (fun w => TS293.Goldbach.triangleSplinePerronIntegrand x w -
        finiteCertifiedPrincipalPart x S data w) z :=
    hf.sub (finiteCertifiedPrincipalPart_analyticAt_of_not_mem x S data hz)
  apply hCandidate.congr
  have hzCompl : z ∈ ((S : Finset Complex) : Set Complex)ᶜ := by
    simpa using hz
  have hAvoid : Filter.Eventually
      (fun w => Not (Membership.mem S w)) (nhds z) :=
    S.isClosed.isOpen_compl.mem_nhds hzCompl
  filter_upwards [hAvoid] with w hw
  simp [finitePoleRegularization, hw]

/-! ## Linear boundary bookkeeping -/

theorem rectangleBoundaryIntegral_congr
    (f g : Complex -> Complex)
    (a b c d : Real)
    (hBottom : forall x : Real,
      f ((x : Complex) + (c : Complex) * I) =
        g ((x : Complex) + (c : Complex) * I))
    (hTop : forall x : Real,
      f ((x : Complex) + (d : Complex) * I) =
        g ((x : Complex) + (d : Complex) * I))
    (hRight : forall y : Real,
      f ((b : Complex) + (y : Complex) * I) =
        g ((b : Complex) + (y : Complex) * I))
    (hLeft : forall y : Real,
      f ((a : Complex) + (y : Complex) * I) =
        g ((a : Complex) + (y : Complex) * I)) :
    rectangleBoundaryIntegral f a b c d =
      rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_congr (fun x _ => hBottom x)]
  rw [intervalIntegral.integral_congr (fun x _ => hTop x)]
  rw [intervalIntegral.integral_congr (fun y _ => hRight y)]
  rw [intervalIntegral.integral_congr (fun y _ => hLeft y)]

theorem rectangleBoundaryIntegral_const_mul
    (k : Complex)
    (f : Complex -> Complex)
    (a b c d : Real) :
    rectangleBoundaryIntegral (fun z => k * f z) a b c d =
      k * rectangleBoundaryIntegral f a b c d := by
  unfold rectangleBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem rectangleBoundaryIntegral_add
    (f g : Complex -> Complex)
    (a b c d : Real)
    (hfBottom : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (c : Complex) * I)) volume a b)
    (hgBottom : IntervalIntegrable
      (fun x : Real => g ((x : Complex) + (c : Complex) * I)) volume a b)
    (hfTop : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (d : Complex) * I)) volume a b)
    (hgTop : IntervalIntegrable
      (fun x : Real => g ((x : Complex) + (d : Complex) * I)) volume a b)
    (hfRight : IntervalIntegrable
      (fun y : Real => f ((b : Complex) + (y : Complex) * I)) volume c d)
    (hgRight : IntervalIntegrable
      (fun y : Real => g ((b : Complex) + (y : Complex) * I)) volume c d)
    (hfLeft : IntervalIntegrable
      (fun y : Real => f ((a : Complex) + (y : Complex) * I)) volume c d)
    (hgLeft : IntervalIntegrable
      (fun y : Real => g ((a : Complex) + (y : Complex) * I)) volume c d) :
    rectangleBoundaryIntegral (fun z => f z + g z) a b c d =
      rectangleBoundaryIntegral f a b c d +
        rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hfBottom hgBottom]
  rw [intervalIntegral.integral_add hfTop hgTop]
  rw [intervalIntegral.integral_add hfRight hgRight]
  rw [intervalIntegral.integral_add hfLeft hgLeft]
  ring

theorem rectangleBoundaryIntegral_sub
    (f g : Complex -> Complex)
    (a b c d : Real)
    (hfBottom : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (c : Complex) * I)) volume a b)
    (hgBottom : IntervalIntegrable
      (fun x : Real => g ((x : Complex) + (c : Complex) * I)) volume a b)
    (hfTop : IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (d : Complex) * I)) volume a b)
    (hgTop : IntervalIntegrable
      (fun x : Real => g ((x : Complex) + (d : Complex) * I)) volume a b)
    (hfRight : IntervalIntegrable
      (fun y : Real => f ((b : Complex) + (y : Complex) * I)) volume c d)
    (hgRight : IntervalIntegrable
      (fun y : Real => g ((b : Complex) + (y : Complex) * I)) volume c d)
    (hfLeft : IntervalIntegrable
      (fun y : Real => f ((a : Complex) + (y : Complex) * I)) volume c d)
    (hgLeft : IntervalIntegrable
      (fun y : Real => g ((a : Complex) + (y : Complex) * I)) volume c d) :
    rectangleBoundaryIntegral (fun z => f z - g z) a b c d =
      rectangleBoundaryIntegral f a b c d -
        rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_sub hfBottom hgBottom]
  rw [intervalIntegral.integral_sub hfTop hgTop]
  rw [intervalIntegral.integral_sub hfRight hgRight]
  rw [intervalIntegral.integral_sub hfLeft hgLeft]
  ring

theorem finset_boundary_sum_algebra
    {alpha : Type*}
    (S : Finset alpha)
    (bottom top right left : alpha -> Complex) :
    (Finset.sum S bottom - Finset.sum S top) +
        Finset.sum S right - Finset.sum S left =
      Finset.sum S (fun q =>
        (bottom q - top q) + right q - left q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
      simp only [Finset.sum_insert hq]
      rw [<- ih]
      ring

theorem rectangleBoundaryIntegral_finset_sum
    {alpha : Type*}
    (S : Finset alpha)
    (f : alpha -> Complex -> Complex)
    (a b c d : Real)
    (hBottom : forall q : alpha, Membership.mem S q -> IntervalIntegrable
      (fun x : Real => f q ((x : Complex) + (c : Complex) * I)) volume a b)
    (hTop : forall q : alpha, Membership.mem S q -> IntervalIntegrable
      (fun x : Real => f q ((x : Complex) + (d : Complex) * I)) volume a b)
    (hRight : forall q : alpha, Membership.mem S q -> IntervalIntegrable
      (fun y : Real => f q ((b : Complex) + (y : Complex) * I)) volume c d)
    (hLeft : forall q : alpha, Membership.mem S q -> IntervalIntegrable
      (fun y : Real => f q ((a : Complex) + (y : Complex) * I)) volume c d) :
    rectangleBoundaryIntegral (fun z => Finset.sum S (fun q => f q z))
        a b c d =
      Finset.sum S (fun q => rectangleBoundaryIntegral (f q) a b c d) := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_finset_sum hBottom]
  rw [intervalIntegral.integral_finset_sum hTop]
  rw [intervalIntegral.integral_finset_sum hRight]
  rw [intervalIntegral.integral_finset_sum hLeft]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact finset_boundary_sum_algebra S
    (fun q => intervalIntegral
      (fun x : Real => f q ((x : Complex) + (c : Complex) * I)) a b volume)
    (fun q => intervalIntegral
      (fun x : Real => f q ((x : Complex) + (d : Complex) * I)) a b volume)
    (fun q => I * intervalIntegral
      (fun y : Real => f q ((b : Complex) + (y : Complex) * I)) c d volume)
    (fun q => I * intervalIntegral
      (fun y : Real => f q ((a : Complex) + (y : Complex) * I)) c d volume)

theorem horizontal_intervalIntegrable_of_analyticAt
    (f : Complex -> Complex)
    (y a b : Real)
    (hf : forall x : Real,
      AnalyticAt Complex f ((x : Complex) + (y : Complex) * I)) :
    IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (y : Complex) * I))
      volume a b := by
  apply Continuous.intervalIntegrable
  rw [continuous_iff_continuousAt]
  intro x
  let g : Real -> Complex := fun u =>
    (u : Complex) + (y : Complex) * I
  have hg : ContinuousAt g x := by
    dsimp [g]
    fun_prop
  have hfg : ContinuousAt f (g x) := by
    simpa [g] using (hf x).continuousAt
  change ContinuousAt (fun u => f (g u)) x
  exact hfg.comp' hg

theorem vertical_intervalIntegrable_of_analyticAt
    (f : Complex -> Complex)
    (x c d : Real)
    (hf : forall y : Real,
      AnalyticAt Complex f ((x : Complex) + (y : Complex) * I)) :
    IntervalIntegrable
      (fun y : Real => f ((x : Complex) + (y : Complex) * I))
      volume c d := by
  apply Continuous.intervalIntegrable
  rw [continuous_iff_continuousAt]
  intro y
  let g : Real -> Complex := fun u =>
    (x : Complex) + (u : Complex) * I
  have hg : ContinuousAt g y := by
    dsimp [g]
    fun_prop
  have hfg : ContinuousAt f (g y) := by
    simpa [g] using (hf y).continuousAt
  change ContinuousAt (fun u => f (g u)) y
  exact hfg.comp' hg

theorem horizontal_intervalIntegrable_of_analyticAt_on
    (f : Complex -> Complex)
    (y a b : Real)
    (hf : forall x : Real, Membership.mem (Set.uIcc a b) x ->
      AnalyticAt Complex f ((x : Complex) + (y : Complex) * I)) :
    IntervalIntegrable
      (fun x : Real => f ((x : Complex) + (y : Complex) * I))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  let g : Real -> Complex := fun u =>
    (u : Complex) + (y : Complex) * I
  have hg : ContinuousAt g x := by
    dsimp [g]
    fun_prop
  have hfg : ContinuousAt f (g x) := by
    simpa [g] using (hf x hx).continuousAt
  exact (hfg.comp' hg).continuousWithinAt

theorem vertical_intervalIntegrable_of_analyticAt_on
    (f : Complex -> Complex)
    (x c d : Real)
    (hf : forall y : Real, Membership.mem (Set.uIcc c d) y ->
      AnalyticAt Complex f ((x : Complex) + (y : Complex) * I)) :
    IntervalIntegrable
      (fun y : Real => f ((x : Complex) + (y : Complex) * I))
      volume c d := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  let g : Real -> Complex := fun u =>
    (x : Complex) + (u : Complex) * I
  have hg : ContinuousAt g y := by
    dsimp [g]
    fun_prop
  have hfg : ContinuousAt f (g y) := by
    simpa [g] using (hf y hy).continuousAt
  exact (hfg.comp' hg).continuousWithinAt

set_option maxHeartbeats 1200000 in
theorem finite_simple_pole_rectangle_residue_theorem
    (x : Nat)
    (S : Finset Complex)
    (data : forall p : {z : Complex // Membership.mem S z},
      TS293.Goldbach.PerronLocalResidueData x p.1)
    (a b c d : Real)
    (hab : a < b)
    (hcd : c < d)
    (hInside : forall p : Complex, Membership.mem S p ->
      a < p.re /\ p.re < b /\ c < p.im /\ p.im < d)
    (hRegular : forall z : Complex,
      Membership.mem
        (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d)) z ->
      Not (Membership.mem S z) ->
        AnalyticAt Complex
          (TS293.Goldbach.triangleSplinePerronIntegrand x) z) :
    rectangleBoundaryIntegral
        (TS293.Goldbach.triangleSplinePerronIntegrand x) a b c d =
      (2 * Real.pi * I) *
        Finset.sum S (certifiedPoleResidue x S data) := by
  let f := TS293.Goldbach.triangleSplinePerronIntegrand x
  let principal := finiteCertifiedPrincipalPart x S data
  let regularized := finitePoleRegularization x S data
  have hAnalyticRegularized : forall z : Complex,
      Membership.mem
        (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d)) z ->
        AnalyticAt Complex regularized z := by
    intro z hz
    by_cases hzS : Membership.mem S z
    · exact finitePoleRegularization_analyticAt_of_mem x S data hzS
    · exact finitePoleRegularization_analyticAt_of_not_mem
        x S data hzS (hRegular z hz hzS)
  have hRegularizedZero :
      rectangleBoundaryIntegral regularized a b c d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    intro z hz
    exact (hAnalyticRegularized z hz).differentiableAt.differentiableWithinAt
  have hBottomNotMem : forall sigma : Real,
      Not (Membership.mem S
        ((sigma : Complex) + (c : Complex) * I)) := by
    intro sigma hs
    have h := hInside _ hs
    have hIm :
        (((sigma : Complex) + (c : Complex) * I).im : Real) = c := by simp
    rw [hIm] at h
    linarith
  have hTopNotMem : forall sigma : Real,
      Not (Membership.mem S
        ((sigma : Complex) + (d : Complex) * I)) := by
    intro sigma hs
    have h := hInside _ hs
    have hIm :
        (((sigma : Complex) + (d : Complex) * I).im : Real) = d := by simp
    rw [hIm] at h
    linarith
  have hRightNotMem : forall t : Real,
      Not (Membership.mem S
        ((b : Complex) + (t : Complex) * I)) := by
    intro t hs
    have h := hInside _ hs
    have hRe :
        (((b : Complex) + (t : Complex) * I).re : Real) = b := by simp
    rw [hRe] at h
    linarith
  have hLeftNotMem : forall t : Real,
      Not (Membership.mem S
        ((a : Complex) + (t : Complex) * I)) := by
    intro t hs
    have h := hInside _ hs
    have hRe :
        (((a : Complex) + (t : Complex) * I).re : Real) = a := by simp
    rw [hRe] at h
    linarith
  have hBottomRect : forall sigma : Real,
      Membership.mem (Set.uIcc a b) sigma ->
      Membership.mem
        (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d))
        ((sigma : Complex) + (c : Complex) * I) := by
    intro sigma hs
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hs
    · simp [Set.uIcc_of_le hcd.le, hcd.le]
  have hTopRect : forall sigma : Real,
      Membership.mem (Set.uIcc a b) sigma ->
      Membership.mem
        (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d))
        ((sigma : Complex) + (d : Complex) * I) := by
    intro sigma hs
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hs
    · simp [Set.uIcc_of_le hcd.le, hcd.le]
  have hRightRect : forall t : Real,
      Membership.mem (Set.uIcc c d) t ->
      Membership.mem
        (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d))
        ((b : Complex) + (t : Complex) * I) := by
    intro t ht
    rw [Complex.mem_reProdIm]
    constructor
    · simp [Set.uIcc_of_le hab.le, hab.le]
    · simpa using ht
  have hLeftRect : forall t : Real,
      Membership.mem (Set.uIcc c d) t ->
      Membership.mem
        (Complex.reProdIm (Set.uIcc a b) (Set.uIcc c d))
        ((a : Complex) + (t : Complex) * I) := by
    intro t ht
    rw [Complex.mem_reProdIm]
    constructor
    · simp [Set.uIcc_of_le hab.le, hab.le]
    · simpa using ht
  have hfBottom : IntervalIntegrable
      (fun sigma : Real => f ((sigma : Complex) + (c : Complex) * I))
      volume a b := by
    apply horizontal_intervalIntegrable_of_analyticAt_on
    intro sigma hs
    exact hRegular _ (hBottomRect sigma hs) (hBottomNotMem sigma)
  have hfTop : IntervalIntegrable
      (fun sigma : Real => f ((sigma : Complex) + (d : Complex) * I))
      volume a b := by
    apply horizontal_intervalIntegrable_of_analyticAt_on
    intro sigma hs
    exact hRegular _ (hTopRect sigma hs) (hTopNotMem sigma)
  have hfRight : IntervalIntegrable
      (fun t : Real => f ((b : Complex) + (t : Complex) * I))
      volume c d := by
    apply vertical_intervalIntegrable_of_analyticAt_on
    intro t ht
    exact hRegular _ (hRightRect t ht) (hRightNotMem t)
  have hfLeft : IntervalIntegrable
      (fun t : Real => f ((a : Complex) + (t : Complex) * I))
      volume c d := by
    apply vertical_intervalIntegrable_of_analyticAt_on
    intro t ht
    exact hRegular _ (hLeftRect t ht) (hLeftNotMem t)
  have hpBottom : IntervalIntegrable
      (fun sigma : Real => principal
        ((sigma : Complex) + (c : Complex) * I)) volume a b := by
    apply horizontal_intervalIntegrable_of_analyticAt_on
    intro sigma _hs
    exact finiteCertifiedPrincipalPart_analyticAt_of_not_mem
      x S data (hBottomNotMem sigma)
  have hpTop : IntervalIntegrable
      (fun sigma : Real => principal
        ((sigma : Complex) + (d : Complex) * I)) volume a b := by
    apply horizontal_intervalIntegrable_of_analyticAt_on
    intro sigma _hs
    exact finiteCertifiedPrincipalPart_analyticAt_of_not_mem
      x S data (hTopNotMem sigma)
  have hpRight : IntervalIntegrable
      (fun t : Real => principal
        ((b : Complex) + (t : Complex) * I)) volume c d := by
    apply vertical_intervalIntegrable_of_analyticAt_on
    intro t _ht
    exact finiteCertifiedPrincipalPart_analyticAt_of_not_mem
      x S data (hRightNotMem t)
  have hpLeft : IntervalIntegrable
      (fun t : Real => principal
        ((a : Complex) + (t : Complex) * I)) volume c d := by
    apply vertical_intervalIntegrable_of_analyticAt_on
    intro t _ht
    exact finiteCertifiedPrincipalPart_analyticAt_of_not_mem
      x S data (hLeftNotMem t)
  have hRegularizedEqSub :
      rectangleBoundaryIntegral regularized a b c d =
        rectangleBoundaryIntegral (fun z => f z - principal z) a b c d := by
    apply rectangleBoundaryIntegral_congr
    · intro sigma
      simp [regularized, finitePoleRegularization, f,
        principal, hBottomNotMem sigma]
    · intro sigma
      simp [regularized, finitePoleRegularization, f,
        principal, hTopNotMem sigma]
    · intro t
      simp [regularized, finitePoleRegularization, f,
        principal, hRightNotMem t]
    · intro t
      simp [regularized, finitePoleRegularization, f,
        principal, hLeftNotMem t]
  have hSub := rectangleBoundaryIntegral_sub f principal a b c d
    hfBottom hpBottom hfTop hpTop hfRight hpRight hfLeft hpLeft
  have hfEqPrincipal :
      rectangleBoundaryIntegral f a b c d =
        rectangleBoundaryIntegral principal a b c d := by
    apply sub_eq_zero.mp
    rw [<- hSub, <- hRegularizedEqSub, hRegularizedZero]
  have hPrincipalBoundary :
      rectangleBoundaryIntegral principal a b c d =
        (2 * Real.pi * I) *
          Finset.sum S (certifiedPoleResidue x S data) := by
    unfold principal finiteCertifiedPrincipalPart
    rw [rectangleBoundaryIntegral_finset_sum S
      (fun p z => certifiedPoleResidue x S data p * simplePoleKernel p z)
      a b c d]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [rectangleBoundaryIntegral_const_mul]
      rw [simplePoleKernel_rectangleBoundaryIntegral p a b c d
        (hInside p hp).1 (hInside p hp).2.1
        (hInside p hp).2.2.1 (hInside p hp).2.2.2]
      ring
    · intro p hp
      exact (simplePoleKernel_horizontal_intervalIntegrable p c a b
        (by linarith [hInside p hp])).const_mul _
    · intro p hp
      exact (simplePoleKernel_horizontal_intervalIntegrable p d a b
        (by linarith [hInside p hp])).const_mul _
    · intro p hp
      exact (simplePoleKernel_vertical_intervalIntegrable p b c d
        (by linarith [hInside p hp])).const_mul _
    · intro p hp
      exact (simplePoleKernel_vertical_intervalIntegrable p a c d
        (by linarith [hInside p hp])).const_mul _
  change rectangleBoundaryIntegral f a b c d = _
  rw [hfEqPrincipal, hPrincipalBoundary]

/-! ## Instantiation of the TS308 census -/

noncomputable def castPerronLocalResidueData
    {x : Nat}
    {p q : Complex}
    (h : p = q)
    (P : TS293.Goldbach.PerronLocalResidueData x p) :
    TS293.Goldbach.PerronLocalResidueData x q := by
  subst q
  exact P

@[simp]
theorem castPerronLocalResidueData_residue
    {x : Nat}
    {p q : Complex}
    (h : p = q)
    (P : TS293.Goldbach.PerronLocalResidueData x p) :
    (castPerronLocalResidueData h P).residue = P.residue := by
  subst q
  rfl

noncomputable def completeCensusResidueData
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    (p : {z : Complex // Membership.mem C.poles z}) :
    TS293.Goldbach.PerronLocalResidueData x p.1 := by
  classical
  by_cases hpOne : p.1 = 1
  · exact castPerronLocalResidueData hpOne.symm C.mainPole
  by_cases hpExceptional :
      Membership.mem C.exceptional.inventory.poles p.1
  · exact C.exceptional.inventory.residueData ⟨p.1, hpExceptional⟩
  have hpComplete :
      Membership.mem (TS308.Goldbach.completePerronPoleValues D.tau) p.1 := by
    rw [<- C.poles_eq]
    exact p.2
  have hpZeroValue :
      Membership.mem (TS308.Goldbach.realHeightZeroValues D.tau) p.1 := by
    have hpExceptionalConcrete :
        Not (Membership.mem TS306.Goldbach.perronExceptionalPoles p.1) := by
      rwa [<- C.exceptional.poles_eq]
    have hpNotZero : Not (p.1 = 0) := by
      intro h
      apply hpExceptionalConcrete
      simp [TS306.Goldbach.perronExceptionalPoles, h]
    have hpNotNegOne : Not (p.1 = -1) := by
      intro h
      apply hpExceptionalConcrete
      simp [TS306.Goldbach.perronExceptionalPoles, h]
    simp only [TS308.Goldbach.completePerronPoleValues,
      Finset.mem_insert] at hpComplete
    rcases hpComplete with h | h | h | h
    · exact False.elim (hpOne h)
    · exact False.elim (hpNotZero h)
    · exact False.elim (hpNotNegOne h)
    · exact h
  let rho := Classical.choose
    ((TS308.Goldbach.mem_realHeightZeroValues_iff D.tau p.1).mp hpZeroValue)
  have hrho := Classical.choose_spec
    ((TS308.Goldbach.mem_realHeightZeroValues_iff D.tau p.1).mp hpZeroValue)
  exact castPerronLocalResidueData hrho.2
    (C.zeroPole rho hrho.1)

theorem completeCensusResidueData_main
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    (hOne : Membership.mem C.poles (1 : Complex)) :
    (completeCensusResidueData C ⟨1, hOne⟩).residue =
      C.mainPole.residue := by
  simp [completeCensusResidueData]

theorem completeCensusResidueData_exceptional
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    (p : Complex)
    (hpC : Membership.mem C.poles p)
    (hpExceptional : Membership.mem C.exceptional.inventory.poles p)
    (hpOne : Not (p = 1)) :
    (completeCensusResidueData C ⟨p, hpC⟩).residue =
      (C.exceptional.inventory.residueData
        ⟨p, hpExceptional⟩).residue := by
  simp [completeCensusResidueData, hpOne, hpExceptional]

theorem completeCensusZeroPole_residue_congr
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    (rho rho' : TS292.Goldbach.ConcreteNontrivialZero)
    (h : rho = rho')
    (hrho : Membership.mem
      (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho)
    (hrho' : Membership.mem
      (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho') :
    (C.zeroPole rho hrho).residue =
      (C.zeroPole rho' hrho').residue := by
  subst rho'
  rfl

set_option maxHeartbeats 600000 in
theorem completeCensusResidueData_zero
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hrho : Membership.mem
      (TS293.Goldbach.concreteZerosUpToRealHeight D.tau) rho)
    (hC : Membership.mem C.poles rho.1) :
    (completeCensusResidueData C ⟨rho.1, hC⟩).residue =
      (C.zeroPole rho hrho).residue := by
  classical
  have hNotOne : Not (rho.1 = 1) := by
    intro h
    have hPos := rho.property.2.2
    rw [h] at hPos
    norm_num at hPos
  have hNotExceptional :
      Not (Membership.mem C.exceptional.inventory.poles rho.1) := by
    intro h
    exact Finset.disjoint_left.mp C.exceptional_disjoint_zero_values
      h ((TS308.Goldbach.mem_realHeightZeroValues_iff D.tau rho.1).mpr
        ⟨rho, hrho, rfl⟩)
  rw [completeCensusResidueData]
  simp only [dif_neg hNotOne, dif_neg hNotExceptional]
  let hZeroValue :
      Membership.mem (TS308.Goldbach.realHeightZeroValues D.tau) rho.1 :=
    (TS308.Goldbach.mem_realHeightZeroValues_iff D.tau rho.1).mpr
      ⟨rho, hrho, rfl⟩
  let hExists :=
    (TS308.Goldbach.mem_realHeightZeroValues_iff D.tau rho.1).mp hZeroValue
  let chosen := Classical.choose hExists
  have hChosen := Classical.choose_spec hExists
  have hChosenEq : chosen = rho := by
    apply Subtype.ext
    exact hChosen.2
  change (castPerronLocalResidueData _
    (C.zeroPole chosen _)).residue = (C.zeroPole rho hrho).residue
  rw [castPerronLocalResidueData_residue]
  exact completeCensusZeroPole_residue_congr C chosen rho hChosenEq _ hrho

theorem completeCensus_poles_eq_insert_union
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    C.poles = insert 1 (insert 0 (insert (-1)
      (TS308.Goldbach.realHeightZeroValues D.tau))) := by
  exact C.poles_eq

theorem one_mem_completeCensus_poles
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    Membership.mem C.poles (1 : Complex) := by
  rw [completeCensus_poles_eq_insert_union C]
  simp

theorem exceptional_mem_completeCensus_poles
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    {p : Complex}
    (hp : Membership.mem C.exceptional.inventory.poles p) :
    Membership.mem C.poles p := by
  have hp' : p = 0 \/ p = -1 := by
    rw [C.exceptional.poles_eq] at hp
    simpa [TS306.Goldbach.perronExceptionalPoles] using hp
  rw [completeCensus_poles_eq_insert_union C]
  rcases hp' with rfl | rfl <;> simp

theorem zeroValue_mem_completeCensus_poles
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    {p : Complex}
    (hp : Membership.mem
      (TS308.Goldbach.realHeightZeroValues D.tau) p) :
    Membership.mem C.poles p := by
  rw [completeCensus_poles_eq_insert_union C]
  simp [hp]

theorem completeCensus_exceptionalResidueSum
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    Finset.sum C.exceptional.inventory.poles
        (certifiedPoleResidue x C.poles (completeCensusResidueData C)) =
      TS293.Goldbach.exceptionalResidueContribution
        C.exceptional.inventory := by
  classical
  unfold TS293.Goldbach.exceptionalResidueContribution
  calc
    Finset.sum C.exceptional.inventory.poles
        (certifiedPoleResidue x C.poles (completeCensusResidueData C)) =
        Finset.sum C.exceptional.inventory.poles.attach
          (fun p => certifiedPoleResidue x C.poles
            (completeCensusResidueData C) p.1) := by
      symm
      exact Finset.sum_attach C.exceptional.inventory.poles
        (certifiedPoleResidue x C.poles (completeCensusResidueData C))
    _ = Finset.sum C.exceptional.inventory.poles.attach
        (fun p => (C.exceptional.inventory.residueData p).residue) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpC := exceptional_mem_completeCensus_poles C p.2
      have hpOne : Not (p.1 = 1) := by
        intro h
        apply C.exceptional.one_not_mem
        simpa [h] using p.2
      rw [certifiedPoleResidue_of_mem x C.poles
        (completeCensusResidueData C) hpC]
      exact completeCensusResidueData_exceptional C p.1 hpC p.2 hpOne

theorem completeCensus_zeroResidueSum
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    Finset.sum (TS308.Goldbach.realHeightZeroValues D.tau)
        (certifiedPoleResidue x C.poles (completeCensusResidueData C)) =
      Finset.sum
        (TS293.Goldbach.concreteZerosUpToRealHeight D.tau).attach
        (fun rho => (C.zeroPole rho.1 rho.2).residue) := by
  classical
  let zeros := TS293.Goldbach.concreteZerosUpToRealHeight D.tau
  let residueAtValue : Complex -> Complex :=
    certifiedPoleResidue x C.poles (completeCensusResidueData C)
  calc
    Finset.sum (TS308.Goldbach.realHeightZeroValues D.tau)
        (certifiedPoleResidue x C.poles (completeCensusResidueData C)) =
        Finset.sum zeros (fun rho => residueAtValue rho.1) := by
      unfold TS308.Goldbach.realHeightZeroValues zeros residueAtValue
      rw [Finset.sum_image]
      intro rho _ rho' _ h
      exact Subtype.ext h
    _ = Finset.sum zeros.attach (fun rho => residueAtValue rho.1) := by
      symm
      exact Finset.sum_attach zeros (fun rho => residueAtValue rho.1)
    _ = Finset.sum zeros.attach
        (fun rho => (C.zeroPole rho.1 rho.2).residue) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hValue : Membership.mem
          (TS308.Goldbach.realHeightZeroValues D.tau) rho.1.1 :=
        (TS308.Goldbach.mem_realHeightZeroValues_iff D.tau rho.1.1).mpr
          (Exists.intro rho.1 (And.intro rho.2 rfl))
      have hpC := zeroValue_mem_completeCensus_poles C hValue
      unfold residueAtValue
      rw [certifiedPoleResidue_of_mem x C.poles
        (completeCensusResidueData C) hpC]
      exact completeCensusResidueData_zero C rho.1 rho.2 hpC

theorem exceptionalPole_not_mem_zeroValues
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    {p : Complex}
    (hp : Membership.mem C.exceptional.inventory.poles p) :
    Not (Membership.mem
      (TS308.Goldbach.realHeightZeroValues D.tau) p) := by
  intro hpZero
  exact Finset.disjoint_left.mp C.exceptional_disjoint_zero_values hp hpZero

theorem completeCensusResidueSum_eq_accounting
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    Finset.sum C.poles
        (certifiedPoleResidue x C.poles (completeCensusResidueData C)) =
      (x : Complex) / 2 -
        TS293.Goldbach.realHeightZeroContribution x D.tau +
          TS293.Goldbach.exceptionalResidueContribution
            C.exceptional.inventory := by
  classical
  let zeros := TS308.Goldbach.realHeightZeroValues D.tau
  have hOneNot : Not (Membership.mem (insert 0 (insert (-1) zeros))
      (1 : Complex)) := by
    norm_num [zeros, C.one_not_mem_zero_values]
  have hZeroExceptional : Membership.mem C.exceptional.inventory.poles
      (0 : Complex) := by
    rw [C.exceptional.poles_eq]
    simp [TS306.Goldbach.perronExceptionalPoles]
  have hNegOneExceptional : Membership.mem C.exceptional.inventory.poles
      (-1 : Complex) := by
    rw [C.exceptional.poles_eq]
    simp [TS306.Goldbach.perronExceptionalPoles]
  have hZeroNot : Not (Membership.mem (insert (-1) zeros) (0 : Complex)) := by
    simp [zeros, exceptionalPole_not_mem_zeroValues C hZeroExceptional]
  have hNegOneNot : Not (Membership.mem zeros (-1 : Complex)) :=
    exceptionalPole_not_mem_zeroValues C hNegOneExceptional
  have hMain := completeCensusResidueData_main C
    (one_mem_completeCensus_poles C)
  have hExceptional := completeCensus_exceptionalResidueSum C
  have hZeroSum := completeCensus_zeroResidueSum C
  have hAccounting := C.residue_accounting
  have hPoleSum :
      Finset.sum C.poles
          (certifiedPoleResidue x C.poles (completeCensusResidueData C)) =
        Finset.sum (insert 1 (insert 0 (insert (-1) zeros)))
          (certifiedPoleResidue x C.poles
            (completeCensusResidueData C)) := by
    exact congrArg
      (fun S => Finset.sum S
        (certifiedPoleResidue x C.poles (completeCensusResidueData C)))
      (completeCensus_poles_eq_insert_union C)
  rw [hPoleSum]
  rw [Finset.sum_insert hOneNot, Finset.sum_insert hZeroNot,
    Finset.sum_insert hNegOneNot]
  rw [certifiedPoleResidue_of_mem x C.poles
    (completeCensusResidueData C) (one_mem_completeCensus_poles C)]
  rw [hMain]
  have hExceptionalExpanded :
      certifiedPoleResidue x C.poles (completeCensusResidueData C) 0 +
          certifiedPoleResidue x C.poles (completeCensusResidueData C) (-1) =
        TS293.Goldbach.exceptionalResidueContribution
          C.exceptional.inventory := by
    rw [<- hExceptional]
    rw [C.exceptional.poles_eq]
    simp [TS306.Goldbach.perronExceptionalPoles]
  dsimp [zeros]
  rw [hZeroSum]
  linear_combination hAccounting + hExceptionalExpanded

theorem completeCensus_regular_on_closedRectangle
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D)
    (z : Complex)
    (hz : Membership.mem
      (Complex.reProdIm
        (Set.uIcc D.left D.right) (Set.uIcc (-D.tau) D.tau)) z)
    (hzNot : Not (Membership.mem C.poles z)) :
    AnalyticAt Complex
      (TS293.Goldbach.triangleSplinePerronIntegrand x) z := by
  rw [Complex.mem_reProdIm] at hz
  have hLR : D.left <= z.re /\ z.re <= D.right := by
    simpa [Set.uIcc_of_le
      (le_trans (le_of_lt D.left_lt_neg_one)
        (le_trans (by norm_num) (le_of_lt D.one_lt_right)))] using hz.1
  have hTauOrder : -D.tau <= D.tau := by
    linarith [D.tau_pos]
  have hBT : -D.tau <= z.im /\ z.im <= D.tau := by
    simpa [Set.uIcc_of_le hTauOrder] using hz.2
  by_cases hLeft : z.re = D.left
  · have hzEq : z =
        (D.left : Complex) + (z.im : Complex) * I := by
      apply Complex.ext
      · simpa using hLeft
      · simp
    rw [hzEq]
    exact C.boundary_analytic.left z.im hBT.1 hBT.2
  by_cases hRight : z.re = D.right
  · have hzEq : z =
        (D.right : Complex) + (z.im : Complex) * I := by
      apply Complex.ext
      · simpa using hRight
      · simp
    rw [hzEq]
    exact C.boundary_analytic.right z.im hBT.1 hBT.2
  by_cases hBottom : z.im = -D.tau
  · have hzEq : z =
        (z.re : Complex) - (D.tau : Complex) * I := by
      apply Complex.ext
      · simp
      · simpa using hBottom
    rw [hzEq]
    exact C.boundary_analytic.bottom z.re hLR.1 hLR.2
  by_cases hTop : z.im = D.tau
  · have hzEq : z =
        (z.re : Complex) + (D.tau : Complex) * I := by
      apply Complex.ext
      · simp
      · simpa using hTop
    rw [hzEq]
    exact C.boundary_analytic.top z.re hLR.1 hLR.2
  exact C.regular_off_census z
    (And.intro (lt_of_le_of_ne hLR.1 (Ne.symm hLeft))
      (And.intro (lt_of_le_of_ne hLR.2 hRight)
        (And.intro (lt_of_le_of_ne hBT.1 (Ne.symm hBottom))
          (lt_of_le_of_ne hBT.2 hTop)))) hzNot

set_option maxHeartbeats 1200000 in
theorem completeCensus_rectangleBoundaryIntegral_eq
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    rectangleBoundaryIntegral
        (TS293.Goldbach.triangleSplinePerronIntegrand x)
        D.left D.right (-D.tau) D.tau =
      (2 * Real.pi * I) *
        ((x : Complex) / 2 -
          TS293.Goldbach.realHeightZeroContribution x D.tau +
            TS293.Goldbach.exceptionalResidueContribution
              C.exceptional.inventory) := by
  rw [finite_simple_pole_rectangle_residue_theorem
    x C.poles (completeCensusResidueData C)
    D.left D.right (-D.tau) D.tau]
  · rw [completeCensusResidueSum_eq_accounting C]
  · linarith [D.left_lt_neg_one, D.one_lt_right]
  · linarith [D.tau_pos]
  · intro p hp
    exact C.all_poles_inside p hp
  · intro z hz hzNot
    exact completeCensus_regular_on_closedRectangle C z hz hzNot

set_option maxHeartbeats 800000 in
theorem perronRectangleBoundaryIntegral_eq_rectangleBoundaryIntegral
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle) :
    TS293.Goldbach.perronRectangleBoundaryIntegral x D =
      rectangleBoundaryIntegral
        (TS293.Goldbach.triangleSplinePerronIntegrand x)
        D.left D.right (-D.tau) D.tau := by
  unfold TS293.Goldbach.perronRectangleBoundaryIntegral
    TS293.Goldbach.perronNonRightBoundaryIntegral
    TS293.Goldbach.perronBottomIntegral
    TS293.Goldbach.perronTopForwardIntegral
    TS293.Goldbach.perronRightIntegral
    TS293.Goldbach.perronLeftForwardIntegral
    rectangleBoundaryIntegral
  simp only [Complex.ofReal_neg, neg_mul]
  have hBottom :
      intervalIntegral
          (fun sigma : Real => TS293.Goldbach.triangleSplinePerronIntegrand x
            ((sigma : Complex) + -((D.tau : Complex) * I)))
          D.left D.right volume =
        intervalIntegral
          (fun sigma : Real => TS293.Goldbach.triangleSplinePerronIntegrand x
            ((sigma : Complex) - (D.tau : Complex) * I))
          D.left D.right volume := by
    apply intervalIntegral.integral_congr
    intro sigma hs
    change TS293.Goldbach.triangleSplinePerronIntegrand x
        ((sigma : Complex) + -((D.tau : Complex) * I)) =
      TS293.Goldbach.triangleSplinePerronIntegrand x
        ((sigma : Complex) - (D.tau : Complex) * I)
    rw [sub_eq_add_neg]
  rw [hBottom]
  ring

theorem completeCensus_perronRectangleBoundaryIntegral_eq
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    TS293.Goldbach.perronRectangleBoundaryIntegral
        x D.toPerronRectangle =
      (2 * Real.pi * I) *
        ((x : Complex) / 2 -
          TS293.Goldbach.realHeightZeroContribution x D.tau +
            TS293.Goldbach.exceptionalResidueContribution
              C.exceptional.inventory) := by
  rw [perronRectangleBoundaryIntegral_eq_rectangleBoundaryIntegral]
  exact completeCensus_rectangleBoundaryIntegral_eq C

theorem normalizedPerronRectangleBoundary_eq_normalize
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle) :
    TS293.Goldbach.normalizedPerronRectangleBoundary x D =
      TS293.Goldbach.normalizeContourIntegral
        (TS293.Goldbach.perronRectangleBoundaryIntegral x D) := by
  unfold TS293.Goldbach.normalizedPerronRectangleBoundary
    TS293.Goldbach.finitePerronRightValue
    TS293.Goldbach.normalizedNonRightBoundary
    TS293.Goldbach.normalizeContourIntegral
    TS293.Goldbach.perronRectangleBoundaryIntegral
  ring

theorem completeCensus_normalizedPerronRectangleBoundary_eq
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    TS293.Goldbach.normalizedPerronRectangleBoundary
        x D.toPerronRectangle =
      (x : Complex) / 2 -
        TS293.Goldbach.realHeightZeroContribution x D.tau +
          TS293.Goldbach.exceptionalResidueContribution
            C.exceptional.inventory := by
  rw [normalizedPerronRectangleBoundary_eq_normalize]
  rw [completeCensus_perronRectangleBoundaryIntegral_eq C]
  unfold TS293.Goldbach.normalizeContourIntegral
  have hPi : Not (((Real.pi : Real) : Complex) = 0) := by
    exact_mod_cast Real.pi_ne_zero
  have hK : Not ((2 * Real.pi * I : Complex) = 0) := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hPi) Complex.I_ne_zero
  have hDen : (((2 * Real.pi : Real) : Complex) * I) =
      (2 * Real.pi * I : Complex) := by
    norm_num
  rw [hDen]
  exact mul_div_cancel_left₀ _ hK

theorem completeCensus_triangleSplineRectangleResidueStatement
    {x T : Nat}
    {D : TS294.Goldbach.QuantitativelyCleanPerronContourData T}
    (C : TS308.Goldbach.CompletePerronResidueCensus x T D) :
    TS293.Goldbach.TriangleSplineRectangleResidueStatement
      x T D.toCleanPerronContourData C.exceptional.inventory := by
  exact completeCensus_normalizedPerronRectangleBoundary_eq C

theorem canonical_triangleSplineRectangleResidueStatement
    (x T : Nat)
    (hx : 0 < x)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    TS293.Goldbach.TriangleSplineRectangleResidueStatement
      x T D.toCleanPerronContourData
        (TS308.Goldbach.completePerronResidueCensus x T hx D).exceptional.inventory :=
  completeCensus_triangleSplineRectangleResidueStatement
    (TS308.Goldbach.completePerronResidueCensus x T hx D)

/-! ## Fail-closed ledger -/

structure MeromorphicRectangleResidueLedger where
  rectangle_boundary_cauchy_reduction_proved : True
  simple_pole_kernel_integral_proved : True
  finite_principal_part_regularization_proved : True
  generic_finite_simple_pole_residue_theorem_proved : True
  ts308_census_instantiated : True
  exact_residue_accounting_reused : True
  ts293_rectangle_residue_statement_proved : True
  perron_inversion_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def meromorphicRectangleResidueLedger :
    MeromorphicRectangleResidueLedger where
  rectangle_boundary_cauchy_reduction_proved := True.intro
  simple_pole_kernel_integral_proved := True.intro
  finite_principal_part_regularization_proved := True.intro
  generic_finite_simple_pole_residue_theorem_proved := True.intro
  ts308_census_instantiated := True.intro
  exact_residue_accounting_reused := True.intro
  ts293_rectangle_residue_statement_proved := True.intro
  perron_inversion_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS309
