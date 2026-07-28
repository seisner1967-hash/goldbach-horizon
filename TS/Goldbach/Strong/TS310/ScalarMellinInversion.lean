import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic
import TS.Goldbach.Strong.TS309.MeromorphicRectangleResidueTheorem

/-!
# TS310 - Scalar Mellin inversion

This file proves the scalar inversion formula for `y^s / (s * (s + 1))` on
every vertical line `re(s) = c` with `1 < c`. The proof uses finite rectangles,
the elementary simple-pole rectangle integral from TS309, and ordered limits.

The cases `y > 1`, `0 < y < 1`, and `y = 1` are kept separate. In particular,
the endpoint case keeps the quadratic kernel intact, so every full-line
Lebesgue integral remains absolutely integrable.
-/

noncomputable section

namespace TS310
namespace Goldbach

open Complex Filter MeasureTheory Metric Set
open scoped BigOperators Interval

noncomputable def scalarMellinIntegrand (y : Real) (z : Complex) : Complex :=
  (y : Complex) ^ z / (z * (z + 1))

noncomputable def scalarMellinZeroNumerator (y : Real) (z : Complex) : Complex :=
  (y : Complex) ^ z / (z + 1)

noncomputable def scalarMellinNegOneNumerator (y : Real) (z : Complex) : Complex :=
  (y : Complex) ^ z / z

theorem realCpow_analyticAt
    {y : Real} (hy : 0 < y) (z : Complex) :
    AnalyticAt Complex (fun w : Complex => (y : Complex) ^ w) z := by
  have hyC : Not ((y : Complex) = 0) := by exact_mod_cast ne_of_gt hy
  letI : NeZero (y : Complex) := { out := hyC }
  exact
    (differentiable_const_cpow_of_neZero (y : Complex)).differentiableOn.analyticAt
      univ_mem

theorem scalarMellinZeroNumerator_analyticAt
    {y : Real} (hy : 0 < y) :
    AnalyticAt Complex (scalarMellinZeroNumerator y) 0 := by
  unfold scalarMellinZeroNumerator
  exact (realCpow_analyticAt hy 0).div
    (analyticAt_id.add analyticAt_const) (by norm_num)

theorem scalarMellinNegOneNumerator_analyticAt
    {y : Real} (hy : 0 < y) :
    AnalyticAt Complex (scalarMellinNegOneNumerator y) (-1) := by
  unfold scalarMellinNegOneNumerator
  exact (realCpow_analyticAt hy (-1)).div analyticAt_id (by norm_num)

theorem scalarMellinIntegrand_eq_zeroNumerator_div
    (y : Real) (z : Complex) :
    scalarMellinIntegrand y z = scalarMellinZeroNumerator y z / z := by
  unfold scalarMellinIntegrand scalarMellinZeroNumerator
  simp only [div_eq_mul_inv]
  rw [mul_comm z (z + 1), mul_inv]
  ring

theorem scalarMellinIntegrand_eq_negOneNumerator_div
    (y : Real) (z : Complex) :
    scalarMellinIntegrand y z = scalarMellinNegOneNumerator y z / (z + 1) := by
  unfold scalarMellinIntegrand scalarMellinNegOneNumerator
  by_cases hz : z = 0
  . subst z
    simp [scalarMellinIntegrand, scalarMellinNegOneNumerator]
  . by_cases hzp : z + 1 = 0
    . simp [scalarMellinIntegrand, scalarMellinNegOneNumerator, hzp]
    . field_simp [hz, hzp]

theorem scalarMellinZeroNumerator_at_zero
    {y : Real} (_hy : 0 < y) :
    scalarMellinZeroNumerator y 0 = 1 := by
  unfold scalarMellinZeroNumerator
  rw [Complex.cpow_zero]
  norm_num

theorem scalarMellinNegOneNumerator_at_neg_one
    {y : Real} (_hy : 0 < y) :
    scalarMellinNegOneNumerator y (-1) = -(y : Complex) ^ (-1 : Complex) := by
  unfold scalarMellinNegOneNumerator
  ring

noncomputable def scalarMellinRegularization (y : Real) (z : Complex) : Complex :=
  if z = 0 then
    deriv (scalarMellinZeroNumerator y) 0 + (y : Complex) ^ (-1 : Complex)
  else if z = -1 then
    deriv (scalarMellinNegOneNumerator y) (-1) + 1
  else
    scalarMellinIntegrand y z - TS309.Goldbach.simplePoleKernel 0 z +
      (y : Complex) ^ (-1 : Complex) * TS309.Goldbach.simplePoleKernel (-1) z

theorem scalarMellinRegularization_analyticAt_zero
    {y : Real} (hy : 0 < y) :
    AnalyticAt Complex (scalarMellinRegularization y) 0 := by
  let H := scalarMellinZeroNumerator y
  let q : Complex := (y : Complex) ^ (-1 : Complex)
  have hH : AnalyticAt Complex H 0 := scalarMellinZeroNumerator_analyticAt hy
  have hEq :
      scalarMellinRegularization y =ᶠ[nhds 0]
        fun z => dslope H 0 z + q * TS309.Goldbach.simplePoleKernel (-1) z := by
    filter_upwards [eventually_ne_nhds (show Not ((0 : Complex) = -1) by norm_num)]
      with z hz
    by_cases hz0 : z = 0
    . subst z
      simp [scalarMellinRegularization, H, q, dslope_same,
        TS309.Goldbach.simplePoleKernel]
    . rw [scalarMellinRegularization, if_neg hz0, if_neg hz]
      rw [scalarMellinIntegrand_eq_zeroNumerator_div]
      rw [TS309.Goldbach.simplePoleKernel, show (z - 0) = z by ring]
      rw [dslope_of_ne H hz0]
      unfold slope
      have hzm1 : Not (z + 1 = 0) := by
        intro h
        apply hz
        linear_combination h
      have hH0 : H 0 = 1 := scalarMellinZeroNumerator_at_zero hy
      rw [hH0]
      field_simp [hz0, hzm1]
  exact ((TS306.Goldbach.analyticAt_dslope hH).add
    (analyticAt_const.mul
      (TS309.Goldbach.simplePoleKernel_analyticAt (by norm_num)))).congr hEq.symm

theorem scalarMellinRegularization_analyticAt_neg_one
    {y : Real} (hy : 0 < y) :
    AnalyticAt Complex (scalarMellinRegularization y) (-1) := by
  let H := scalarMellinNegOneNumerator y
  let q : Complex := (y : Complex) ^ (-1 : Complex)
  have hH : AnalyticAt Complex H (-1) := scalarMellinNegOneNumerator_analyticAt hy
  have hEq :
      scalarMellinRegularization y =ᶠ[nhds (-1)]
        fun z => dslope H (-1) z - TS309.Goldbach.simplePoleKernel 0 z := by
    filter_upwards [eventually_ne_nhds (show Not ((-1 : Complex) = 0) by norm_num)]
      with z hz
    by_cases hzm1 : z = -1
    . subst z
      simp [scalarMellinRegularization, H, q, dslope_same,
        TS309.Goldbach.simplePoleKernel]
    . rw [scalarMellinRegularization, if_neg hz, if_neg hzm1]
      rw [scalarMellinIntegrand_eq_negOneNumerator_div]
      rw [TS309.Goldbach.simplePoleKernel]
      rw [dslope_of_ne H hzm1]
      unfold slope
      have hq : H (-1) = -q := scalarMellinNegOneNumerator_at_neg_one hy
      rw [hq]
      have hzadd : Not (z + 1 = 0) := by
        intro h
        apply hzm1
        linear_combination h
      unfold TS309.Goldbach.simplePoleKernel
      simp only [div_eq_mul_inv]
      simp only [vsub_eq_sub, smul_eq_mul]
      ring
  exact ((TS306.Goldbach.analyticAt_dslope hH).sub
    (TS309.Goldbach.simplePoleKernel_analyticAt (by norm_num))).congr hEq.symm

theorem scalarMellinRegularization_analyticAt_of_ne
    {y : Real} (hy : 0 < y) {z : Complex}
    (hz0 : Not (z = 0)) (hzm1 : Not (z = -1)) :
    AnalyticAt Complex (scalarMellinRegularization y) z := by
  have hEq : scalarMellinRegularization y =ᶠ[nhds z]
      fun w => scalarMellinIntegrand y w - TS309.Goldbach.simplePoleKernel 0 w +
        (y : Complex) ^ (-1 : Complex) * TS309.Goldbach.simplePoleKernel (-1) w := by
    filter_upwards [eventually_ne_nhds hz0, eventually_ne_nhds hzm1]
      with w hw0 hwm1
    simp [scalarMellinRegularization, hw0, hwm1]
  have hInt : AnalyticAt Complex (scalarMellinIntegrand y) z := by
    unfold scalarMellinIntegrand
    exact (realCpow_analyticAt hy z).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const))
      (mul_ne_zero hz0 (by
        intro h
        apply hzm1
        linear_combination h))
  exact ((hInt.sub (TS309.Goldbach.simplePoleKernel_analyticAt hz0)).add
    (analyticAt_const.mul
      (TS309.Goldbach.simplePoleKernel_analyticAt hzm1))).congr hEq.symm

theorem scalarMellinIntegrand_analyticAt_of_ne
    {y : Real} (hy : 0 < y) {z : Complex}
    (hz0 : Not (z = 0)) (hzm1 : Not (z = -1)) :
    AnalyticAt Complex (scalarMellinIntegrand y) z := by
  unfold scalarMellinIntegrand
  exact (realCpow_analyticAt hy z).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const))
    (mul_ne_zero hz0 (by
      intro h
      apply hzm1
      linear_combination h))

structure RectangleBoundaryAnalyticData
    (f : Complex -> Complex) (a b c d : Real) : Prop where
  bottom : forall x : Real, Membership.mem (Set.uIcc a b) x ->
    AnalyticAt Complex f ((x : Complex) + (c : Complex) * I)
  top : forall x : Real, Membership.mem (Set.uIcc a b) x ->
    AnalyticAt Complex f ((x : Complex) + (d : Complex) * I)
  right : forall y : Real, Membership.mem (Set.uIcc c d) y ->
    AnalyticAt Complex f ((b : Complex) + (y : Complex) * I)
  left : forall y : Real, Membership.mem (Set.uIcc c d) y ->
    AnalyticAt Complex f ((a : Complex) + (y : Complex) * I)

theorem rectangleBoundaryIntegral_sub_add_of_analytic
    (f g h : Complex -> Complex) (a b c d : Real)
    (hf : RectangleBoundaryAnalyticData f a b c d)
    (hg : RectangleBoundaryAnalyticData g a b c d)
    (hh : RectangleBoundaryAnalyticData h a b c d) :
    TS309.Goldbach.rectangleBoundaryIntegral (fun z => f z - g z + h z) a b c d =
      TS309.Goldbach.rectangleBoundaryIntegral f a b c d -
        TS309.Goldbach.rectangleBoundaryIntegral g a b c d +
          TS309.Goldbach.rectangleBoundaryIntegral h a b c d := by
  have hfB := TS309.Goldbach.horizontal_intervalIntegrable_of_analyticAt_on
    f c a b hf.bottom
  have hgB := TS309.Goldbach.horizontal_intervalIntegrable_of_analyticAt_on
    g c a b hg.bottom
  have hhB := TS309.Goldbach.horizontal_intervalIntegrable_of_analyticAt_on
    h c a b hh.bottom
  have hfT := TS309.Goldbach.horizontal_intervalIntegrable_of_analyticAt_on
    f d a b hf.top
  have hgT := TS309.Goldbach.horizontal_intervalIntegrable_of_analyticAt_on
    g d a b hg.top
  have hhT := TS309.Goldbach.horizontal_intervalIntegrable_of_analyticAt_on
    h d a b hh.top
  have hfR := TS309.Goldbach.vertical_intervalIntegrable_of_analyticAt_on
    f b c d hf.right
  have hgR := TS309.Goldbach.vertical_intervalIntegrable_of_analyticAt_on
    g b c d hg.right
  have hhR := TS309.Goldbach.vertical_intervalIntegrable_of_analyticAt_on
    h b c d hh.right
  have hfL := TS309.Goldbach.vertical_intervalIntegrable_of_analyticAt_on
    f a c d hf.left
  have hgL := TS309.Goldbach.vertical_intervalIntegrable_of_analyticAt_on
    g a c d hg.left
  have hhL := TS309.Goldbach.vertical_intervalIntegrable_of_analyticAt_on
    h a c d hh.left
  rw [TS309.Goldbach.rectangleBoundaryIntegral_add
    (fun z => f z - g z) h a b c d
    (hfB.sub hgB) hhB (hfT.sub hgT) hhT
    (hfR.sub hgR) hhR (hfL.sub hgL) hhL]
  rw [TS309.Goldbach.rectangleBoundaryIntegral_sub
    f g a b c d hfB hgB hfT hgT hfR hgR hfL hgL]

theorem scalarMellinIntegrand_boundaryAnalyticData
    {y : Real} (hy : 0 < y) {a b c d : Real}
    (ha : a < -1) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    RectangleBoundaryAnalyticData (scalarMellinIntegrand y) a b c d := by
  constructor
  . intro x hx
    apply scalarMellinIntegrand_analyticAt_of_ne hy
    . intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    . intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  . intro x hx
    apply scalarMellinIntegrand_analyticAt_of_ne hy
    . intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    . intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  . intro t ht
    apply scalarMellinIntegrand_analyticAt_of_ne hy
    . intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    . intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
  . intro t ht
    apply scalarMellinIntegrand_analyticAt_of_ne hy
    . intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    . intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith

theorem simplePoleBoundaryAnalyticData
    (p : Complex) {a b c d : Real}
    (hBottom : Not (c = p.im))
    (hTop : Not (d = p.im))
    (hRight : Not (b = p.re))
    (hLeft : Not (a = p.re)) :
    RectangleBoundaryAnalyticData (TS309.Goldbach.simplePoleKernel p) a b c d := by
  constructor
  . intro x hx
    apply TS309.Goldbach.simplePoleKernel_analyticAt
    intro h
    have him := congrArg Complex.im h
    exact hBottom (by simpa using him)
  . intro x hx
    apply TS309.Goldbach.simplePoleKernel_analyticAt
    intro h
    have him := congrArg Complex.im h
    exact hTop (by simpa using him)
  . intro y hy
    apply TS309.Goldbach.simplePoleKernel_analyticAt
    intro h
    have hre := congrArg Complex.re h
    exact hRight (by simpa using hre)
  . intro y hy
    apply TS309.Goldbach.simplePoleKernel_analyticAt
    intro h
    have hre := congrArg Complex.re h
    exact hLeft (by simpa using hre)

set_option maxHeartbeats 800000 in
theorem scalarMellinIntegrand_rectangleBoundaryIntegral
    {y : Real} (hy : 0 < y) {a b c d : Real}
    (ha : a < -1) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    TS309.Goldbach.rectangleBoundaryIntegral (scalarMellinIntegrand y) a b c d =
      (2 * Real.pi * I) * (1 - (y : Complex) ^ (-1 : Complex)) := by
  let f := scalarMellinIntegrand y
  let k0 := TS309.Goldbach.simplePoleKernel 0
  let km1 := TS309.Goldbach.simplePoleKernel (-1)
  let q : Complex := (y : Complex) ^ (-1 : Complex)
  let h : Complex -> Complex := fun z => q * km1 z
  have hRegAnalytic : forall z : Complex,
      AnalyticAt Complex (scalarMellinRegularization y) z := by
    intro z
    by_cases hz0 : z = 0
    . subst z
      exact scalarMellinRegularization_analyticAt_zero hy
    . by_cases hzm1 : z = -1
      . subst z
        exact scalarMellinRegularization_analyticAt_neg_one hy
      . exact scalarMellinRegularization_analyticAt_of_ne hy hz0 hzm1
  have hRegZero :
      TS309.Goldbach.rectangleBoundaryIntegral
        (scalarMellinRegularization y) a b c d = 0 := by
    apply TS309.Goldbach.rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    intro z hz
    exact (hRegAnalytic z).differentiableAt.differentiableWithinAt
  have hf : RectangleBoundaryAnalyticData f a b c d :=
    scalarMellinIntegrand_boundaryAnalyticData hy ha hb hc hd
  have hk0 : RectangleBoundaryAnalyticData k0 a b c d := by
    apply simplePoleBoundaryAnalyticData
    all_goals simp <;> linarith
  have hkm1 : RectangleBoundaryAnalyticData km1 a b c d := by
    apply simplePoleBoundaryAnalyticData
    all_goals simp <;> linarith
  have hh : RectangleBoundaryAnalyticData h a b c d := by
    exact {
      bottom := fun x hx => analyticAt_const.mul (hkm1.bottom x hx)
      top := fun x hx => analyticAt_const.mul (hkm1.top x hx)
      right := fun t ht => analyticAt_const.mul (hkm1.right t ht)
      left := fun t ht => analyticAt_const.mul (hkm1.left t ht) }
  have hRegEq {z : Complex} (hz0 : Not (z = 0)) (hzm1 : Not (z = -1)) :
      scalarMellinRegularization y z = f z - k0 z + h z := by
    simp [scalarMellinRegularization, hz0, hzm1, f, k0, h]
  have hBoundaryCongr :
      TS309.Goldbach.rectangleBoundaryIntegral
          (scalarMellinRegularization y) a b c d =
        TS309.Goldbach.rectangleBoundaryIntegral
          (fun z => f z - k0 z + h z) a b c d := by
    apply TS309.Goldbach.rectangleBoundaryIntegral_congr
    . intro u
      apply hRegEq
      . intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
      . intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
    . intro u
      apply hRegEq
      . intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
      . intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
    . intro u
      apply hRegEq
      . intro hz
        have hre := congrArg Complex.re hz
        simp at hre
        linarith
      . intro hz
        have hre := congrArg Complex.re hz
        simp at hre
        linarith
    . intro u
      apply hRegEq
      . intro hz
        have hre := congrArg Complex.re hz
        simp at hre
        linarith
      . intro hz
        have hre := congrArg Complex.re hz
        simp at hre
        linarith
  have hLinear := rectangleBoundaryIntegral_sub_add_of_analytic
    f k0 h a b c d hf hk0 hh
  have hk0Value :
      TS309.Goldbach.rectangleBoundaryIntegral k0 a b c d = 2 * Real.pi * I := by
    exact TS309.Goldbach.simplePoleKernel_rectangleBoundaryIntegral
      (0 : Complex) a b c d (by simpa using ha.trans (by norm_num : (-1 : Real) < 0))
        (by simpa using hb) (by simpa using hc) (by simpa using hd)
  have hkm1Value :
      TS309.Goldbach.rectangleBoundaryIntegral km1 a b c d = 2 * Real.pi * I := by
    exact TS309.Goldbach.simplePoleKernel_rectangleBoundaryIntegral
      (-1 : Complex) a b c d (by simpa using ha)
        (by simpa using lt_trans (by norm_num : (-1 : Real) < 0) hb)
        (by simpa using hc) (by simpa using hd)
  have hhValue :
      TS309.Goldbach.rectangleBoundaryIntegral h a b c d =
        q * (2 * Real.pi * I) := by
    rw [show h = fun z => q * km1 z by rfl,
      TS309.Goldbach.rectangleBoundaryIntegral_const_mul, hkm1Value]
  rw [hBoundaryCongr, hLinear, hk0Value, hhValue] at hRegZero
  dsimp [f, q] at hRegZero
  linear_combination hRegZero

noncomputable def scalarMellinVerticalIntegrand
    (y sigma t : Real) : Complex :=
  scalarMellinIntegrand y ((sigma : Complex) + (t : Complex) * I)

theorem norm_real_cpow_vertical
    {y : Real} (hy : 0 < y) (sigma t : Real) :
    norm ((y : Complex) ^ ((sigma : Complex) + (t : Complex) * I)) =
      y ^ sigma := by
  rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hy]
  simp

theorem vertical_point_norm_sq
    (sigma t : Real) :
    norm ((sigma : Complex) + (t : Complex) * I) ^ 2 = sigma ^ 2 + t ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem vertical_point_add_one_norm_sq
    (sigma t : Real) :
    norm (((sigma : Complex) + (t : Complex) * I) + 1) ^ 2 =
      (sigma + 1) ^ 2 + t ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem one_add_sq_le_vertical_denominator_norm_of_one_le
    {sigma t : Real} (hsigma : 1 <= sigma) :
    1 + t ^ 2 <=
      norm ((sigma : Complex) + (t : Complex) * I) *
        norm (((sigma : Complex) + (t : Complex) * I) + 1) := by
  have h0 := norm_nonneg ((sigma : Complex) + (t : Complex) * I)
  have h1 := norm_nonneg (((sigma : Complex) + (t : Complex) * I) + 1)
  have hs0 := vertical_point_norm_sq sigma t
  have hs1 := vertical_point_add_one_norm_sq sigma t
  have hLower0 : 1 + t ^ 2 <=
      norm ((sigma : Complex) + (t : Complex) * I) ^ 2 := by
    nlinarith [sq_nonneg (sigma - 1)]
  have hle :
      norm ((sigma : Complex) + (t : Complex) * I) <=
        norm (((sigma : Complex) + (t : Complex) * I) + 1) := by
    nlinarith
  nlinarith

theorem one_add_sq_le_vertical_denominator_norm_left
    {A t : Real} (hA : 2 <= A) :
    1 + t ^ 2 <=
      norm ((-A : Complex) + (t : Complex) * I) *
        norm (((-A : Complex) + (t : Complex) * I) + 1) := by
  have h0 := norm_nonneg ((-A : Complex) + (t : Complex) * I)
  have h1 := norm_nonneg (((-A : Complex) + (t : Complex) * I) + 1)
  have hs0 := vertical_point_norm_sq (-A) t
  have hs1 := vertical_point_add_one_norm_sq (-A) t
  have hs0' : norm ((-A : Complex) + (t : Complex) * I) ^ 2 =
      A ^ 2 + t ^ 2 := by
    simpa using hs0
  have hs1' : norm (((-A : Complex) + (t : Complex) * I) + 1) ^ 2 =
      (A - 1) ^ 2 + t ^ 2 := by
    rw [<- Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hLower1 : 1 + t ^ 2 <=
      norm (((-A : Complex) + (t : Complex) * I) + 1) ^ 2 := by
    rw [hs1']
    have hsq : 1 <= (A - 1) ^ 2 := by
      nlinarith [sq_nonneg (A - 2)]
    nlinarith
  have hle :
      norm (((-A : Complex) + (t : Complex) * I) + 1) <=
        norm ((-A : Complex) + (t : Complex) * I) := by
    have hsqle :
        norm (((-A : Complex) + (t : Complex) * I) + 1) ^ 2 <=
          norm ((-A : Complex) + (t : Complex) * I) ^ 2 := by
      rw [hs0', hs1']
      nlinarith
    nlinarith [sq_nonneg
      (norm ((-A : Complex) + (t : Complex) * I) -
        norm (((-A : Complex) + (t : Complex) * I) + 1))]
  nlinarith

theorem scalarMellinVerticalIntegrand_norm_le_right
    {y sigma : Real} (hy : 0 < y) (hsigma : 1 <= sigma) (t : Real) :
    norm (scalarMellinVerticalIntegrand y sigma t) <=
      y ^ sigma * (1 / (1 + t ^ 2)) := by
  unfold scalarMellinVerticalIntegrand scalarMellinIntegrand
  rw [norm_div, norm_mul, norm_real_cpow_vertical hy]
  have hbase : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hprod := one_add_sq_le_vertical_denominator_norm_of_one_le
    (sigma := sigma) (t := t) hsigma
  have hden : 0 <
      norm ((sigma : Complex) + (t : Complex) * I) *
        norm (((sigma : Complex) + (t : Complex) * I) + 1) :=
    hbase.trans_le hprod
  exact mul_le_mul_of_nonneg_left
    (by simpa [one_div] using one_div_le_one_div_of_le hbase hprod)
    (Real.rpow_nonneg hy.le _)

theorem scalarMellinVerticalIntegrand_norm_le_left
    {y A : Real} (hy : 0 < y) (hA : 2 <= A) (t : Real) :
    norm (scalarMellinVerticalIntegrand y (-A) t) <=
      y ^ (-A) * (1 / (1 + t ^ 2)) := by
  unfold scalarMellinVerticalIntegrand scalarMellinIntegrand
  rw [norm_div, norm_mul, norm_real_cpow_vertical hy]
  have hbase : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hprod := one_add_sq_le_vertical_denominator_norm_left
    (A := A) (t := t) hA
  exact mul_le_mul_of_nonneg_left
    (by simpa [one_div] using one_div_le_one_div_of_le hbase hprod)
    (Real.rpow_nonneg hy.le _)

theorem continuous_scalarMellinVerticalIntegrand
    {y sigma : Real} (hy : 0 < y)
    (hs0 : Not (sigma = 0)) (hsm1 : Not (sigma = -1)) :
    Continuous (scalarMellinVerticalIntegrand y sigma) := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : Real -> Complex := fun u => (sigma : Complex) + (u : Complex) * I
  have hz : ContinuousAt z t := by dsimp [z]; fun_prop
  have hAnalytic : AnalyticAt Complex (scalarMellinIntegrand y) (z t) := by
    apply scalarMellinIntegrand_analyticAt_of_ne hy
    . intro h
      have hre := congrArg Complex.re h
      simp [z] at hre
      exact hs0 hre
    . intro h
      have hre := congrArg Complex.re h
      simp [z] at hre
      exact hsm1 hre
  exact hAnalytic.continuousAt.comp_of_eq hz rfl

theorem integrable_scalarMellinVerticalIntegrand_right
    {y sigma : Real} (hy : 0 < y) (hsigma : 1 <= sigma) :
    Integrable (scalarMellinVerticalIntegrand y sigma) := by
  have hmajorant : Integrable
      (fun t : Real => y ^ sigma * (1 / (1 + t ^ 2))) := by
    simpa [one_div] using integrable_inv_one_add_sq.const_mul (y ^ sigma)
  exact hmajorant.mono'
    (continuous_scalarMellinVerticalIntegrand hy (by linarith) (by linarith)).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (scalarMellinVerticalIntegrand_norm_le_right hy hsigma))

theorem integrable_scalarMellinVerticalIntegrand_left
    {y A : Real} (hy : 0 < y) (hA : 2 <= A) :
    Integrable (scalarMellinVerticalIntegrand y (-A)) := by
  have hmajorant : Integrable
      (fun t : Real => y ^ (-A) * (1 / (1 + t ^ 2))) := by
    simpa [one_div] using integrable_inv_one_add_sq.const_mul (y ^ (-A))
  exact hmajorant.mono'
    (continuous_scalarMellinVerticalIntegrand hy (by linarith) (by linarith)).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (scalarMellinVerticalIntegrand_norm_le_left hy hA))

noncomputable def scalarCauchyMass : Real :=
  integral (volume : Measure Real) (fun t : Real => 1 / (1 + t ^ 2))

theorem scalarCauchyMass_nonnegative : 0 <= scalarCauchyMass := by
  unfold scalarCauchyMass
  exact integral_nonneg (fun t => by positivity)

theorem scalarMellinVerticalIntegral_norm_le_left
    {y A : Real} (hy : 0 < y) (hA : 2 <= A) :
    norm (integral (volume : Measure Real)
      (scalarMellinVerticalIntegrand y (-A))) <=
      y ^ (-A) * scalarCauchyMass := by
  unfold scalarCauchyMass
  have hmajorant : Integrable
      (fun t : Real => y ^ (-A) * (1 / (1 + t ^ 2))) := by
    simpa [one_div] using integrable_inv_one_add_sq.const_mul (y ^ (-A))
  have h := norm_integral_le_of_norm_le hmajorant
    (Filter.Eventually.of_forall
      (scalarMellinVerticalIntegrand_norm_le_left hy hA))
  calc
    norm (integral (volume : Measure Real)
      (scalarMellinVerticalIntegrand y (-A))) <=
        integral (volume : Measure Real)
          (fun t : Real => y ^ (-A) * (1 / (1 + t ^ 2))) := h
    _ = y ^ (-A) * scalarCauchyMass := by
      unfold scalarCauchyMass
      change (integral (volume : Measure Real)
        (fun t : Real => y ^ (-A) • (1 / (1 + t ^ 2)))) = _
      rw [integral_smul]
      rfl

theorem real_rpow_le_endpoint_max
    {y a b sigma : Real} (hy : 0 < y) (hab : a <= b)
    (hsigma : Membership.mem (Set.uIcc a b) sigma) :
    y ^ sigma <= max (y ^ a) (y ^ b) := by
  rw [Set.uIcc_of_le hab] at hsigma
  rcases hsigma with ⟨ha, hb⟩
  by_cases hyOne : 1 <= y
  . exact (Real.rpow_le_rpow_of_exponent_le hyOne hb).trans (le_max_right _ _)
  . have hyLe : y <= 1 := le_of_not_ge hyOne
    exact (Real.rpow_le_rpow_of_exponent_ge hy hyLe ha).trans (le_max_left _ _)

theorem horizontal_denominator_norm_ge_sq
    (sigma T : Real) :
    T ^ 2 <=
      norm ((sigma : Complex) + (T : Complex) * I) *
        norm (((sigma : Complex) + (T : Complex) * I) + 1) := by
  have h0 := norm_nonneg ((sigma : Complex) + (T : Complex) * I)
  have h1 := norm_nonneg (((sigma : Complex) + (T : Complex) * I) + 1)
  have hs0 := vertical_point_norm_sq sigma T
  have hs1 := vertical_point_add_one_norm_sq sigma T
  have hT0 : T ^ 2 <= norm ((sigma : Complex) + (T : Complex) * I) ^ 2 := by
    nlinarith [sq_nonneg sigma]
  have hT1 : T ^ 2 <=
      norm (((sigma : Complex) + (T : Complex) * I) + 1) ^ 2 := by
    nlinarith [sq_nonneg (sigma + 1)]
  have hsq : (T ^ 2) ^ 2 <=
      (norm ((sigma : Complex) + (T : Complex) * I) *
        norm (((sigma : Complex) + (T : Complex) * I) + 1)) ^ 2 := by
    calc
      (T ^ 2) ^ 2 = (T ^ 2) * (T ^ 2) := by ring
      _ <= norm ((sigma : Complex) + (T : Complex) * I) ^ 2 *
          norm (((sigma : Complex) + (T : Complex) * I) + 1) ^ 2 :=
        mul_le_mul hT0 hT1 (sq_nonneg T) (sq_nonneg _)
      _ = (norm ((sigma : Complex) + (T : Complex) * I) *
          norm (((sigma : Complex) + (T : Complex) * I) + 1)) ^ 2 := by ring
  exact (sq_le_sq₀ (sq_nonneg T) (mul_nonneg h0 h1)).mp hsq

theorem scalarMellinHorizontalIntegrand_norm_le
    {y a b sigma T : Real} (hy : 0 < y) (hab : a <= b)
    (hT : Not (T = 0)) (hsigma : Membership.mem (Set.uIcc a b) sigma) :
    norm (scalarMellinIntegrand y
      ((sigma : Complex) + (T : Complex) * I)) <=
      max (y ^ a) (y ^ b) / T ^ 2 := by
  unfold scalarMellinIntegrand
  rw [norm_div, norm_mul, norm_real_cpow_vertical hy]
  have hT2 : 0 < T ^ 2 := sq_pos_of_ne_zero hT
  have hden := horizontal_denominator_norm_ge_sq sigma T
  have hprod : 0 <
      norm ((sigma : Complex) + (T : Complex) * I) *
        norm (((sigma : Complex) + (T : Complex) * I) + 1) :=
    hT2.trans_le hden
  calc
    y ^ sigma / (norm ((sigma : Complex) + (T : Complex) * I) *
        norm (((sigma : Complex) + (T : Complex) * I) + 1)) <=
      y ^ sigma / T ^ 2 := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hT2 hden
    _ <= max (y ^ a) (y ^ b) / T ^ 2 := by
      exact div_le_div_of_nonneg_right
        (real_rpow_le_endpoint_max hy hab hsigma) hT2.le

theorem scalarMellinHorizontalIntegral_norm_le
    {y a b T : Real} (hy : 0 < y) (hab : a <= b) (hT : Not (T = 0)) :
    norm (intervalIntegral
      (fun sigma : Real => scalarMellinIntegrand y
        ((sigma : Complex) + (T : Complex) * I))
      a b (volume : Measure Real)) <=
      (b - a) * (max (y ^ a) (y ^ b) / T ^ 2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun sigma hsigma =>
      scalarMellinHorizontalIntegrand_norm_le hy hab hT
        (uIoc_subset_uIcc hsigma))
  have habs : |b - a| = b - a := _root_.abs_of_nonneg (sub_nonneg.mpr hab)
  calc
    norm (intervalIntegral
      (fun sigma : Real => scalarMellinIntegrand y
        ((sigma : Complex) + (T : Complex) * I))
      a b (volume : Measure Real)) <=
        (max (y ^ a) (y ^ b) / T ^ 2) * |b - a| := h
    _ = (b - a) * (max (y ^ a) (y ^ b) / T ^ 2) := by
      rw [habs]
      ring

theorem scalarMellinHorizontalIntegral_tendsto_zero
    {y a b : Real} (hy : 0 < y) (hab : a <= b) :
    Tendsto
      (fun T : Real => intervalIntegral
        (fun sigma : Real => scalarMellinIntegrand y
          ((sigma : Complex) + (T : Complex) * I))
        a b (volume : Measure Real))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hInvSq : Tendsto (fun T : Real => 1 / T ^ 2) atTop (nhds 0) := by
    have hInv : Tendsto (fun T : Real => T⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hInv.mul hInv
    simpa [one_div, pow_two] using h
  have hBound : Tendsto
      (fun T : Real => (b - a) * (max (y ^ a) (y ^ b) / T ^ 2))
      atTop (nhds 0) := by
    let C : Real := (b - a) * max (y ^ a) (y ^ b)
    have hCont : ContinuousAt (fun u : Real => C * u) 0 :=
      by fun_prop
    have hMul := hCont.tendsto.comp hInvSq
    simpa [C, div_eq_mul_inv, mul_assoc] using hMul
  refine squeeze_zero'
    (f := fun T : Real => norm (intervalIntegral
      (fun sigma : Real => scalarMellinIntegrand y
        ((sigma : Complex) + (T : Complex) * I))
      a b (volume : Measure Real)))
    (g := fun T : Real => (b - a) * (max (y ^ a) (y ^ b) / T ^ 2))
    (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hBound
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  exact scalarMellinHorizontalIntegral_norm_le hy hab hT.ne'

set_option maxHeartbeats 500000 in
theorem scalarMellinHorizontalIntegral_bottom_tendsto_zero
    {y a b : Real} (hy : 0 < y) (hab : a <= b) :
    Tendsto
      (fun T : Real => intervalIntegral
        (fun sigma : Real => scalarMellinIntegrand y
          ((sigma : Complex) - (T : Complex) * I))
        a b (volume : Measure Real))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hInvSq : Tendsto (fun T : Real => 1 / T ^ 2) atTop (nhds 0) := by
    have hInv : Tendsto (fun T : Real => T⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h := hInv.mul hInv
    simpa [one_div, pow_two] using h
  have hBound : Tendsto
      (fun T : Real => (b - a) * (max (y ^ a) (y ^ b) / T ^ 2))
      atTop (nhds 0) := by
    let C : Real := (b - a) * max (y ^ a) (y ^ b)
    have hCont : ContinuousAt (fun u : Real => C * u) 0 :=
      by fun_prop
    have hMul := hCont.tendsto.comp hInvSq
    simpa [C, div_eq_mul_inv, mul_assoc] using hMul
  refine squeeze_zero'
    (f := fun T : Real => norm (intervalIntegral
      (fun sigma : Real => scalarMellinIntegrand y
        ((sigma : Complex) - (T : Complex) * I))
      a b (volume : Measure Real)))
    (g := fun T : Real => (b - a) * (max (y ^ a) (y ^ b) / T ^ 2))
    (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hBound
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  have h := scalarMellinHorizontalIntegral_norm_le
    (y := y) (a := a) (b := b) (T := -T) hy hab (neg_ne_zero.mpr hT.ne')
  have hfun :
      (fun sigma : Real => scalarMellinIntegrand y
        ((sigma : Complex) - (T : Complex) * I)) =
      (fun sigma : Real => scalarMellinIntegrand y
        ((sigma : Complex) + ((-T : Real) : Complex) * I)) := by
    funext sigma
    congr 2
    push_cast
    ring
  rw [hfun]
  simpa only [neg_sq] using h

noncomputable def scalarMellinVerticalIntegral
    (y sigma : Real) : Complex :=
  integral (volume : Measure Real) (scalarMellinVerticalIntegrand y sigma)

theorem scalarMellinVerticalTruncation_tendsto
    {y sigma : Real}
    (hInt : Integrable (scalarMellinVerticalIntegrand y sigma)) :
    Tendsto
      (fun T : Real => intervalIntegral
        (scalarMellinVerticalIntegrand y sigma) (-T) T
        (volume : Measure Real))
      atTop (nhds (scalarMellinVerticalIntegral y sigma)) := by
  unfold scalarMellinVerticalIntegral
  exact intervalIntegral_tendsto_integral hInt tendsto_neg_atTop_atBot tendsto_id

set_option maxHeartbeats 800000 in
theorem scalarMellinVerticalIntegral_sub_left
    {y c A : Real} (hy : 0 < y) (hc : 1 < c) (hA : 2 <= A) :
    scalarMellinVerticalIntegral y c - scalarMellinVerticalIntegral y (-A) =
      (2 * Real.pi : Complex) * (1 - (y : Complex) ^ (-1 : Complex)) := by
  let bottom : Real -> Complex := fun T => intervalIntegral
    (fun sigma : Real => scalarMellinIntegrand y
      ((sigma : Complex) - (T : Complex) * I))
    (-A) c (volume : Measure Real)
  let top : Real -> Complex := fun T => intervalIntegral
    (fun sigma : Real => scalarMellinIntegrand y
      ((sigma : Complex) + (T : Complex) * I))
    (-A) c (volume : Measure Real)
  let right : Real -> Complex := fun T => intervalIntegral
    (fun t : Real => scalarMellinIntegrand y
      ((c : Complex) + (t : Complex) * I))
    (-T) T (volume : Measure Real)
  let left : Real -> Complex := fun T => intervalIntegral
    (fun t : Real => scalarMellinIntegrand y
      ((-A : Complex) + (t : Complex) * I))
    (-T) T (volume : Measure Real)
  let boundary : Real -> Complex := fun T =>
    bottom T - top T + I * right T - I * left T
  have hBottom : Tendsto bottom atTop (nhds 0) := by
    simpa [bottom] using scalarMellinHorizontalIntegral_bottom_tendsto_zero
      hy (show -A <= c by linarith)
  have hTop : Tendsto top atTop (nhds 0) := by
    simpa [top] using scalarMellinHorizontalIntegral_tendsto_zero
      hy (show -A <= c by linarith)
  have hRight : Tendsto right atTop
      (nhds (scalarMellinVerticalIntegral y c)) := by
    simpa [right, scalarMellinVerticalIntegrand] using scalarMellinVerticalTruncation_tendsto
      (integrable_scalarMellinVerticalIntegrand_right hy hc.le)
  have hLeft : Tendsto left atTop
      (nhds (scalarMellinVerticalIntegral y (-A))) := by
    have hBase := scalarMellinVerticalTruncation_tendsto
      (integrable_scalarMellinVerticalIntegrand_left hy hA)
    apply hBase.congr'
    filter_upwards [] with T
    apply intervalIntegral.integral_congr
    intro t ht
    unfold scalarMellinVerticalIntegrand
    congr 2
    push_cast
    ring
  have hBoundary : Tendsto boundary atTop
      (nhds (I * (scalarMellinVerticalIntegral y c -
        scalarMellinVerticalIntegral y (-A)))) := by
    have hIR := Tendsto.const_mul I hRight
    have hIL := Tendsto.const_mul I hLeft
    have h := (hBottom.sub hTop).add hIR |>.sub hIL
    convert h using 1 <;> simp [boundary] <;> ring
  have hEventually : boundary =ᶠ[atTop]
      fun _ => (2 * Real.pi * I) * (1 - (y : Complex) ^ (-1 : Complex)) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    have hRect := scalarMellinIntegrand_rectangleBoundaryIntegral
      (y := y) (a := -A) (b := c) (c := -T) (d := T)
      hy (by linarith) (by linarith) (by linarith) hT
    simpa [boundary, bottom, top, right, left,
      TS309.Goldbach.rectangleBoundaryIntegral,
      scalarMellinVerticalIntegrand, sub_eq_add_neg, ofReal_neg] using hRect
  have hBoundaryResidue : Tendsto boundary atTop
      (nhds ((2 * Real.pi * I) *
        (1 - (y : Complex) ^ (-1 : Complex)))) :=
    (tendsto_const_nhds.congr' hEventually.symm)
  have hEq := tendsto_nhds_unique hBoundary hBoundaryResidue
  have hI : Not (I = 0) := I_ne_zero
  apply (mul_left_cancel₀ hI)
  linear_combination hEq

theorem scalarMellinLeftVerticalIntegral_tendsto_zero
    {y : Real} (hy : 1 < y) :
    Tendsto (fun A : Real => scalarMellinVerticalIntegral y (-A))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hNeg : Tendsto (fun A : Real => y ^ (-A)) atTop (nhds 0) :=
    (tendsto_rpow_atTop_of_base_gt_one y hy).comp tendsto_neg_atTop_atBot
  have hBound : Tendsto
      (fun A : Real => y ^ (-A) * scalarCauchyMass) atTop (nhds 0) := by
    simpa using hNeg.mul_const scalarCauchyMass
  refine squeeze_zero'
    (f := fun A : Real => norm (scalarMellinVerticalIntegral y (-A)))
    (g := fun A : Real => y ^ (-A) * scalarCauchyMass)
    (Filter.Eventually.of_forall (fun A => norm_nonneg _)) ?_ hBound
  filter_upwards [eventually_ge_atTop (2 : Real)] with A hA
  exact scalarMellinVerticalIntegral_norm_le_left hy0 hA

theorem triangleSplineScalarMellinInversion_of_one_lt
    {y c : Real} (hy : 1 < y) (hc : 1 < c) :
    scalarMellinVerticalIntegral y c =
      (2 * Real.pi : Complex) * (1 - (y : Complex) ^ (-1 : Complex)) := by
  have hEq : forall A : Real, 2 <= A ->
      scalarMellinVerticalIntegral y c =
        (2 * Real.pi : Complex) * (1 - (y : Complex) ^ (-1 : Complex)) +
          scalarMellinVerticalIntegral y (-A) := by
    intro A hA
    have h := scalarMellinVerticalIntegral_sub_left
      (lt_trans zero_lt_one hy) hc hA
    linear_combination h
  have hEventually :
      (fun _ : Real => scalarMellinVerticalIntegral y c) =ᶠ[atTop]
        fun A => (2 * Real.pi : Complex) *
          (1 - (y : Complex) ^ (-1 : Complex)) +
            scalarMellinVerticalIntegral y (-A) := by
    filter_upwards [eventually_ge_atTop (2 : Real)] with A hA
    exact hEq A hA
  have hLeft := scalarMellinLeftVerticalIntegral_tendsto_zero hy
  have hRight : Tendsto
      (fun A => (2 * Real.pi : Complex) *
        (1 - (y : Complex) ^ (-1 : Complex)) +
          scalarMellinVerticalIntegral y (-A))
      atTop
      (nhds ((2 * Real.pi : Complex) *
        (1 - (y : Complex) ^ (-1 : Complex)))) := by
    simpa using tendsto_const_nhds.add hLeft
  have hConst : Tendsto (fun _ : Real => scalarMellinVerticalIntegral y c)
      atTop (nhds (scalarMellinVerticalIntegral y c)) := tendsto_const_nhds
  exact tendsto_nhds_unique hConst (hRight.congr' hEventually.symm)

theorem scalarMellinIntegrand_rectangleBoundaryIntegral_right_eq_zero
    {y a b c d : Real} (hy : 0 < y) (ha : 0 < a) (hab : a < b) (_hcd : c < d) :
    TS309.Goldbach.rectangleBoundaryIntegral (scalarMellinIntegrand y) a b c d = 0 := by
  apply TS309.Goldbach.rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  have hzMem := hz
  rw [Complex.mem_reProdIm] at hzMem
  have hzRe : z.re ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab.le] using hzMem.1
  have hz0 : Not (z = 0) := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hzRe.1]
  have hzm1 : Not (z = -1) := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hzRe.1]
  exact (scalarMellinIntegrand_analyticAt_of_ne hy hz0 hzm1).differentiableAt.differentiableWithinAt

set_option maxHeartbeats 800000 in
theorem scalarMellinVerticalIntegral_eq_right
    {y c A : Real} (hy : 0 < y) (hc : 1 < c) (hA : c < A) :
    scalarMellinVerticalIntegral y c = scalarMellinVerticalIntegral y A := by
  let bottom : Real -> Complex := fun T => intervalIntegral
    (fun sigma : Real => scalarMellinIntegrand y
      ((sigma : Complex) - (T : Complex) * I))
    c A (volume : Measure Real)
  let top : Real -> Complex := fun T => intervalIntegral
    (fun sigma : Real => scalarMellinIntegrand y
      ((sigma : Complex) + (T : Complex) * I))
    c A (volume : Measure Real)
  let right : Real -> Complex := fun T => intervalIntegral
    (fun t : Real => scalarMellinIntegrand y
      ((A : Complex) + (t : Complex) * I))
    (-T) T (volume : Measure Real)
  let left : Real -> Complex := fun T => intervalIntegral
    (fun t : Real => scalarMellinIntegrand y
      ((c : Complex) + (t : Complex) * I))
    (-T) T (volume : Measure Real)
  let boundary : Real -> Complex := fun T =>
    bottom T - top T + I * right T - I * left T
  have hBottom : Tendsto bottom atTop (nhds 0) := by
    simpa [bottom] using scalarMellinHorizontalIntegral_bottom_tendsto_zero hy hA.le
  have hTop : Tendsto top atTop (nhds 0) := by
    simpa [top] using scalarMellinHorizontalIntegral_tendsto_zero hy hA.le
  have hRight : Tendsto right atTop
      (nhds (scalarMellinVerticalIntegral y A)) := by
    simpa [right, scalarMellinVerticalIntegrand] using
      scalarMellinVerticalTruncation_tendsto
        (integrable_scalarMellinVerticalIntegrand_right hy (by linarith))
  have hLeft : Tendsto left atTop
      (nhds (scalarMellinVerticalIntegral y c)) := by
    simpa [left, scalarMellinVerticalIntegrand] using
      scalarMellinVerticalTruncation_tendsto
        (integrable_scalarMellinVerticalIntegrand_right hy hc.le)
  have hBoundary : Tendsto boundary atTop
      (nhds (I * (scalarMellinVerticalIntegral y A -
        scalarMellinVerticalIntegral y c))) := by
    have hIR := Tendsto.const_mul I hRight
    have hIL := Tendsto.const_mul I hLeft
    have h := (hBottom.sub hTop).add hIR |>.sub hIL
    convert h using 1 <;> simp [boundary] <;> ring
  have hEventually : boundary =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    have hRect := scalarMellinIntegrand_rectangleBoundaryIntegral_right_eq_zero
      (y := y) (a := c) (b := A) (c := -T) (d := T)
      hy (lt_trans zero_lt_one hc) hA (by linarith)
    simpa [boundary, bottom, top, right, left,
      TS309.Goldbach.rectangleBoundaryIntegral,
      sub_eq_add_neg, ofReal_neg] using hRect
  have hBoundaryZero : Tendsto boundary atTop (nhds 0) :=
    tendsto_const_nhds.congr' hEventually.symm
  have hEq := tendsto_nhds_unique hBoundary hBoundaryZero
  have hI : Not (I = 0) := I_ne_zero
  have hdiff : scalarMellinVerticalIntegral y A -
      scalarMellinVerticalIntegral y c = 0 :=
    (mul_eq_zero.mp hEq).resolve_left hI
  exact (sub_eq_zero.mp hdiff).symm

theorem scalarMellinVerticalIntegral_norm_le_right
    {y sigma : Real} (hy : 0 < y) (hsigma : 1 <= sigma) :
    norm (scalarMellinVerticalIntegral y sigma) <=
      y ^ sigma * scalarCauchyMass := by
  unfold scalarMellinVerticalIntegral
  have hmajorant : Integrable
      (fun t : Real => y ^ sigma * (1 / (1 + t ^ 2))) := by
    simpa [one_div] using integrable_inv_one_add_sq.const_mul (y ^ sigma)
  have h := norm_integral_le_of_norm_le hmajorant
    (Filter.Eventually.of_forall
      (scalarMellinVerticalIntegrand_norm_le_right hy hsigma))
  calc
    norm (integral (volume : Measure Real)
      (scalarMellinVerticalIntegrand y sigma)) <=
        integral (volume : Measure Real)
          (fun t : Real => y ^ sigma * (1 / (1 + t ^ 2))) := h
    _ = y ^ sigma * scalarCauchyMass := by
      unfold scalarCauchyMass
      change (integral (volume : Measure Real)
        (fun t : Real => y ^ sigma • (1 / (1 + t ^ 2)))) = _
      rw [integral_smul]
      rfl

theorem scalarMellinRightVerticalIntegral_tendsto_zero
    {y : Real} (hy0 : 0 < y) (hy1 : y < 1) :
    Tendsto (fun A : Real => scalarMellinVerticalIntegral y A)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hPow : Tendsto (fun A : Real => y ^ A) atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1
  have hBound : Tendsto
      (fun A : Real => y ^ A * scalarCauchyMass) atTop (nhds 0) := by
    simpa using hPow.mul_const scalarCauchyMass
  refine squeeze_zero'
    (f := fun A : Real => norm (scalarMellinVerticalIntegral y A))
    (g := fun A : Real => y ^ A * scalarCauchyMass)
    (Filter.Eventually.of_forall (fun A => norm_nonneg _)) ?_ hBound
  filter_upwards [eventually_ge_atTop (1 : Real)] with A hA
  exact scalarMellinVerticalIntegral_norm_le_right hy0 hA

theorem triangleSplineScalarMellinInversion_of_lt_one
    {y c : Real} (hy0 : 0 < y) (hy1 : y < 1) (hc : 1 < c) :
    scalarMellinVerticalIntegral y c = 0 := by
  have hEq : forall A : Real, c < A ->
      scalarMellinVerticalIntegral y c = scalarMellinVerticalIntegral y A :=
    fun A hA => scalarMellinVerticalIntegral_eq_right hy0 hc hA
  have hEventually :
      (fun _ : Real => scalarMellinVerticalIntegral y c) =ᶠ[atTop]
        fun A => scalarMellinVerticalIntegral y A := by
    filter_upwards [eventually_gt_atTop c] with A hA
    exact hEq A hA
  have hConst : Tendsto (fun _ : Real => scalarMellinVerticalIntegral y c)
      atTop (nhds (scalarMellinVerticalIntegral y c)) := tendsto_const_nhds
  exact tendsto_nhds_unique hConst
    ((scalarMellinRightVerticalIntegral_tendsto_zero hy0 hy1).congr' hEventually.symm)

theorem inv_sq_add_sq_eq_scaled_cauchy
    {r : Real} (hr : Not (r = 0)) (t : Real) :
    1 / (t ^ 2 + r ^ 2) =
      r⁻¹ ^ 2 * (1 / (1 + (r⁻¹ * t) ^ 2)) := by
  field_simp
  ring

theorem integrable_inv_sq_add_sq
    {r : Real} (hr : Not (r = 0)) :
    Integrable (fun t : Real => 1 / (t ^ 2 + r ^ 2)) := by
  have hComp : Integrable
      (fun t : Real => 1 / (1 + (r⁻¹ * t) ^ 2)) := by
    exact (integrable_comp_mul_left_iff
      (fun u : Real => 1 / (1 + u ^ 2)) (inv_ne_zero hr)).2
      (by simpa [one_div] using integrable_inv_one_add_sq)
  have hScaled := hComp.const_mul (r⁻¹ ^ 2)
  apply hScaled.congr
  filter_upwards [] with t
  exact (inv_sq_add_sq_eq_scaled_cauchy hr t).symm

theorem integral_inv_sq_add_sq
    {r : Real} (hr : 0 < r) :
    integral (volume : Measure Real) (fun t : Real => 1 / (t ^ 2 + r ^ 2)) =
      Real.pi / r := by
  let g : Real -> Real := fun u => 1 / (1 + u ^ 2)
  have hScale := Measure.integral_comp_inv_mul_left g r
  have hRewrite :
      (fun t : Real => 1 / (t ^ 2 + r ^ 2)) =
        (fun t : Real => r⁻¹ ^ 2 * g (r⁻¹ * t)) := by
    funext t
    exact inv_sq_add_sq_eq_scaled_cauchy (ne_of_gt hr) t
  rw [hRewrite]
  change (integral (volume : Measure Real)
    (fun t : Real => r⁻¹ ^ 2 • g (r⁻¹ * t))) = _
  rw [integral_smul, hScale]
  simp [g, abs_of_pos hr]
  field_simp
  ring

theorem scalarMellinVerticalIntegrand_one_norm_le_left_sharp
    {A : Real} (hA : 2 <= A) (t : Real) :
    norm (scalarMellinVerticalIntegrand 1 (-A) t) <=
      1 / (t ^ 2 + (A - 1) ^ 2) := by
  unfold scalarMellinVerticalIntegrand scalarMellinIntegrand
  norm_num only [ofReal_one, ofReal_neg]
  rw [Complex.one_cpow, norm_div, norm_one, norm_mul]
  have h0 := norm_nonneg ((-A : Complex) + (t : Complex) * I)
  have h1 := norm_nonneg (((-A : Complex) + (t : Complex) * I) + 1)
  have hs0 : norm ((-A : Complex) + (t : Complex) * I) ^ 2 =
      A ^ 2 + t ^ 2 := by
    rw [<- Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hs1 : norm (((-A : Complex) + (t : Complex) * I) + 1) ^ 2 =
      (A - 1) ^ 2 + t ^ 2 := by
    rw [<- Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hle :
      norm (((-A : Complex) + (t : Complex) * I) + 1) <=
        norm ((-A : Complex) + (t : Complex) * I) := by
    have hsqle :
        norm (((-A : Complex) + (t : Complex) * I) + 1) ^ 2 <=
          norm ((-A : Complex) + (t : Complex) * I) ^ 2 := by
      rw [hs0, hs1]
      nlinarith
    nlinarith [sq_nonneg
      (norm ((-A : Complex) + (t : Complex) * I) -
        norm (((-A : Complex) + (t : Complex) * I) + 1))]
  have hden : t ^ 2 + (A - 1) ^ 2 <=
      norm ((-A : Complex) + (t : Complex) * I) *
        norm (((-A : Complex) + (t : Complex) * I) + 1) := by
    rw [add_comm, <- hs1]
    nlinarith
  have hpos : 0 < t ^ 2 + (A - 1) ^ 2 := by
    have : 0 < A - 1 := by linarith
    positivity
  simpa [one_div] using one_div_le_one_div_of_le hpos hden

theorem scalarMellinVerticalIntegral_one_norm_le_left_sharp
    {A : Real} (hA : 2 <= A) :
    norm (scalarMellinVerticalIntegral 1 (-A)) <= Real.pi / (A - 1) := by
  unfold scalarMellinVerticalIntegral
  have hInt : Integrable
      (fun t : Real => 1 / (t ^ 2 + (A - 1) ^ 2)) :=
    integrable_inv_sq_add_sq (by linarith)
  have h := norm_integral_le_of_norm_le hInt
    (Filter.Eventually.of_forall
      (scalarMellinVerticalIntegrand_one_norm_le_left_sharp hA))
  rw [integral_inv_sq_add_sq (by linarith)] at h
  exact h

theorem scalarMellinLeftVerticalIntegral_one_tendsto_zero :
    Tendsto (fun A : Real => scalarMellinVerticalIntegral 1 (-A))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hBound : Tendsto (fun A : Real => Real.pi / (A - 1))
      atTop (nhds 0) := by
    have hDen : Tendsto (fun A : Real => A - 1) atTop atTop :=
      by
        simpa [sub_eq_add_neg] using
          tendsto_atTop_add_const_right atTop (-1 : Real)
            (show Tendsto (fun A : Real => A) atTop atTop from tendsto_id)
    exact tendsto_const_nhds.div_atTop hDen
  refine squeeze_zero'
    (f := fun A : Real => norm (scalarMellinVerticalIntegral 1 (-A)))
    (g := fun A : Real => Real.pi / (A - 1))
    (Filter.Eventually.of_forall (fun A => norm_nonneg _)) ?_ hBound
  filter_upwards [eventually_ge_atTop (2 : Real)] with A hA
  exact scalarMellinVerticalIntegral_one_norm_le_left_sharp hA

theorem triangleSplineScalarMellinInversion_one
    {c : Real} (hc : 1 < c) :
    scalarMellinVerticalIntegral 1 c = 0 := by
  have hEq : forall A : Real, 2 <= A ->
      scalarMellinVerticalIntegral 1 c = scalarMellinVerticalIntegral 1 (-A) := by
    intro A hA
    have h := scalarMellinVerticalIntegral_sub_left one_pos hc hA
    exact sub_eq_zero.mp (by simpa using h)
  have hEventually :
      (fun _ : Real => scalarMellinVerticalIntegral 1 c) =ᶠ[atTop]
        fun A => scalarMellinVerticalIntegral 1 (-A) := by
    filter_upwards [eventually_ge_atTop (2 : Real)] with A hA
    exact hEq A hA
  have hConst : Tendsto (fun _ : Real => scalarMellinVerticalIntegral 1 c)
      atTop (nhds (scalarMellinVerticalIntegral 1 c)) := tendsto_const_nhds
  exact tendsto_nhds_unique hConst
    (scalarMellinLeftVerticalIntegral_one_tendsto_zero.congr' hEventually.symm)

theorem triangleSplineScalarMellinInversion
    {y c : Real} (hy : 0 < y) (hc : 1 < c) :
    scalarMellinVerticalIntegral y c =
      if 1 < y then
        (2 * Real.pi : Complex) * (1 - (y : Complex) ^ (-1 : Complex))
      else 0 := by
  by_cases hyOne : 1 < y
  . rw [if_pos hyOne]
    exact triangleSplineScalarMellinInversion_of_one_lt hyOne hc
  . rw [if_neg hyOne]
    rcases lt_or_eq_of_le (le_of_not_gt hyOne) with hyLt | rfl
    . exact triangleSplineScalarMellinInversion_of_lt_one hy hyLt hc
    . exact triangleSplineScalarMellinInversion_one hc








end Goldbach
end TS310
