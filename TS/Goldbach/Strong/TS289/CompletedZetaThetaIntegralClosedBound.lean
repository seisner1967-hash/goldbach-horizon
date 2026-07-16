import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import TS.Goldbach.Strong.TS288.CompletedZetaThetaMellinCircleGrowth

/-!
# TS289 - Closed Bound for the Completed-Zeta Theta Integral

TS288 bounded Mathlib's entire regularized completed zeta function by a
radial theta-Mellin integral.  This sprint evaluates that integral up to an
explicit elementary envelope.

The modified theta kernel is self-dual under `x -> 1 / x`.  Its right tail
is exactly the nonconstant part of the Jacobi theta series, hence is bounded
by a geometric exponential tail.  Inversion carries the interval `(0, 1)`
to `(1, infinity)`, including the exact square-root Jacobian correction.

For `R >= 2`, the logarithmic tangent inequality at `R + 2` gives

`x ^ (R / 2 - 1 / 2) * exp (-pi * x)
  <= exp (R * log (R + 2)) * exp (-x)`.

Consequently the TS288 majorant is bounded by

`(2 / (1 - exp (-pi))) * exp (R * log (R + 2))`.

This supplies an unconditional closed circle-growth input to TS287 and is
routed through the concrete xi/Jensen factorization.  A sharp
Riemann-von Mangoldt asymptotic, transport to the global TS270 counting
contract, the explicit formula, Gallagher, OTSA, and Goldbach are not
claimed here.
-/

noncomputable section

namespace TS289
namespace Goldbach

open Complex Filter MeasureTheory Real Set

theorem kernel_eq_right
    {x : Real}
    (hx : 1 < x) :
    TS288.Goldbach.completedZetaModifiedThetaKernel x =
      ((HurwitzZeta.evenKernel 0 x - 1 : Real) : Complex) := by
  unfold TS288.Goldbach.completedZetaModifiedThetaKernel WeakFEPair.f_modif
  rw [Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_not_mem (not_mem_Ioo_of_ge hx.le), add_zero]
  simp [HurwitzZeta.hurwitzEvenFEPair]

theorem kernel_inversion
    {x : Real}
    (hx : 0 < x) :
    TS288.Goldbach.completedZetaModifiedThetaKernel (1 / x) =
      ((x ^ (1 / 2 : Real) : Real) : Complex) *
        TS288.Goldbach.completedZetaModifiedThetaKernel x := by
  have h := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE x hx
  have hgf :
      (HurwitzZeta.hurwitzEvenFEPair 0).g_modif x =
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
    have hsymm := congrArg
      (fun P : WeakFEPair Complex => P.f_modif x)
      HurwitzZeta.hurwitzEvenFEPair_zero_symm
    simpa [WeakFEPair.symm, WeakFEPair.f_modif,
      WeakFEPair.g_modif] using hsymm
  rw [hgf] at h
  simpa [TS288.Goldbach.completedZetaModifiedThetaKernel,
    HurwitzZeta.hurwitzEvenFEPair, smul_eq_mul] using h

theorem F_nat_zero_zero_eq
    {x : Real}
    (hx : 0 < x) :
    HurwitzKernelBounds.F_nat 0 0 x =
      1 + HurwitzKernelBounds.F_nat 0 1 x := by
  rw [HurwitzKernelBounds.F_nat,
    tsum_eq_zero_add (HurwitzKernelBounds.summable_f_nat 0 0 hx)]
  simp only [HurwitzKernelBounds.f_nat, Nat.cast_zero, add_zero,
    pow_zero, one_mul, sq, mul_zero, zero_mul, Real.exp_zero]
  congr 1
  apply tsum_congr
  intro n
  rw [HurwitzKernelBounds.f_nat]
  push_cast
  ring_nf

theorem evenKernel_zero_sub_one_eq
    {x : Real}
    (hx : 0 < x) :
    HurwitzZeta.evenKernel 0 x - 1 =
      2 * HurwitzKernelBounds.F_nat 0 1 x := by
  have hRec := HasSum.int_rec
    (HurwitzKernelBounds.summable_f_nat 0 0 hx).hasSum
    (HurwitzKernelBounds.summable_f_nat 0 1 hx).hasSum
  have hRec' :
      HasSum
        (fun n : Int => Real.exp (-Real.pi * (n : Real) ^ 2 * x))
        (HurwitzKernelBounds.F_nat 0 0 x +
          HurwitzKernelBounds.F_nat 0 1 x) := by
    apply hRec.congr_fun
    intro n
    cases n with
    | ofNat m =>
        simp [HurwitzKernelBounds.f_nat]
    | negSucc m =>
        simp [HurwitzKernelBounds.f_nat]
        ring_nf
        simp
  have hEven :
      HurwitzZeta.evenKernel 0 x =
        HurwitzKernelBounds.F_nat 0 0 x +
          HurwitzKernelBounds.F_nat 0 1 x := by
    exact (HurwitzZeta.hasSum_int_evenKernel (0 : Real) hx).unique
      (by simpa only [add_zero] using hRec')
  rw [hEven, F_nat_zero_zero_eq hx]
  ring

theorem kernel_norm_le_geometric
    {x : Real}
    (hx : 1 < x) :
    norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) <=
      2 * (Real.exp (-Real.pi * x) /
        (1 - Real.exp (-Real.pi * x))) := by
  rw [kernel_eq_right hx, norm_real, Real.norm_eq_abs]
  have hEq :
      HurwitzZeta.evenKernel 0 x - 1 =
        2 * HurwitzKernelBounds.F_nat 0 1 x := by
    exact evenKernel_zero_sub_one_eq (lt_trans zero_lt_one hx)
  rw [hEq, abs_mul, _root_.abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  have hBound := HurwitzKernelBounds.F_nat_zero_le
    (a := (1 : Real)) zero_le_one (lt_trans zero_lt_one hx)
  rw [Real.norm_eq_abs] at hBound
  simpa using mul_le_mul_of_nonneg_left hBound (by norm_num : (0 : Real) <= 2)

noncomputable def lowerThetaKernelTail (R x : Real) : Real :=
  x ^ (-R / 2 - 1) *
    norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)

noncomputable def upperThetaKernelTail (R x : Real) : Real :=
  x ^ (R / 2 - 1 / 2) *
    norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)

theorem kernel_norm_inversion
    {x : Real}
    (hx : 0 < x) :
    norm (TS288.Goldbach.completedZetaModifiedThetaKernel (1 / x)) =
      x ^ (1 / 2 : Real) *
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) := by
  rw [kernel_inversion hx, norm_mul, norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg (Real.rpow_nonneg hx.le _)]

theorem lowerThetaKernelTail_integral_eq_upper
    (R : Real) :
    integral (volume.restrict (Ioo 0 1)) (lowerThetaKernelTail R) =
      integral (volume.restrict (Ioi 1)) (upperThetaKernelTail R) := by
  let g : Real -> Real := (Ioi 1).indicator (upperThetaKernelTail R)
  have hSub := integral_comp_rpow_Ioi g
    (p := (-1 : Real)) (by norm_num)
  have hSub' :
      integral (volume.restrict (Ioi 0))
          (fun x : Real =>
            (|(-1 : Real)| * x ^ ((-1 : Real) - 1)) *
              g (x ^ (-1 : Real))) =
        integral (volume.restrict (Ioi 0)) g := by
    simpa only [smul_eq_mul] using hSub
  have hLeft :
      integral (volume.restrict (Ioi 0))
          (fun x : Real =>
            (|(-1 : Real)| * x ^ ((-1 : Real) - 1)) *
              g (x ^ (-1 : Real))) =
        integral (volume.restrict (Ioo 0 1))
          (lowerThetaKernelTail R) := by
    rw [<- integral_indicator measurableSet_Ioi,
      <- integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx0 : 0 < x
    case pos =>
      by_cases hx1 : x < 1
      case pos =>
        have hxInv : 1 < x ^ (-1 : Real) := by
          rw [Real.rpow_neg_one]
          simpa only [one_div] using one_lt_one_div hx0 hx1
        simp only [indicator_of_mem (mem_Ioi.mpr hx0),
          indicator_of_mem (mem_Ioo.mpr (And.intro hx0 hx1)), g,
          indicator_of_mem (mem_Ioi.mpr hxInv), abs_neg, abs_one,
          one_mul, smul_eq_mul]
        unfold upperThetaKernelTail lowerThetaKernelTail
        rw [Real.rpow_neg_one, <- one_div,
          kernel_norm_inversion hx0, one_div]
        rw [<- Real.rpow_neg_one x,
          <- Real.rpow_mul hx0.le]
        have hPow :
            x ^ ((-1 : Real) - 1) *
                (x ^ ((-1 : Real) * (R / 2 - 1 / 2)) *
                  x ^ (1 / 2 : Real)) =
              x ^ (-R / 2 - 1) := by
          rw [<- Real.rpow_add hx0, <- Real.rpow_add hx0]
          congr 1
          ring
        calc
          x ^ ((-1 : Real) - 1) *
                (x ^ ((-1 : Real) * (R / 2 - 1 / 2)) *
                  (x ^ (1 / 2 : Real) *
                    norm (TS288.Goldbach.completedZetaModifiedThetaKernel x))) =
              (x ^ ((-1 : Real) - 1) *
                  (x ^ ((-1 : Real) * (R / 2 - 1 / 2)) *
                    x ^ (1 / 2 : Real))) *
                norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) := by
            ring
          _ = x ^ (-R / 2 - 1) *
                norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) := by
            rw [hPow]
      case neg =>
        have hxInv : x ^ (-1 : Real) <= 1 := by
          rw [Real.rpow_neg_one]
          have h := one_div_le_one_div_of_le one_pos (le_of_not_gt hx1)
          simpa only [one_div, inv_one] using h
        simp [g, hx0, hx1, hxInv]
    case neg =>
      simp [g, hx0]
  have hRight :
      integral (volume.restrict (Ioi 0)) g =
        integral (volume.restrict (Ioi 1))
          (upperThetaKernelTail R) := by
    rw [<- integral_indicator measurableSet_Ioi,
      <- integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 1 < x
    case pos => simp [g, hx, lt_trans zero_lt_one hx]
    case neg =>
      by_cases hx0 : 0 < x
      case pos => simp [g, hx, hx0]
      case neg => simp [g, hx, hx0]
  exact hLeft.symm.trans (hSub'.trans hRight)

theorem rpow_mul_exp_neg_pi_le_closed
    {R x : Real}
    (hR : 2 <= R)
    (hx : 0 < x) :
    x ^ (R / 2 - 1 / 2) * Real.exp (-Real.pi * x) <=
      Real.exp (R * Real.log (R + 2)) * Real.exp (-x) := by
  let b : Real := R / 2 - 1 / 2
  let B : Real := R + 2
  have hb : 0 <= b := by
    dsimp [b]
    linarith
  have hbR : b <= R := by
    dsimp [b]
    linarith
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hBone : 1 <= B := by
    dsimp [B]
    linarith
  have hLogB : 0 <= Real.log B := Real.log_nonneg hBone
  have hLogDiv := Real.log_le_sub_one_of_pos (div_pos hx hB)
  rw [Real.log_div hx.ne' hB.ne'] at hLogDiv
  have hLogScaled :
      b * Real.log x <= b * (x / B - 1 + Real.log B) := by
    have hMul := mul_le_mul_of_nonneg_left hLogDiv hb
    calc
      b * Real.log x =
          b * (Real.log x - Real.log B) + b * Real.log B := by ring
      _ <= b * (x / B - 1) + b * Real.log B :=
        add_le_add_right hMul _
      _ = b * (x / B - 1 + Real.log B) := by ring
  have hRatio : b / B <= 1 := by
    exact (div_le_one hB).mpr (by dsimp [b, B]; linarith)
  have hRatioMul : (b / B) * x <= x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hRatio hx.le
  have hBTerm : b * Real.log B <= R * Real.log B :=
    mul_le_mul_of_nonneg_right hbR hLogB
  have hLogFinal :
      b * Real.log x <= x + R * Real.log B := by
    calc
      b * Real.log x <= b * (x / B - 1 + Real.log B) := hLogScaled
      _ = (b / B) * x - b + b * Real.log B := by ring
      _ <= x - b + b * Real.log B := by linarith
      _ <= x + R * Real.log B := by linarith
  have hPi : 2 * x <= Real.pi * x :=
    mul_le_mul_of_nonneg_right Real.two_le_pi hx.le
  rw [Real.rpow_def_of_pos hx, <- Real.exp_add, <- Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [b, B] at hLogFinal
  dsimp [b, B]
  nlinarith

noncomputable def completedZetaThetaTailConstant : Real :=
  2 / (1 - Real.exp (-Real.pi))

theorem completedZetaThetaTailConstant_pos :
    0 < completedZetaThetaTailConstant := by
  unfold completedZetaThetaTailConstant
  apply div_pos two_pos
  rw [sub_pos, Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr Real.pi_pos

theorem completedZetaModifiedThetaKernel_norm_le_exp
    {x : Real}
    (hx : 1 <= x) :
    norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) <=
      completedZetaThetaTailConstant * Real.exp (-Real.pi * x) := by
  rcases hx.eq_or_lt with rfl | hx
  case inl =>
    have hZero :
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel 1) = 0 := by
      simp [TS288.Goldbach.completedZetaModifiedThetaKernel,
        WeakFEPair.f_modif]
    rw [hZero]
    exact mul_nonneg completedZetaThetaTailConstant_pos.le (Real.exp_pos _).le
  case inr =>
    have hGeom := kernel_norm_le_geometric hx
    have hExp : Real.exp (-Real.pi * x) <= Real.exp (-Real.pi) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hDenPos : 0 < 1 - Real.exp (-Real.pi) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr Real.pi_pos
    have hDen :
        1 - Real.exp (-Real.pi) <=
          1 - Real.exp (-Real.pi * x) := by
      linarith
    have hFrac :
        Real.exp (-Real.pi * x) /
            (1 - Real.exp (-Real.pi * x)) <=
          Real.exp (-Real.pi * x) /
            (1 - Real.exp (-Real.pi)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hDenPos hDen
    calc
      norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) <=
          2 * (Real.exp (-Real.pi * x) /
            (1 - Real.exp (-Real.pi * x))) := hGeom
      _ <= 2 * (Real.exp (-Real.pi * x) /
            (1 - Real.exp (-Real.pi))) :=
        mul_le_mul_of_nonneg_left hFrac (by norm_num)
      _ = completedZetaThetaTailConstant * Real.exp (-Real.pi * x) := by
        unfold completedZetaThetaTailConstant
        field_simp [hDenPos.ne']

theorem upperThetaKernelTail_le_closed
    {R x : Real}
    (hR : 2 <= R)
    (hx : 1 <= x) :
    upperThetaKernelTail R x <=
      completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) * Real.exp (-x) := by
  have hKernel := completedZetaModifiedThetaKernel_norm_le_exp hx
  have hPower := rpow_mul_exp_neg_pi_le_closed hR
    (lt_of_lt_of_le zero_lt_one hx)
  unfold upperThetaKernelTail
  calc
    x ^ (R / 2 - 1 / 2) *
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) <=
      x ^ (R / 2 - 1 / 2) *
        (completedZetaThetaTailConstant * Real.exp (-Real.pi * x)) :=
      mul_le_mul_of_nonneg_left hKernel
        (Real.rpow_nonneg (le_trans zero_le_one hx) _)
    _ = completedZetaThetaTailConstant *
        (x ^ (R / 2 - 1 / 2) * Real.exp (-Real.pi * x)) := by ring
    _ <= completedZetaThetaTailConstant *
        (Real.exp (R * Real.log (R + 2)) * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hPower completedZetaThetaTailConstant_pos.le
    _ = completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) * Real.exp (-x) := by ring

theorem upperThetaKernelTail_integral_le_closed
    {R : Real}
    (hR : 2 <= R) :
    integral (volume.restrict (Ioi 1)) (upperThetaKernelTail R) <=
      completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) := by
  have hTailInt : IntegrableOn (upperThetaKernelTail R) (Ioi 1) := by
    have h := TS288.Goldbach.upperThetaMellinEnvelope_integrableOn (R + 1)
    refine (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun ?_ measurableSet_Ioi
    intro x hx
    unfold upperThetaKernelTail
    ring_nf
  have hExpInt :
      IntegrableOn (fun x : Real => Real.exp (-x)) (Ioi 1) := by
    have h := Real.GammaIntegral_convergent (s := (1 : Real)) one_pos
    refine (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp
  have hClosedInt :
      IntegrableOn
        (fun x : Real =>
          completedZetaThetaTailConstant *
            Real.exp (R * Real.log (R + 2)) * Real.exp (-x))
        (Ioi 1) := by
    exact hExpInt.const_mul _
  have hMono := setIntegral_mono_on hTailInt hClosedInt measurableSet_Ioi
    (fun x hx => upperThetaKernelTail_le_closed hR hx.le)
  calc
    integral (volume.restrict (Ioi 1)) (upperThetaKernelTail R) <=
        integral (volume.restrict (Ioi 1))
          (fun x : Real =>
            completedZetaThetaTailConstant *
              Real.exp (R * Real.log (R + 2)) * Real.exp (-x)) := hMono
    _ = completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) * Real.exp (-1) := by
      rw [integral_mul_left, integral_exp_neg_Ioi]
    _ <= completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) := by
      have hConst : 0 <= completedZetaThetaTailConstant *
          Real.exp (R * Real.log (R + 2)) :=
        mul_nonneg completedZetaThetaTailConstant_pos.le (Real.exp_pos _).le
      have hExpOne : Real.exp (-1) <= 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-1 : Real) <= 0)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hExpOne hConst

theorem thetaMellinRadialWeight_eq_lower
    {R x : Real}
    (hR : 0 <= R)
    (hx0 : 0 < x)
    (hx1 : x <= 1) :
    TS288.Goldbach.thetaMellinRadialWeight R x =
      x ^ (-R / 2 - 1) := by
  unfold TS288.Goldbach.thetaMellinRadialWeight
  rw [max_eq_right]
  exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)

theorem thetaMellinRadialWeight_eq_upper
    {R x : Real}
    (hR : 0 <= R)
    (hx : 1 <= x) :
    TS288.Goldbach.thetaMellinRadialWeight R x =
      x ^ (R / 2 - 1) := by
  rcases hx.eq_or_lt with rfl | hx
  case inl => simp [TS288.Goldbach.thetaMellinRadialWeight]
  case inr =>
    unfold TS288.Goldbach.thetaMellinRadialWeight
    rw [max_eq_left]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)

theorem thetaMellinRadialIntegral_le_upperTail
    {R : Real}
    (hR : 0 <= R) :
    integral (volume.restrict (Ioi 0))
        (fun x : Real =>
          TS288.Goldbach.thetaMellinRadialWeight R x *
            norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)) <=
      2 * integral (volume.restrict (Ioi 1))
        (upperThetaKernelTail R) := by
  let f : Real -> Real := fun x =>
    TS288.Goldbach.thetaMellinRadialWeight R x *
      norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)
  have hInt : IntegrableOn f (Ioi 0) :=
    TS288.Goldbach.thetaMellinRadialEnvelope_integrableOn R
  have hLowInt : IntegrableOn f (Ioo 0 1) :=
    hInt.mono_set (fun _ hx => hx.1)
  have hHighInt : IntegrableOn f (Ici 1) :=
    hInt.mono_set (by
      intro x hx
      change 0 < x
      change 1 <= x at hx
      linarith)
  have hDisjoint : Disjoint (Ioo (0 : Real) 1) (Ici 1) := by
    apply Set.disjoint_left.mpr
    intro x hxLow hxHigh
    exact (not_lt_of_ge hxHigh hxLow.2)
  have hUnion : Set.union (Ioo (0 : Real) 1) (Ici 1) = Ioi 0 := by
    ext x
    constructor
    case mp =>
      intro hx
      rcases hx with hx | hx
      case inl => exact hx.1
      case inr =>
        change 1 <= x at hx
        change 0 < x
        linarith
    case mpr =>
      intro hx
      by_cases hx1 : x < 1
      case pos => exact Or.inl (And.intro hx hx1)
      case neg => exact Or.inr (le_of_not_gt hx1)
  have hSplit :
      integral (volume.restrict (Ioi 0)) f =
        integral (volume.restrict (Ioo 0 1)) f +
          integral (volume.restrict (Ici 1)) f := by
    rw [<- hUnion]
    exact setIntegral_union hDisjoint measurableSet_Ici hLowInt hHighInt
  have hLowEq :
      integral (volume.restrict (Ioo 0 1)) f =
        integral (volume.restrict (Ioo 0 1))
          (lowerThetaKernelTail R) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    unfold lowerThetaKernelTail
    change TS288.Goldbach.thetaMellinRadialWeight R x *
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) =
      x ^ (-R / 2 - 1) *
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)
    rw [thetaMellinRadialWeight_eq_lower hR hx.1 hx.2.le]
  have hUpperInt : IntegrableOn (upperThetaKernelTail R) (Ici 1) := by
    have h := TS288.Goldbach.upperThetaMellinEnvelope_integrableOn (R + 1)
    refine (h.mono_set (by
      intro x hx
      change 0 < x
      change 1 <= x at hx
      linarith)).congr_fun ?_ measurableSet_Ici
    intro x hx
    unfold upperThetaKernelTail
    ring_nf
  have hHighLe :
      integral (volume.restrict (Ici 1)) f <=
        integral (volume.restrict (Ici 1))
          (upperThetaKernelTail R) := by
    apply setIntegral_mono_on hHighInt hUpperInt measurableSet_Ici
    intro x hx
    change 1 <= x at hx
    unfold upperThetaKernelTail
    change TS288.Goldbach.thetaMellinRadialWeight R x *
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) <=
      x ^ (R / 2 - 1 / 2) *
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)
    rw [thetaMellinRadialWeight_eq_upper hR hx]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rcases hx.eq_or_lt with rfl | hx
    case inl => simp
    case inr =>
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hUpperIciEq :
      integral (volume.restrict (Ici 1)) (upperThetaKernelTail R) =
        integral (volume.restrict (Ioi 1)) (upperThetaKernelTail R) := by
    exact integral_Ici_eq_integral_Ioi
  rw [hSplit, hLowEq, lowerThetaKernelTail_integral_eq_upper R]
  linarith [hHighLe, hUpperIciEq]

theorem completedZetaThetaMellinMajorant_le_closed
    {R : Real}
    (hR : 2 <= R) :
    TS288.Goldbach.completedZetaThetaMellinMajorant R <=
      completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) := by
  unfold TS288.Goldbach.completedZetaThetaMellinMajorant
  calc
    integral (volume.restrict (Ioi 0))
          (fun x : Real =>
            TS288.Goldbach.thetaMellinRadialWeight R x *
              norm (TS288.Goldbach.completedZetaModifiedThetaKernel x)) / 2 <=
        (2 * integral (volume.restrict (Ioi 1))
          (upperThetaKernelTail R)) / 2 :=
      div_le_div_of_nonneg_right
        (thetaMellinRadialIntegral_le_upperTail (by linarith)) (by norm_num)
    _ = integral (volume.restrict (Ioi 1))
        (upperThetaKernelTail R) := by ring
    _ <= completedZetaThetaTailConstant *
        Real.exp (R * Real.log (R + 2)) :=
      upperThetaKernelTail_integral_le_closed hR

noncomputable def completedZetaThetaClosedMajorant (R : Real) : Real :=
  completedZetaThetaTailConstant * Real.exp (R * Real.log (R + 2))

def completedZetaThetaClosedCircleGrowth :
    TS287.Goldbach.CompletedZetaZeroCircleGrowthStatement
      completedZetaThetaClosedMajorant where
  norm_le := by
    intro R hR z hz
    exact (TS288.Goldbach.completedRiemannZetaZero_abs_le_thetaMellinMajorant
      R z hz).trans (completedZetaThetaMellinMajorant_le_closed hR)

noncomputable def xiThetaClosedBoundaryNormStatement
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
      (TS.Goldbach.MasterAPI.xi_factorization r hr)
      (TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
        completedZetaThetaClosedMajorant
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :=
  TS287.Goldbach.xi_explicitBoundaryNormStatement
    completedZetaThetaClosedCircleGrowth r hr hLarge

theorem xi_finiteJensenBoundaryEstimate_thetaClosed
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      (TS.Goldbach.MasterAPI.xi_disk_data r hr)
      TS.Goldbach.MasterAPI.xi
      (TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
        completedZetaThetaClosedMajorant
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :=
  TS287.Goldbach.xi_finiteJensenBoundaryEstimate_explicit
    completedZetaThetaClosedCircleGrowth r hr hLarge

theorem xi_zero_count_le_thetaClosed_majorant
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (TS.Goldbach.MasterAPI.xi_disk_data r hr) : Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (TS287.Goldbach.xiBoundaryMajorantFromCompletedZeta
            completedZetaThetaClosedMajorant
            (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius)
          (TS.Goldbach.MasterAPI.xi
            (TS.Goldbach.MasterAPI.xi_geometry r hr).center) /
        Real.log
          ((TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius /
            (TS.Goldbach.MasterAPI.xi_geometry r hr).innerRadius) :=
  TS287.Goldbach.xi_zero_count_le_explicit_completedZeta_majorant
    completedZetaThetaClosedCircleGrowth r hr hLarge

structure CompletedZetaThetaIntegralClosedBoundLedger where
  ts288_theta_mellin_growth :
    TS288.Goldbach.CompletedZetaThetaMellinCircleGrowthLedger
  modified_kernel_inversion :
    forall x : Real,
      0 < x ->
        TS288.Goldbach.completedZetaModifiedThetaKernel (1 / x) =
          ((x ^ (1 / 2 : Real) : Real) : Complex) *
            TS288.Goldbach.completedZetaModifiedThetaKernel x
  right_kernel_exponential_decay :
    forall x : Real,
      1 <= x ->
        norm (TS288.Goldbach.completedZetaModifiedThetaKernel x) <=
          completedZetaThetaTailConstant * Real.exp (-Real.pi * x)
  low_tail_inversion :
    forall R : Real,
      integral (volume.restrict (Ioo 0 1)) (lowerThetaKernelTail R) =
        integral (volume.restrict (Ioi 1)) (upperThetaKernelTail R)
  closed_theta_mellin_bound :
    forall R : Real,
      2 <= R ->
        TS288.Goldbach.completedZetaThetaMellinMajorant R <=
          completedZetaThetaClosedMajorant R
  completed_zeta_closed_circle_growth :
    TS287.Goldbach.CompletedZetaZeroCircleGrowthStatement
      completedZetaThetaClosedMajorant
  von_mangoldt_asymptotic_not_proved : True
  xi_zeta_zero_count_transport_not_proved : True
  global_multiplicity_count_contract_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def completedZetaThetaIntegralClosedBoundLedger :
    CompletedZetaThetaIntegralClosedBoundLedger where
  ts288_theta_mellin_growth :=
    TS288.Goldbach.completedZetaThetaMellinCircleGrowthLedger
  modified_kernel_inversion := by
    intro x hx
    exact kernel_inversion hx
  right_kernel_exponential_decay := by
    intro x hx
    exact completedZetaModifiedThetaKernel_norm_le_exp hx
  low_tail_inversion := lowerThetaKernelTail_integral_eq_upper
  closed_theta_mellin_bound := by
    intro R hR
    exact completedZetaThetaMellinMajorant_le_closed hR
  completed_zeta_closed_circle_growth := completedZetaThetaClosedCircleGrowth
  von_mangoldt_asymptotic_not_proved := True.intro
  xi_zeta_zero_count_transport_not_proved := True.intro
  global_multiplicity_count_contract_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def CompletedZetaThetaIntegralClosedBoundTarget : Prop :=
  Nonempty CompletedZetaThetaIntegralClosedBoundLedger

theorem completedZetaThetaIntegralClosedBoundTarget :
    CompletedZetaThetaIntegralClosedBoundTarget :=
  Nonempty.intro completedZetaThetaIntegralClosedBoundLedger

end Goldbach
end TS289
