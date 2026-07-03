import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TS.Goldbach.Strong.TS223.CosSquareIPPPrimitiveAtTopAsymptotic

namespace TS224
namespace Goldbach

open Filter

/-!
# TS224 - Cos-Square IPP Primitive Zero-Right Asymptotic

TS222 reduced boundary vanishing to two one-variable limits for the TS220
primitive `P`.  TS223 proved the atTop limit.  This sprint proves the remaining
zero-right limit:

`P(eps) -> 0` as `eps -> 0+`.

The proof uses local estimates near zero:

* `|1 - cos x| <= x^2 / 2`;
* `|sin x| <= |x|`;
* `|cos x| <= 1`.

For `0 < x`, these imply

* `|f(x)| <= x^4 / 4`;
* `|f'(x)| <= x^3`;
* `|f''(x)| <= 3*x^2`;
* `|P(x)| <= (3/4)*x`.

Since `(3/4)*x -> 0` along `nhdsWithin 0 (Ioi 0)`, squeezing proves the
zero-right asymptotic.  TS224 also combines this with TS223 through the TS222
bridge to prove the TS219 boundary-vanishing statement.

TS224 does not prove the third-derivative cutoff value, Dirichlet cutoff or
Abel convergence, the cos-square value, the canonical `sinc^4` value,
Plancherel evidence, or Goldbach.
-/

private theorem one_sub_cos_abs_le_half_sq
    (x : Real) :
    |1 - Real.cos x| <= x ^ 2 / 2 := by
  have hnonneg : 0 <= 1 - Real.cos x := by
    exact sub_nonneg.mpr (Real.cos_le_one x)
  have hquad : 1 - Real.cos x <= x ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  simpa [abs_of_nonneg hnonneg] using hquad

/-- Local fourth-order bound for `f(x) = (1 - cos x)^2`. -/
theorem cosSquareRemainder_abs_le_quarter_fourth
    (x : Real) :
    |TS213.Goldbach.cosSquareRemainder x| <= x ^ 4 / 4 := by
  have hbase := one_sub_cos_abs_le_half_sq x
  have hbase_nonneg : 0 <= |1 - Real.cos x| := abs_nonneg _
  unfold TS213.Goldbach.cosSquareRemainder
  rw [abs_pow]
  nlinarith

/-- Local cubic bound for the first derivative model. -/
theorem cosSquareFirstDerivativeModel_abs_le_cube
    (x : Real) (hx : 0 < x) :
    |TS220.Goldbach.cosSquareFirstDerivativeModel x| <= x ^ 3 := by
  have hbase := one_sub_cos_abs_le_half_sq x
  have hsin_abs : |Real.sin x| <= |x| := Real.abs_sin_le_abs
  have hsin : |Real.sin x| <= x := by
    simpa [abs_of_pos hx] using hsin_abs
  have hmul :
      |1 - Real.cos x| * |Real.sin x| <=
        (x ^ 2 / 2) * x := by
    exact mul_le_mul hbase hsin (abs_nonneg _) (by positivity)
  unfold TS220.Goldbach.cosSquareFirstDerivativeModel
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  nlinarith [hmul]

/-- Local quadratic bound for the second derivative model. -/
theorem cosSquareSecondDerivativeModel_abs_le_three_sq
    (x : Real) (hx : 0 < x) :
    |TS220.Goldbach.cosSquareSecondDerivativeModel x| <= 3 * x ^ 2 := by
  have hbase := one_sub_cos_abs_le_half_sq x
  have hsin_abs : |Real.sin x| <= |x| := Real.abs_sin_le_abs
  have hsin : |Real.sin x| <= x := by
    simpa [abs_of_pos hx] using hsin_abs
  have hcos : |Real.cos x| <= (1 : Real) := Real.abs_cos_le_one x
  have hsin_sq :
      |2 * Real.sin x ^ 2| <= 2 * x ^ 2 := by
    have hsin_nonneg : 0 <= |Real.sin x| := abs_nonneg _
    have hsq : |Real.sin x| ^ 2 <= x ^ 2 := by
      nlinarith
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2), abs_pow]
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hcross :
      |2 * (1 - Real.cos x) * Real.cos x| <= x ^ 2 := by
    have hmul :
        |1 - Real.cos x| * |Real.cos x| <=
          (x ^ 2 / 2) * (1 : Real) := by
      exact mul_le_mul hbase hcos (abs_nonneg _) (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    nlinarith [hmul]
  unfold TS220.Goldbach.cosSquareSecondDerivativeModel
  calc
    |2 * Real.sin x ^ 2 + 2 * (1 - Real.cos x) * Real.cos x|
        <= |2 * Real.sin x ^ 2| +
          |2 * (1 - Real.cos x) * Real.cos x| := abs_add _ _
    _ <= 3 * x ^ 2 := by
      linarith

private theorem primitive_term1_abs_le
    (x : Real) (hx : 0 < x) :
    |(-(1 / 3 : Real)) *
        TS213.Goldbach.cosSquareRemainder x *
          x ^ (-3 : Int)| <=
      (1 / 12 : Real) * x := by
  have hf := cosSquareRemainder_abs_le_quarter_fourth x
  have hz_nonneg : 0 <= |x ^ (-3 : Int)| := abs_nonneg _
  have hmul :
      |TS213.Goldbach.cosSquareRemainder x| * |x ^ (-3 : Int)| <=
        (x ^ 4 / 4) * |x ^ (-3 : Int)| := by
    exact mul_le_mul_of_nonneg_right hf hz_nonneg
  have hcoef : |(-(1 / 3 : Real))| = (1 / 3 : Real) := by
    norm_num
  have hz : |x ^ (-3 : Int)| = Inv.inv (x ^ 3) := by
    rw [zpow_neg]
    exact abs_of_pos (inv_pos.mpr (pow_pos hx 3))
  calc
    |(-(1 / 3 : Real)) *
        TS213.Goldbach.cosSquareRemainder x *
          x ^ (-3 : Int)|
        =
      (1 / 3 : Real) *
        |TS213.Goldbach.cosSquareRemainder x| *
          |x ^ (-3 : Int)| := by
      rw [abs_mul, abs_mul, hcoef]
    _ =
      (1 / 3 : Real) *
        (|TS213.Goldbach.cosSquareRemainder x| *
          |x ^ (-3 : Int)|) := by
      ring
    _ <=
      (1 / 3 : Real) * ((x ^ 4 / 4) * |x ^ (-3 : Int)|) := by
      exact mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ =
      (1 / 3 : Real) * ((x ^ 4 / 4) * Inv.inv (x ^ 3)) := by
      rw [hz]
    _ = (1 / 12 : Real) * x := by
      field_simp [ne_of_gt hx]
      ring

private theorem primitive_term2_abs_le
    (x : Real) (hx : 0 < x) :
    |(-(1 / 6 : Real)) *
        TS220.Goldbach.cosSquareFirstDerivativeModel x *
          x ^ (-2 : Int)| <=
      (1 / 6 : Real) * x := by
  have hf := cosSquareFirstDerivativeModel_abs_le_cube x hx
  have hz_nonneg : 0 <= |x ^ (-2 : Int)| := abs_nonneg _
  have hmul :
      |TS220.Goldbach.cosSquareFirstDerivativeModel x| *
          |x ^ (-2 : Int)| <=
        x ^ 3 * |x ^ (-2 : Int)| := by
    exact mul_le_mul_of_nonneg_right hf hz_nonneg
  have hcoef : |(-(1 / 6 : Real))| = (1 / 6 : Real) := by
    norm_num
  have hz : |x ^ (-2 : Int)| = Inv.inv (x ^ 2) := by
    rw [zpow_neg]
    exact abs_of_pos (inv_pos.mpr (pow_pos hx 2))
  calc
    |(-(1 / 6 : Real)) *
        TS220.Goldbach.cosSquareFirstDerivativeModel x *
          x ^ (-2 : Int)|
        =
      (1 / 6 : Real) *
        |TS220.Goldbach.cosSquareFirstDerivativeModel x| *
          |x ^ (-2 : Int)| := by
      rw [abs_mul, abs_mul, hcoef]
    _ =
      (1 / 6 : Real) *
        (|TS220.Goldbach.cosSquareFirstDerivativeModel x| *
          |x ^ (-2 : Int)|) := by
      ring
    _ <=
      (1 / 6 : Real) * (x ^ 3 * |x ^ (-2 : Int)|) := by
      exact mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ =
      (1 / 6 : Real) * (x ^ 3 * Inv.inv (x ^ 2)) := by
      rw [hz]
    _ = (1 / 6 : Real) * x := by
      field_simp [ne_of_gt hx]
      ring

private theorem primitive_term3_abs_le
    (x : Real) (hx : 0 < x) :
    |(-(1 / 6 : Real)) *
        TS220.Goldbach.cosSquareSecondDerivativeModel x *
          x ^ (-1 : Int)| <=
      (1 / 2 : Real) * x := by
  have hf := cosSquareSecondDerivativeModel_abs_le_three_sq x hx
  have hz_nonneg : 0 <= |x ^ (-1 : Int)| := abs_nonneg _
  have hmul :
      |TS220.Goldbach.cosSquareSecondDerivativeModel x| *
          |x ^ (-1 : Int)| <=
        (3 * x ^ 2) * |x ^ (-1 : Int)| := by
    exact mul_le_mul_of_nonneg_right hf hz_nonneg
  have hcoef : |(-(1 / 6 : Real))| = (1 / 6 : Real) := by
    norm_num
  have hz : |x ^ (-1 : Int)| = Inv.inv x := by
    rw [zpow_neg]
    simpa using abs_of_pos (inv_pos.mpr hx)
  calc
    |(-(1 / 6 : Real)) *
        TS220.Goldbach.cosSquareSecondDerivativeModel x *
          x ^ (-1 : Int)|
        =
      (1 / 6 : Real) *
        |TS220.Goldbach.cosSquareSecondDerivativeModel x| *
          |x ^ (-1 : Int)| := by
      rw [abs_mul, abs_mul, hcoef]
    _ =
      (1 / 6 : Real) *
        (|TS220.Goldbach.cosSquareSecondDerivativeModel x| *
          |x ^ (-1 : Int)|) := by
      ring
    _ <=
      (1 / 6 : Real) * ((3 * x ^ 2) * |x ^ (-1 : Int)|) := by
      exact mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ =
      (1 / 6 : Real) * ((3 * x ^ 2) * Inv.inv x) := by
      rw [hz]
    _ = (1 / 2 : Real) * x := by
      field_simp [ne_of_gt hx]
      ring

/-- Local linear bound for the full TS220 primitive. -/
theorem cosSquareIPPPrimitive_abs_le_three_quarters_mul
    (x : Real) (hx : 0 < x) :
    |TS220.Goldbach.cosSquareIPPPrimitive x| <=
      (3 / 4 : Real) * x := by
  have h1 := primitive_term1_abs_le x hx
  have h2 := primitive_term2_abs_le x hx
  have h3 := primitive_term3_abs_le x hx
  unfold TS220.Goldbach.cosSquareIPPPrimitive
  calc
    |(-(1 / 3 : Real)) * TS213.Goldbach.cosSquareRemainder x *
        x ^ (-3 : Int) +
        (-(1 / 6 : Real)) *
          TS220.Goldbach.cosSquareFirstDerivativeModel x *
            x ^ (-2 : Int) +
        (-(1 / 6 : Real)) *
          TS220.Goldbach.cosSquareSecondDerivativeModel x *
            x ^ (-1 : Int)|
        =
      |(-(1 / 3 : Real)) * TS213.Goldbach.cosSquareRemainder x *
          x ^ (-3 : Int) +
        ((-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareFirstDerivativeModel x *
              x ^ (-2 : Int) +
          (-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareSecondDerivativeModel x *
              x ^ (-1 : Int))| := by
      ring_nf
    _ <=
      |(-(1 / 3 : Real)) * TS213.Goldbach.cosSquareRemainder x *
          x ^ (-3 : Int)| +
        (|(-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareFirstDerivativeModel x *
              x ^ (-2 : Int)| +
          |(-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareSecondDerivativeModel x *
              x ^ (-1 : Int)|) := by
      exact (abs_add _ _).trans (add_le_add_left (abs_add _ _) _)
    _ =
      |(-(1 / 3 : Real)) * TS213.Goldbach.cosSquareRemainder x *
          x ^ (-3 : Int)| +
        |(-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareFirstDerivativeModel x *
              x ^ (-2 : Int)| +
          |(-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareSecondDerivativeModel x *
              x ^ (-1 : Int)| := by
      ring
    _ <= (3 / 4 : Real) * x := by
      linarith

/-- The TS220 IPP primitive tends to zero as `x -> 0+`. -/
theorem cosSquareIPPPrimitiveZeroRightVanishing :
    TS222.Goldbach.CosSquareIPPPrimitiveZeroRightVanishingStatement := by
  unfold TS222.Goldbach.CosSquareIPPPrimitiveZeroRightVanishingStatement
  have hx0 :
      Tendsto
        (fun x : Real => (3 / 4 : Real) * x)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) := by
    have hid :
        Tendsto
          (fun x : Real => x)
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
          (nhds (0 : Real)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.const_mul (3 / 4 : Real)
  have hneg :
      Tendsto
        (fun x : Real => -((3 / 4 : Real) * x))
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) := by
    simpa using hx0.neg
  have hlower :
      Filter.Eventually
        (fun x : Real =>
          -((3 / 4 : Real) * x) <=
            TS220.Goldbach.cosSquareIPPPrimitive x)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hbound := cosSquareIPPPrimitive_abs_le_three_quarters_mul x hxpos
    exact neg_le_of_abs_le hbound
  have hupper :
      Filter.Eventually
        (fun x : Real =>
          TS220.Goldbach.cosSquareIPPPrimitive x <=
            (3 / 4 : Real) * x)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hbound := cosSquareIPPPrimitive_abs_le_three_quarters_mul x hxpos
    exact le_of_abs_le hbound
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hneg
      hx0
      hlower
      hupper

/-- Boundary limit evidence after TS223 and TS224. -/
noncomputable def cosSquareIPPPrimitiveBoundaryLimitEvidence :
    TS222.Goldbach.CosSquareIPPPrimitiveBoundaryLimitEvidence where
  atTop_vanishing :=
    TS223.Goldbach.cosSquareIPPPrimitiveAtTopVanishing
  zero_right_vanishing :=
    cosSquareIPPPrimitiveZeroRightVanishing

/-- The TS219 boundary sum vanishes along the corrected cutoff filter. -/
theorem cosSquareBoundaryVanishing :
    TS219.Goldbach.CosSquareBoundaryVanishingStatement :=
  TS222.Goldbach.cosSquareBoundaryVanishing_of_primitiveLimits
    cosSquareIPPPrimitiveBoundaryLimitEvidence

/-- Ledger recording the zero-right asymptotic and boundary vanishing discharge. -/
structure CosSquareIPPPrimitiveZeroRightAsymptoticLedger where
  ts223_atTop :
    TS223.Goldbach.CosSquareIPPPrimitiveAtTopAsymptoticLedger

  remainder_local_bound :
    forall x : Real,
      |TS213.Goldbach.cosSquareRemainder x| <= x ^ 4 / 4

  first_derivative_local_bound :
    forall x : Real,
      0 < x ->
        |TS220.Goldbach.cosSquareFirstDerivativeModel x| <= x ^ 3

  second_derivative_local_bound :
    forall x : Real,
      0 < x ->
        |TS220.Goldbach.cosSquareSecondDerivativeModel x| <= 3 * x ^ 2

  primitive_local_bound :
    forall x : Real,
      0 < x ->
        |TS220.Goldbach.cosSquareIPPPrimitive x| <= (3 / 4 : Real) * x

  zero_right_vanishing :
    TS222.Goldbach.CosSquareIPPPrimitiveZeroRightVanishingStatement

  boundary_vanishing :
    TS219.Goldbach.CosSquareBoundaryVanishingStatement

  third_derivative_cutoff_value_not_proved :
    True

  dirichlet_cutoff_not_proved :
    True

  cos_square_value_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS224 zero-right asymptotic ledger. -/
noncomputable def cosSquareIPPPrimitiveZeroRightAsymptoticLedger :
    CosSquareIPPPrimitiveZeroRightAsymptoticLedger where
  ts223_atTop :=
    TS223.Goldbach.cosSquareIPPPrimitiveAtTopAsymptoticLedger
  remainder_local_bound :=
    cosSquareRemainder_abs_le_quarter_fourth
  first_derivative_local_bound :=
    cosSquareFirstDerivativeModel_abs_le_cube
  second_derivative_local_bound :=
    cosSquareSecondDerivativeModel_abs_le_three_sq
  primitive_local_bound :=
    cosSquareIPPPrimitive_abs_le_three_quarters_mul
  zero_right_vanishing :=
    cosSquareIPPPrimitiveZeroRightVanishing
  boundary_vanishing :=
    cosSquareBoundaryVanishing
  third_derivative_cutoff_value_not_proved :=
    True.intro
  dirichlet_cutoff_not_proved :=
    True.intro
  cos_square_value_not_proved :=
    True.intro
  canonical_sinc_fourth_value_not_proved :=
    True.intro
  plancherel_not_proved :=
    True.intro
  goldbach_not_claimed :=
    True.intro

/-- Target proposition for TS224. -/
def CosSquareIPPPrimitiveZeroRightAsymptoticTarget :
    Prop :=
  Nonempty CosSquareIPPPrimitiveZeroRightAsymptoticLedger

theorem cosSquareIPPPrimitiveZeroRightAsymptoticTarget :
    CosSquareIPPPrimitiveZeroRightAsymptoticTarget :=
  Nonempty.intro cosSquareIPPPrimitiveZeroRightAsymptoticLedger

end Goldbach
end TS224
