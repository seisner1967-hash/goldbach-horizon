import Mathlib.Tactic
import TS.Goldbach.Strong.TS222.CosSquareBoundaryVanishingReductionBridge

namespace TS223
namespace Goldbach

open Filter

/-!
# TS223 - Cos-Square IPP Primitive AtTop Asymptotic

TS222 reduced the TS219 boundary-vanishing statement to two one-variable
limits for the TS220 primitive `P`:

* `P(T) -> 0` as `T -> +infty`;
* `P(eps) -> 0` as `eps -> 0+`.

This sprint discharges only the first, easier asymptotic.  The proof uses the
explicit primitive

`P(x) = -f(x)/(3*x^3) - f'(x)/(6*x^2) - f''(x)/(6*x)`,

and bounds the three trigonometric coefficients globally.  Each term is then a
bounded coefficient times `x^(-k)` with `k > 0`, hence tends to zero at
`+infty`.

TS223 does not prove the zero-right asymptotic, the full boundary vanishing
statement, the third-derivative cutoff value, Dirichlet cutoff or Abel
convergence, the canonical `sinc^4` value, Plancherel evidence, or Goldbach.
-/

private theorem one_sub_cos_abs_le_two
    (x : Real) :
    |1 - Real.cos x| <= (2 : Real) := by
  have hcos : |Real.cos x| <= (1 : Real) := Real.abs_cos_le_one x
  calc
    |1 - Real.cos x| = |(1 : Real) + -Real.cos x| := by ring_nf
    _ <= |(1 : Real)| + |-Real.cos x| := abs_add _ _
    _ <= (2 : Real) := by
      rw [abs_one, abs_neg]
      linarith

/-- The cos-square remainder is globally bounded. -/
theorem cosSquareRemainder_abs_le_four
    (x : Real) :
    |TS213.Goldbach.cosSquareRemainder x| <= (4 : Real) := by
  have hbase := one_sub_cos_abs_le_two x
  have hnonneg : 0 <= |1 - Real.cos x| := abs_nonneg _
  unfold TS213.Goldbach.cosSquareRemainder
  rw [abs_pow]
  nlinarith [hbase, hnonneg]

/-- The first derivative model in the TS220 primitive is globally bounded. -/
theorem cosSquareFirstDerivativeModel_abs_le_four
    (x : Real) :
    |TS220.Goldbach.cosSquareFirstDerivativeModel x| <= (4 : Real) := by
  have hbase := one_sub_cos_abs_le_two x
  have hsin : |Real.sin x| <= (1 : Real) := Real.abs_sin_le_one x
  have hbase_nonneg : 0 <= |1 - Real.cos x| := abs_nonneg _
  have hsin_nonneg : 0 <= |Real.sin x| := abs_nonneg _
  unfold TS220.Goldbach.cosSquareFirstDerivativeModel
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  nlinarith

/-- The second derivative model in the TS220 primitive is globally bounded. -/
theorem cosSquareSecondDerivativeModel_abs_le_six
    (x : Real) :
    |TS220.Goldbach.cosSquareSecondDerivativeModel x| <= (6 : Real) := by
  have hbase := one_sub_cos_abs_le_two x
  have hsin : |Real.sin x| <= (1 : Real) := Real.abs_sin_le_one x
  have hcos : |Real.cos x| <= (1 : Real) := Real.abs_cos_le_one x
  have hsin_nonneg : 0 <= |Real.sin x| := abs_nonneg _
  have hbase_nonneg : 0 <= |1 - Real.cos x| := abs_nonneg _
  have hcos_nonneg : 0 <= |Real.cos x| := abs_nonneg _
  have hsin_sq_bound :
      |2 * Real.sin x ^ 2| <= (2 : Real) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2), abs_pow]
    nlinarith
  have hcross_bound :
      |2 * (1 - Real.cos x) * Real.cos x| <= (4 : Real) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    nlinarith
  unfold TS220.Goldbach.cosSquareSecondDerivativeModel
  calc
    |2 * Real.sin x ^ 2 + 2 * (1 - Real.cos x) * Real.cos x|
        <= |2 * Real.sin x ^ 2| +
          |2 * (1 - Real.cos x) * Real.cos x| := abs_add _ _
    _ <= (6 : Real) := by
      linarith

private theorem remainder_zpow_tendsto_zero
    (n : Int) (hn : n < 0)
    (C : Real)
    (hC :
      forall x : Real,
        |TS213.Goldbach.cosSquareRemainder x| <= C) :
    Tendsto
      (fun x : Real =>
        TS213.Goldbach.cosSquareRemainder x * x ^ n)
      atTop
      (nhds (0 : Real)) := by
  exact
    bdd_le_mul_tendsto_zero'
      C
      (Eventually.of_forall hC)
      (tendsto_zpow_atTop_zero hn)

private theorem firstDerivative_zpow_tendsto_zero
    (n : Int) (hn : n < 0)
    (C : Real)
    (hC :
      forall x : Real,
        |TS220.Goldbach.cosSquareFirstDerivativeModel x| <= C) :
    Tendsto
      (fun x : Real =>
        TS220.Goldbach.cosSquareFirstDerivativeModel x * x ^ n)
      atTop
      (nhds (0 : Real)) := by
  exact
    bdd_le_mul_tendsto_zero'
      C
      (Eventually.of_forall hC)
      (tendsto_zpow_atTop_zero hn)

private theorem secondDerivative_zpow_tendsto_zero
    (n : Int) (hn : n < 0)
    (C : Real)
    (hC :
      forall x : Real,
        |TS220.Goldbach.cosSquareSecondDerivativeModel x| <= C) :
    Tendsto
      (fun x : Real =>
        TS220.Goldbach.cosSquareSecondDerivativeModel x * x ^ n)
      atTop
      (nhds (0 : Real)) := by
  exact
    bdd_le_mul_tendsto_zero'
      C
      (Eventually.of_forall hC)
      (tendsto_zpow_atTop_zero hn)

/-- The TS220 IPP primitive tends to zero at `+infty`. -/
theorem cosSquareIPPPrimitiveAtTopVanishing :
    TS222.Goldbach.CosSquareIPPPrimitiveAtTopVanishingStatement := by
  unfold TS222.Goldbach.CosSquareIPPPrimitiveAtTopVanishingStatement
  have hrem :
      Tendsto
        (fun x : Real =>
          TS213.Goldbach.cosSquareRemainder x * x ^ (-3 : Int))
        atTop
        (nhds (0 : Real)) := by
    exact
      remainder_zpow_tendsto_zero
        (-3 : Int)
        (by norm_num)
        (4 : Real)
        cosSquareRemainder_abs_le_four
  have hfirst :
      Tendsto
        (fun x : Real =>
          TS220.Goldbach.cosSquareFirstDerivativeModel x *
            x ^ (-2 : Int))
        atTop
        (nhds (0 : Real)) := by
    exact
      firstDerivative_zpow_tendsto_zero
        (-2 : Int)
        (by norm_num)
        (4 : Real)
        cosSquareFirstDerivativeModel_abs_le_four
  have hsecond :
      Tendsto
        (fun x : Real =>
          TS220.Goldbach.cosSquareSecondDerivativeModel x *
            x ^ (-1 : Int))
        atTop
        (nhds (0 : Real)) := by
    exact
      secondDerivative_zpow_tendsto_zero
        (-1 : Int)
        (by norm_num)
        (6 : Real)
        cosSquareSecondDerivativeModel_abs_le_six
  have hterm1 :
      Tendsto
        (fun x : Real =>
          (-(1 / 3 : Real)) *
            TS213.Goldbach.cosSquareRemainder x *
              x ^ (-3 : Int))
        atTop
        (nhds (0 : Real)) := by
    simpa [mul_assoc] using
      (hrem.const_mul (-(1 / 3 : Real)))
  have hterm2 :
      Tendsto
        (fun x : Real =>
          (-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareFirstDerivativeModel x *
              x ^ (-2 : Int))
        atTop
        (nhds (0 : Real)) := by
    simpa [mul_assoc] using
      (hfirst.const_mul (-(1 / 6 : Real)))
  have hterm3 :
      Tendsto
        (fun x : Real =>
          (-(1 / 6 : Real)) *
            TS220.Goldbach.cosSquareSecondDerivativeModel x *
              x ^ (-1 : Int))
        atTop
        (nhds (0 : Real)) := by
    simpa [mul_assoc] using
      (hsecond.const_mul (-(1 / 6 : Real)))
  have hsum :
      Tendsto
        (fun x : Real =>
          (-(1 / 3 : Real)) *
              TS213.Goldbach.cosSquareRemainder x *
                x ^ (-3 : Int) +
            ((-(1 / 6 : Real)) *
                TS220.Goldbach.cosSquareFirstDerivativeModel x *
                  x ^ (-2 : Int) +
              (-(1 / 6 : Real)) *
                TS220.Goldbach.cosSquareSecondDerivativeModel x *
                  x ^ (-1 : Int)))
        atTop
        (nhds (0 : Real)) := by
    simpa using hterm1.add (hterm2.add hterm3)
  have hfun :
      (fun x : Real =>
          (-(1 / 3 : Real)) *
              TS213.Goldbach.cosSquareRemainder x *
                x ^ (-3 : Int) +
            ((-(1 / 6 : Real)) *
                TS220.Goldbach.cosSquareFirstDerivativeModel x *
                  x ^ (-2 : Int) +
              (-(1 / 6 : Real)) *
                TS220.Goldbach.cosSquareSecondDerivativeModel x *
                  x ^ (-1 : Int))) =
        TS220.Goldbach.cosSquareIPPPrimitive := by
    funext x
    unfold TS220.Goldbach.cosSquareIPPPrimitive
    ring_nf
  rw [<- hfun]
  exact hsum

/-- Ledger recording the TS223 atTop asymptotic discharge. -/
structure CosSquareIPPPrimitiveAtTopAsymptoticLedger where
  ts222_boundary_reduction :
    TS222.Goldbach.CosSquareBoundaryVanishingReductionBridgeLedger

  remainder_bound :
    forall x : Real,
      |TS213.Goldbach.cosSquareRemainder x| <= (4 : Real)

  first_derivative_bound :
    forall x : Real,
      |TS220.Goldbach.cosSquareFirstDerivativeModel x| <= (4 : Real)

  second_derivative_bound :
    forall x : Real,
      |TS220.Goldbach.cosSquareSecondDerivativeModel x| <= (6 : Real)

  atTop_vanishing :
    TS222.Goldbach.CosSquareIPPPrimitiveAtTopVanishingStatement

  zero_right_asymptotic_not_proved :
    True

  boundary_vanishing_not_proved :
    True

  third_derivative_cutoff_value_not_proved :
    True

  dirichlet_cutoff_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS223 atTop asymptotic ledger. -/
noncomputable def cosSquareIPPPrimitiveAtTopAsymptoticLedger :
    CosSquareIPPPrimitiveAtTopAsymptoticLedger where
  ts222_boundary_reduction :=
    TS222.Goldbach.cosSquareBoundaryVanishingReductionBridgeLedger
  remainder_bound :=
    cosSquareRemainder_abs_le_four
  first_derivative_bound :=
    cosSquareFirstDerivativeModel_abs_le_four
  second_derivative_bound :=
    cosSquareSecondDerivativeModel_abs_le_six
  atTop_vanishing :=
    cosSquareIPPPrimitiveAtTopVanishing
  zero_right_asymptotic_not_proved :=
    True.intro
  boundary_vanishing_not_proved :=
    True.intro
  third_derivative_cutoff_value_not_proved :=
    True.intro
  dirichlet_cutoff_not_proved :=
    True.intro
  canonical_sinc_fourth_value_not_proved :=
    True.intro
  plancherel_not_proved :=
    True.intro
  goldbach_not_claimed :=
    True.intro

/-- Target proposition for TS223. -/
def CosSquareIPPPrimitiveAtTopAsymptoticTarget :
    Prop :=
  Nonempty CosSquareIPPPrimitiveAtTopAsymptoticLedger

theorem cosSquareIPPPrimitiveAtTopAsymptoticTarget :
    CosSquareIPPPrimitiveAtTopAsymptoticTarget :=
  Nonempty.intro cosSquareIPPPrimitiveAtTopAsymptoticLedger

end Goldbach
end TS223
