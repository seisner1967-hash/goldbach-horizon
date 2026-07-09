import Mathlib.Tactic
import TS.Goldbach.Strong.TS239.DirichletCutoffAPIDirectRouteProbe

/-!
# TS240 - Dirichlet Tail Bound Discharge

TS239 exposed the quantitative direct-cutoff fallback target:

`|F(U) - F(T)| <= 2 / T` for `0 < T <= U`, where
`F(T) = int_0^T sin x / x dx`.

This sprint proves exactly that tail estimate.  It works only on the positive
interval `[T, U]`, so the repository Dirichlet kernel has no singularity on the
interval.  No Cauchy convergence, cutoff value, Abel-to-cutoff bridge,
cos-square value, `sinc^4` value, Plancherel evidence, or Goldbach claim is
made here.
-/

namespace TS240
namespace Goldbach

open MeasureTheory

/-- Primitive used for the one-step integration by parts tail identity. -/
noncomputable def dirichletTailPrimitive (x : Real) : Real :=
  -Real.cos x / x

private theorem positive_on_uIcc_of_left_pos
    {T U x : Real}
    (hT : 0 < T)
    (hTU : T <= U)
    (hx : Set.Mem (Set.uIcc T U) x) :
    0 < x := by
  have hxIcc : Set.Mem (Set.Icc T U) x := by
    simpa [Set.uIcc_of_le hTU] using hx
  exact lt_of_lt_of_le hT hxIcc.1

/-- The partial-integral difference is the interval integral over `[T, U]`. -/
theorem dirichletPartialIntegral_sub_eq_tail
    (T U : Real) :
    TS228.Goldbach.dirichletUnitPartialIntegral U -
        TS228.Goldbach.dirichletUnitPartialIntegral T =
      intervalIntegral
        (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
        T
        U
        volume := by
  unfold TS228.Goldbach.dirichletUnitPartialIntegral
  exact
    intervalIntegral.integral_interval_sub_left
      (TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable 0 U)
      (TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable 0 T)

/-- On the positive half-line, the unit kernel is `sin x / x`. -/
theorem sineDirichletKernel_one_eq_sin_div
    {x : Real}
    (_hx : Not (x = 0)) :
    TS213.Goldbach.sineDirichletKernel 1 x =
      Real.sin x / x := by
  simp [TS213.Goldbach.sineDirichletKernel]

/-- The tail primitive differentiates to `D_1(x) + cos x / x^2` away from zero. -/
theorem hasDerivAt_dirichletTailPrimitive
    (x : Real)
    (hx : Not (x = 0)) :
    HasDerivAt
      dirichletTailPrimitive
      (TS213.Goldbach.sineDirichletKernel 1 x +
        Real.cos x / x ^ 2)
      x := by
  have hnum :
      HasDerivAt
        (fun y : Real => -Real.cos y)
        (Real.sin x)
        x := by
    simpa using (Real.hasDerivAt_cos x).neg
  have hden :
      HasDerivAt (fun y : Real => y) (1 : Real) x :=
    hasDerivAt_id x
  have hdiv := hnum.div hden hx
  have hvalue :
      TS213.Goldbach.sineDirichletKernel 1 x +
          Real.cos x / x ^ 2 =
        (Real.sin x * x - -Real.cos x * 1) / x ^ 2 := by
    rw [sineDirichletKernel_one_eq_sin_div hx]
    field_simp [hx]
    ring
  simpa [dirichletTailPrimitive, hvalue] using hdiv

private theorem cos_over_square_intervalIntegrable
    (T U : Real)
    (hT : 0 < T)
    (hTU : T <= U) :
    IntervalIntegrable
      (fun x : Real => Real.cos x / x ^ 2)
      volume
      T
      U := by
  have hcont :
      ContinuousOn
        (fun x : Real => Real.cos x / x ^ 2)
        (Set.uIcc T U) := by
    intro x hx
    have hxpos : 0 < x :=
      positive_on_uIcc_of_left_pos hT hTU hx
    exact
      ((by fun_prop :
        Continuous (fun y : Real => Real.cos y)).continuousWithinAt).div
        ((by fun_prop :
          Continuous (fun y : Real => y ^ 2)).continuousWithinAt)
        (pow_ne_zero 2 (ne_of_gt hxpos))
  exact hcont.intervalIntegrable

private theorem one_over_square_intervalIntegrable
    (T U : Real)
    (hT : 0 < T)
    (hTU : T <= U) :
    IntervalIntegrable
      (fun x : Real => (1 : Real) / x ^ 2)
      volume
      T
      U := by
  have hcont :
      ContinuousOn
        (fun x : Real => (1 : Real) / x ^ 2)
        (Set.uIcc T U) := by
    intro x hx
    have hxpos : 0 < x :=
      positive_on_uIcc_of_left_pos hT hTU hx
    exact
      ((by fun_prop :
        Continuous (fun y : Real => (1 : Real))).continuousWithinAt).div
        ((by fun_prop :
          Continuous (fun y : Real => y ^ 2)).continuousWithinAt)
        (pow_ne_zero 2 (ne_of_gt hxpos))
  exact hcont.intervalIntegrable

/-- Exact finite tail identity obtained by FTC from `-cos x / x`. -/
theorem dirichletTailIntegral_eq
    (T U : Real)
    (hT : 0 < T)
    (hTU : T <= U) :
    TS228.Goldbach.dirichletUnitPartialIntegral U -
        TS228.Goldbach.dirichletUnitPartialIntegral T =
      Real.cos T / T -
        Real.cos U / U -
          intervalIntegral
            (fun x : Real => Real.cos x / x ^ 2)
            T
            U
            volume := by
  have hU : 0 < U := lt_of_lt_of_le hT hTU
  let d : Real -> Real := fun x =>
    TS213.Goldbach.sineDirichletKernel 1 x +
      Real.cos x / x ^ 2
  have hderiv :
      forall x : Real, Set.Mem (Set.uIcc T U) x ->
        HasDerivAt dirichletTailPrimitive (d x) x := by
    intro x hx
    have hxpos : 0 < x :=
      positive_on_uIcc_of_left_pos hT hTU hx
    exact hasDerivAt_dirichletTailPrimitive x (ne_of_gt hxpos)
  have hcosInt :
      IntervalIntegrable
        (fun x : Real => Real.cos x / x ^ 2)
        volume
        T
        U :=
    cos_over_square_intervalIntegrable T U hT hTU
  have hDInt :
      IntervalIntegrable
        (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
        volume
        T
        U :=
    TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable T U
  have hsumInt : IntervalIntegrable d volume T U := by
    unfold d
    exact hDInt.add hcosInt
  have hFTC :
      intervalIntegral d T U volume =
        dirichletTailPrimitive U - dirichletTailPrimitive T := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hsumInt
  have hsplit :
      intervalIntegral d T U volume =
        intervalIntegral
          (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
          T
          U
          volume +
        intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume := by
    unfold d
    exact intervalIntegral.integral_add hDInt hcosInt
  have htail :
      intervalIntegral
          (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
          T
          U
          volume =
        dirichletTailPrimitive U - dirichletTailPrimitive T -
          intervalIntegral
            (fun x : Real => Real.cos x / x ^ 2)
            T
            U
            volume := by
    rw [hsplit] at hFTC
    linarith
  calc
    TS228.Goldbach.dirichletUnitPartialIntegral U -
        TS228.Goldbach.dirichletUnitPartialIntegral T
        =
      intervalIntegral
        (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
        T
        U
        volume := dirichletPartialIntegral_sub_eq_tail T U
    _ =
      dirichletTailPrimitive U - dirichletTailPrimitive T -
        intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume := htail
    _ =
      Real.cos T / T -
        Real.cos U / U -
          intervalIntegral
            (fun x : Real => Real.cos x / x ^ 2)
            T
            U
            volume := by
      unfold dirichletTailPrimitive
      field_simp [hT.ne', hU.ne']
      ring

/-- Exact evaluation of the positive inverse-square interval integral. -/
theorem inverseSquareIntervalIntegral
    (T U : Real)
    (hT : 0 < T)
    (hTU : T <= U) :
    intervalIntegral
      (fun x : Real => (1 : Real) / x ^ 2)
      T
      U
      volume =
      (1 : Real) / T - (1 : Real) / U := by
  have hU : 0 < U := lt_of_lt_of_le hT hTU
  let primitive : Real -> Real := fun x => -(1 : Real) / x
  have hderiv :
      forall x : Real, Set.Mem (Set.uIcc T U) x ->
        HasDerivAt primitive ((1 : Real) / x ^ 2) x := by
    intro x hx
    have hxpos : 0 < x :=
      positive_on_uIcc_of_left_pos hT hTU hx
    have hx0 : Not (x = 0) := ne_of_gt hxpos
    have hnum :
        HasDerivAt (fun _ : Real => -(1 : Real)) 0 x :=
      hasDerivAt_const x (-(1 : Real))
    have hden :
        HasDerivAt (fun y : Real => y) (1 : Real) x :=
      hasDerivAt_id x
    have hdiv := hnum.div hden hx0
    have hvalue :
        (1 : Real) / x ^ 2 =
          (0 * x - -(1 : Real) * 1) / x ^ 2 := by
      field_simp [hx0]
    simpa [primitive, hvalue] using hdiv
  have hint :
      IntervalIntegrable
        (fun x : Real => (1 : Real) / x ^ 2)
        volume
        T
        U :=
    one_over_square_intervalIntegrable T U hT hTU
  have hFTC :
      intervalIntegral
        (fun x : Real => (1 : Real) / x ^ 2)
        T
        U
        volume =
        primitive U - primitive T := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  unfold primitive
  field_simp [hT.ne', hU.ne']
  ring

/-- The residual integration-by-parts term is bounded by the inverse-square tail. -/
theorem cosOverSquareIntegral_abs_le
    (T U : Real)
    (hT : 0 < T)
    (hTU : T <= U) :
    |intervalIntegral
        (fun x : Real => Real.cos x / x ^ 2)
        T
        U
        volume| <=
      (1 : Real) / T - (1 : Real) / U := by
  have hmajorant :
      IntervalIntegrable
        (fun x : Real => (1 : Real) / x ^ 2)
        volume
        T
        U :=
    one_over_square_intervalIntegrable T U hT hTU
  have hbound :
      forall x : Real,
        norm (Real.cos x / x ^ 2) <=
          (1 : Real) / x ^ 2 := by
    intro x
    by_cases hx : x = 0
    case pos =>
      simp [hx]
    case neg =>
      have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx2pos]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one x) hx2pos.le
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le
      (a := T)
      (b := U)
      (f := fun x : Real => Real.cos x / x ^ 2)
      (g := fun x : Real => (1 : Real) / x ^ 2)
      (Filter.Eventually.of_forall hbound)
      hmajorant
  have hnonneg :
      0 <=
        intervalIntegral
          (fun x : Real => (1 : Real) / x ^ 2)
          T
          U
          volume := by
    exact
      intervalIntegral.integral_nonneg hTU
        (fun x hx => div_nonneg zero_le_one (sq_nonneg x))
  have hnorm_abs :
      |intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume| <=
        |intervalIntegral
          (fun x : Real => (1 : Real) / x ^ 2)
          T
          U
          volume| := by
    simpa [Real.norm_eq_abs] using hnorm
  have hmain :
      |intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume| <=
        intervalIntegral
          (fun x : Real => (1 : Real) / x ^ 2)
          T
          U
          volume :=
    hnorm_abs.trans_eq (abs_of_nonneg hnonneg)
  rw [inverseSquareIntervalIntegral T U hT hTU] at hmain
  exact hmain

private theorem boundaryTerms_abs_le
    (T U : Real)
    (hT : 0 < T)
    (hTU : T <= U) :
    |Real.cos T / T - Real.cos U / U| <=
      (1 : Real) / T + (1 : Real) / U := by
  have hU : 0 < U := lt_of_lt_of_le hT hTU
  calc
    |Real.cos T / T - Real.cos U / U|
        <= |Real.cos T / T| + |Real.cos U / U| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add (Real.cos T / T) (-(Real.cos U / U))
    _ = |Real.cos T| / T + |Real.cos U| / U := by
          rw [abs_div, abs_of_pos hT, abs_div, abs_of_pos hU]
    _ <= (1 : Real) / T + (1 : Real) / U := by
          exact
            add_le_add
              (div_le_div_of_nonneg_right
                (Real.abs_cos_le_one T)
                hT.le)
              (div_le_div_of_nonneg_right
                (Real.abs_cos_le_one U)
                hU.le)

/-- The TS239 quantitative Dirichlet tail bound. -/
theorem dirichletTailBound :
    TS239.Goldbach.DirichletTailBoundStatement := by
  intro T U hT hTU
  have hU : 0 < U := lt_of_lt_of_le hT hTU
  have htail := dirichletTailIntegral_eq T U hT hTU
  rw [htail]
  have hboundary := boundaryTerms_abs_le T U hT hTU
  have hresidual := cosOverSquareIntegral_abs_le T U hT hTU
  calc
    |Real.cos T / T - Real.cos U / U -
        intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume|
        <=
      |Real.cos T / T - Real.cos U / U| +
        |intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add
                (Real.cos T / T - Real.cos U / U)
                (-
                  intervalIntegral
                    (fun x : Real => Real.cos x / x ^ 2)
                    T
                    U
                    volume)
    _ <=
      ((1 : Real) / T + (1 : Real) / U) +
        ((1 : Real) / T - (1 : Real) / U) := by
          exact add_le_add hboundary hresidual
    _ = 2 / T := by
          field_simp [hT.ne', hU.ne']
          ring

/-- Ledger recording the TS240 tail-bound discharge. -/
structure DirichletTailBoundDischargeLedger where
  ts239_direct_probe :
    TS239.Goldbach.DirichletCutoffAPIDirectRouteProbeLedger

  partial_integral_tail_decomposition :
    forall T U : Real,
      TS228.Goldbach.dirichletUnitPartialIntegral U -
          TS228.Goldbach.dirichletUnitPartialIntegral T =
        intervalIntegral
          (fun x : Real => TS213.Goldbach.sineDirichletKernel 1 x)
          T
          U
          volume

  tail_primitive_has_deriv :
    forall x : Real, Not (x = 0) ->
      HasDerivAt
        dirichletTailPrimitive
        (TS213.Goldbach.sineDirichletKernel 1 x +
          Real.cos x / x ^ 2)
        x

  finite_tail_identity :
    forall T U : Real, 0 < T -> T <= U ->
      TS228.Goldbach.dirichletUnitPartialIntegral U -
          TS228.Goldbach.dirichletUnitPartialIntegral T =
        Real.cos T / T -
          Real.cos U / U -
            intervalIntegral
              (fun x : Real => Real.cos x / x ^ 2)
              T
              U
              volume

  inverse_square_integral :
    forall T U : Real, 0 < T -> T <= U ->
      intervalIntegral
        (fun x : Real => (1 : Real) / x ^ 2)
        T
        U
        volume =
        (1 : Real) / T - (1 : Real) / U

  residual_bound :
    forall T U : Real, 0 < T -> T <= U ->
      |intervalIntegral
          (fun x : Real => Real.cos x / x ^ 2)
          T
          U
          volume| <=
        (1 : Real) / T - (1 : Real) / U

  dirichlet_tail_bound_statement : Prop
  dirichlet_tail_bound_statement_eq :
    dirichlet_tail_bound_statement =
      TS239.Goldbach.DirichletTailBoundStatement
  dirichlet_tail_bound_proved :
    dirichlet_tail_bound_statement

  cauchy_convergence_not_proved : True
  cutoff_value_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS240 discharge ledger. -/
noncomputable def dirichletTailBoundDischargeLedger :
    DirichletTailBoundDischargeLedger where
  ts239_direct_probe :=
    TS239.Goldbach.dirichletCutoffAPIDirectRouteProbeLedger
  partial_integral_tail_decomposition :=
    dirichletPartialIntegral_sub_eq_tail
  tail_primitive_has_deriv :=
    hasDerivAt_dirichletTailPrimitive
  finite_tail_identity :=
    dirichletTailIntegral_eq
  inverse_square_integral :=
    inverseSquareIntervalIntegral
  residual_bound :=
    cosOverSquareIntegral_abs_le
  dirichlet_tail_bound_statement :=
    TS239.Goldbach.DirichletTailBoundStatement
  dirichlet_tail_bound_statement_eq :=
    rfl
  dirichlet_tail_bound_proved :=
    dirichletTailBound
  cauchy_convergence_not_proved := True.intro
  cutoff_value_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS240. -/
def DirichletTailBoundDischargeTarget : Prop :=
  Nonempty DirichletTailBoundDischargeLedger

/-- TS240 target: the quantitative Dirichlet tail bound is discharged. -/
theorem dirichletTailBoundDischargeTarget :
    DirichletTailBoundDischargeTarget :=
  Nonempty.intro dirichletTailBoundDischargeLedger

end Goldbach
end TS240
