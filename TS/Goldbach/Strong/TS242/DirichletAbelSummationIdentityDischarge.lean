import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS241.DirichletCutoffCauchyConvergenceDischarge
import TS.Goldbach.Strong.TS232.DampedDirichletFubiniBridgeReduction

/-!
# TS242 - Dirichlet Abel Summation Identity Discharge

TS241 constructed the direct cutoff limit of the unit Dirichlet partial
integrals.  This sprint proves the finite Abel summation identity

`D_b(T) = exp(-b*T) * F(T) + b * int_0^T exp(-b*x) * F(x) dx`,

where `F(T) = int_0^T sin x / x dx` and
`D_b(T) = int_0^T exp(-b*x) * sin x / x dx`.

It also proves that the boundary term `exp(-b*T) * F(T)` tends to zero when
`b > 0`, using TS241 convergence and exponential decay.

No identification of the TS241 cutoff limit with `pi/2`, Abel-to-cutoff
bridge, cos-square value, `sinc^4` value, Plancherel evidence, or Goldbach
claim is made here.
-/

namespace TS242
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The Abel average term obtained after integration by parts. -/
noncomputable def dirichletAbelAverage (b T : Real) : Real :=
  b *
    intervalIntegral
      (fun x : Real =>
        Real.exp (-b * x) *
          TS228.Goldbach.dirichletUnitPartialIntegral x)
      0
      T
      volume

/-- Away from zero, the repository unit Dirichlet kernel is continuous. -/
theorem sineDirichletKernel_one_continuousAt_of_ne
    {x : Real}
    (hx : Not (x = 0)) :
    ContinuousAt
      (fun y : Real => TS213.Goldbach.sineDirichletKernel 1 y)
      x := by
  unfold TS213.Goldbach.sineDirichletKernel
  exact
    ((Real.continuous_sin.comp
      ((continuous_const.mul continuous_id))).continuousAt).div
      continuousAt_id
      hx

/--
The partial integral has the expected derivative away from zero.  The statement
deliberately avoids `x = 0`, where the repository kernel is represented by
field division and evaluates to zero.
-/
theorem hasDerivAt_dirichletUnitPartialIntegral_of_ne
    {x : Real}
    (hx : Not (x = 0)) :
    HasDerivAt
      TS228.Goldbach.dirichletUnitPartialIntegral
      (TS213.Goldbach.sineDirichletKernel 1 x)
      x := by
  unfold TS228.Goldbach.dirichletUnitPartialIntegral
  exact
    intervalIntegral.integral_hasDerivAt_right
      (TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable 0 x)
      (by
        unfold TS213.Goldbach.sineDirichletKernel
        exact
          ((Real.measurable_sin.comp
            ((measurable_const.mul measurable_id))).div
            measurable_id).aestronglyMeasurable.stronglyMeasurableAtFilter)
      (sineDirichletKernel_one_continuousAt_of_ne hx)

/-- The repository unit partial integral starts at zero. -/
theorem dirichletUnitPartialIntegral_zero :
    TS228.Goldbach.dirichletUnitPartialIntegral 0 = 0 := by
  simp [TS228.Goldbach.dirichletUnitPartialIntegral]

/-- A global Lipschitz estimate for the unit Dirichlet partial integral. -/
theorem dirichletUnitPartialIntegral_sub_abs_le
    (x y : Real) :
    |TS228.Goldbach.dirichletUnitPartialIntegral y -
        TS228.Goldbach.dirichletUnitPartialIntegral x| <=
      |y - x| := by
  have htail :
      TS228.Goldbach.dirichletUnitPartialIntegral y -
          TS228.Goldbach.dirichletUnitPartialIntegral x =
        intervalIntegral
          (fun t : Real => TS213.Goldbach.sineDirichletKernel 1 t)
          x
          y
          volume := by
    unfold TS228.Goldbach.dirichletUnitPartialIntegral
    exact
      intervalIntegral.integral_interval_sub_left
        (TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable 0 y)
        (TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable 0 x)
  rw [htail]
  have hbound :
      forall t : Real,
        (Set.uIoc x y) t ->
          norm (TS213.Goldbach.sineDirichletKernel 1 t) <=
            (1 : Real) := by
    intro t _ht
    simpa [Real.norm_eq_abs] using
      TS228.Goldbach.sineDirichletKernel_one_abs_le_one t
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x)
      (b := y)
      (C := (1 : Real))
      (f := fun t : Real => TS213.Goldbach.sineDirichletKernel 1 t)
      hbound
  simpa [Real.norm_eq_abs, abs_sub_comm] using hnorm

/-- The unit Dirichlet partial integral is 1-Lipschitz. -/
theorem dirichletUnitPartialIntegral_lipschitz :
    LipschitzWith 1 TS228.Goldbach.dirichletUnitPartialIntegral := by
  apply LipschitzWith.mk_one
  intro x y
  simpa [Real.dist_eq] using
    dirichletUnitPartialIntegral_sub_abs_le y x

/-- Continuity of the unit Dirichlet partial integral. -/
theorem dirichletUnitPartialIntegral_continuous :
    Continuous TS228.Goldbach.dirichletUnitPartialIntegral :=
  dirichletUnitPartialIntegral_lipschitz.continuous

/-- Derivative of the exponential damping factor. -/
theorem hasDerivAt_exp_neg_mul
    (b x : Real) :
    HasDerivAt
      (fun y : Real => Real.exp (-b * y))
      ((-b) * Real.exp (-b * x))
      x := by
  have hlin :
      HasDerivAt (fun y : Real => -b * y) (-b) x := by
    simpa using (hasDerivAt_id x).const_mul (-b)
  have h := hlin.exp
  convert h using 1
  ring

private theorem exp_neg_mul_derivative_intervalIntegrable
    (b T : Real) :
    IntervalIntegrable
      (fun x : Real => (-b) * Real.exp (-b * x))
      volume
      0
      T := by
  have hcont :
      ContinuousOn
        (fun x : Real => (-b) * Real.exp (-b * x))
        (Set.uIcc 0 T) := by
    fun_prop
  exact hcont.intervalIntegrable

private theorem exp_times_partial_intervalIntegrable
    (b T : Real) :
    IntervalIntegrable
      (fun x : Real =>
        Real.exp (-b * x) *
          TS228.Goldbach.dirichletUnitPartialIntegral x)
      volume
      0
      T := by
  have hcont :
      ContinuousOn
        (fun x : Real =>
          Real.exp (-b * x) *
            TS228.Goldbach.dirichletUnitPartialIntegral x)
        (Set.uIcc 0 T) := by
    exact
      ((by fun_prop :
        Continuous (fun x : Real => Real.exp (-b * x))).continuousOn).mul
        dirichletUnitPartialIntegral_continuous.continuousOn
  exact hcont.intervalIntegrable

/--
Finite Abel summation identity for the damped Dirichlet integral.

The derivative of `F` is used only on the open interval `(0,T)`, so no
derivative claim at the singular endpoint `0` is needed.
-/
theorem dampedPartialIntegral_eq_boundary_add_abelAverage
    (b T : Real)
    (_hb : 0 < b)
    (hT : 0 <= T) :
    TS232.Goldbach.dampedPartialIntegral b T =
      Real.exp (-b * T) *
        TS228.Goldbach.dirichletUnitPartialIntegral T +
          dirichletAbelAverage b T := by
  let u : Real -> Real := fun x => Real.exp (-b * x)
  let v : Real -> Real := TS228.Goldbach.dirichletUnitPartialIntegral
  let u' : Real -> Real := fun x => (-b) * Real.exp (-b * x)
  let v' : Real -> Real := fun x => TS213.Goldbach.sineDirichletKernel 1 x
  have hu : ContinuousOn u (Set.uIcc 0 T) := by
    dsimp [u]
    fun_prop
  have hv : ContinuousOn v (Set.uIcc 0 T) := by
    dsimp [v]
    exact dirichletUnitPartialIntegral_continuous.continuousOn
  have huderiv :
      forall x : Real,
        Set.Mem (Set.Ioo (min 0 T) (max 0 T)) x ->
          HasDerivAt u (u' x) x := by
    intro x _hx
    dsimp [u, u']
    exact hasDerivAt_exp_neg_mul b x
  have hvderiv :
      forall x : Real,
        Set.Mem (Set.Ioo (min 0 T) (max 0 T)) x ->
          HasDerivAt v (v' x) x := by
    intro x hx
    have hmin : min (0 : Real) T = 0 := min_eq_left hT
    have hxpos : 0 < x := by
      simpa [hmin] using hx.1
    dsimp [v, v']
    exact hasDerivAt_dirichletUnitPartialIntegral_of_ne (ne_of_gt hxpos)
  have hu' :
      IntervalIntegrable u' volume 0 T := by
    dsimp [u']
    exact exp_neg_mul_derivative_intervalIntegrable b T
  have hv' :
      IntervalIntegrable v' volume 0 T := by
    dsimp [v']
    exact TS228.Goldbach.sineDirichletKernel_one_intervalIntegrable 0 T
  have hIPP :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := 0)
      (b := T)
      (u := u)
      (v := v)
      (u' := u')
      (v' := v')
      hu
      hv
      huderiv
      hvderiv
      hu'
      hv'
  have hfactor :
      intervalIntegral
          (fun x : Real =>
            (-b) * Real.exp (-b * x) *
              TS228.Goldbach.dirichletUnitPartialIntegral x)
          0
          T
          volume =
        (-b) *
          intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                TS228.Goldbach.dirichletUnitPartialIntegral x)
            0
            T
            volume := by
    calc
      intervalIntegral
          (fun x : Real =>
            (-b) * Real.exp (-b * x) *
              TS228.Goldbach.dirichletUnitPartialIntegral x)
          0
          T
          volume =
        intervalIntegral
          (fun x : Real =>
            (-b) *
              (Real.exp (-b * x) *
                TS228.Goldbach.dirichletUnitPartialIntegral x))
          0
          T
          volume := by
            congr 1
            ext x
            ring
      _ =
        (-b) *
          intervalIntegral
            (fun x : Real =>
              Real.exp (-b * x) *
                TS228.Goldbach.dirichletUnitPartialIntegral x)
            0
            T
            volume := by
              rw [intervalIntegral.integral_const_mul]
  have hrewrite :
      intervalIntegral
          (fun x : Real =>
            Real.exp (-b * x) *
              TS213.Goldbach.sineDirichletKernel 1 x)
          0
          T
          volume =
        Real.exp (-b * T) *
          TS228.Goldbach.dirichletUnitPartialIntegral T +
          b *
            intervalIntegral
              (fun x : Real =>
                Real.exp (-b * x) *
                  TS228.Goldbach.dirichletUnitPartialIntegral x)
              0
              T
              volume := by
    have hIPP' := hIPP
    dsimp [u, v, u', v'] at hIPP'
    rw [hfactor] at hIPP'
    rw [dirichletUnitPartialIntegral_zero] at hIPP'
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hIPP'
  unfold TS232.Goldbach.dampedPartialIntegral
  unfold TS229.Goldbach.dampedDirichletKernel
  unfold dirichletAbelAverage
  simpa [mul_assoc] using hrewrite

/--
For each positive damping parameter, the Abel summation boundary term vanishes
at infinity.
-/
theorem dampedCutoffBoundary_tendsto_zero
    (b : Real)
    (hb : 0 < b) :
    Tendsto
      (fun T : Real =>
        Real.exp (-b * T) *
          TS228.Goldbach.dirichletUnitPartialIntegral T)
      atTop
      (nhds (0 : Real)) := by
  have hscale :
      Tendsto (fun T : Real => -b * T) atTop atBot := by
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hexp :
      Tendsto
        (fun T : Real => Real.exp (-b * T))
        atTop
        (nhds (0 : Real)) :=
    Real.tendsto_exp_atBot.comp hscale
  have hprod :=
    hexp.mul TS241.Goldbach.tendsto_dirichletCutoffLimit
  simpa using hprod

/-- Ledger recording the TS242 Abel summation identity discharge. -/
structure DirichletAbelSummationIdentityDischargeLedger where
  ts241_cauchy_convergence :
    TS241.Goldbach.DirichletCutoffCauchyConvergenceDischargeLedger

  abel_average_family :
    Real -> Real -> Real
  abel_average_family_eq :
    abel_average_family = dirichletAbelAverage

  partial_integral_zero :
    TS228.Goldbach.dirichletUnitPartialIntegral 0 = 0

  partial_integral_lipschitz :
    LipschitzWith 1 TS228.Goldbach.dirichletUnitPartialIntegral

  partial_integral_continuous :
    Continuous TS228.Goldbach.dirichletUnitPartialIntegral

  partial_integral_derivative_positive :
    forall x : Real, 0 < x ->
      HasDerivAt
        TS228.Goldbach.dirichletUnitPartialIntegral
        (TS213.Goldbach.sineDirichletKernel 1 x)
        x

  finite_abel_summation_identity :
    forall b T : Real, 0 < b -> 0 <= T ->
      TS232.Goldbach.dampedPartialIntegral b T =
        Real.exp (-b * T) *
          TS228.Goldbach.dirichletUnitPartialIntegral T +
            dirichletAbelAverage b T

  damped_cutoff_boundary_vanishing :
    forall b : Real, 0 < b ->
      Tendsto
        (fun T : Real =>
          Real.exp (-b * T) *
            TS228.Goldbach.dirichletUnitPartialIntegral T)
        atTop
        (nhds (0 : Real))

  cutoff_limit_value : Real
  cutoff_limit_tendsto :
    Tendsto
      TS228.Goldbach.dirichletUnitPartialIntegral
      atTop
      (nhds cutoff_limit_value)

  cutoff_value_pi_over_two_not_proved : True
  abel_identification_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS242 Abel summation identity ledger. -/
noncomputable def dirichletAbelSummationIdentityDischargeLedger :
    DirichletAbelSummationIdentityDischargeLedger where
  ts241_cauchy_convergence :=
    TS241.Goldbach.dirichletCutoffCauchyConvergenceDischargeLedger
  abel_average_family :=
    dirichletAbelAverage
  abel_average_family_eq := rfl
  partial_integral_zero :=
    dirichletUnitPartialIntegral_zero
  partial_integral_lipschitz :=
    dirichletUnitPartialIntegral_lipschitz
  partial_integral_continuous :=
    dirichletUnitPartialIntegral_continuous
  partial_integral_derivative_positive := by
    intro x hx
    exact hasDerivAt_dirichletUnitPartialIntegral_of_ne (ne_of_gt hx)
  finite_abel_summation_identity :=
    dampedPartialIntegral_eq_boundary_add_abelAverage
  damped_cutoff_boundary_vanishing :=
    dampedCutoffBoundary_tendsto_zero
  cutoff_limit_value :=
    TS241.Goldbach.dirichletCutoffLimit
  cutoff_limit_tendsto :=
    TS241.Goldbach.tendsto_dirichletCutoffLimit
  cutoff_value_pi_over_two_not_proved := True.intro
  abel_identification_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS242. -/
def DirichletAbelSummationIdentityDischargeTarget : Prop :=
  Nonempty DirichletAbelSummationIdentityDischargeLedger

/-- TS242 target: finite Abel summation and boundary vanishing are discharged. -/
theorem dirichletAbelSummationIdentityDischargeTarget :
    DirichletAbelSummationIdentityDischargeTarget :=
  Nonempty.intro dirichletAbelSummationIdentityDischargeLedger

end Goldbach
end TS242
