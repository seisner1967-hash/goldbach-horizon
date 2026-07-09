import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import TS.Goldbach.Strong.TS235.DampedDifferenceAtTopDischarge

/-!
# TS236 - Auxiliary Damping Uniform Bound Discharge

TS235 discharged the damped-difference limit isolated by TS232.  This sprint
discharges the final remaining TS232 auxiliary estimate:

`TS232.Goldbach.AuxiliaryDampingUniformBoundStatement`.

The estimate is the elementary high-damping bound

`|int_0^T exp(-A*x) * D_1(x) dx| <= 1 / A`

for `0 < A` and `0 <= T`.  It uses the TS228 bound `|D_1(x)| <= 1`,
then integrates the exponential majorant on `[0, T]`.

It does not prove the corrected Fubini execution statement, the damped
Dirichlet evaluation target, any Abel-to-cutoff bridge, or any final
Dirichlet cutoff value.
-/

namespace TS236
namespace Goldbach

open Filter MeasureTheory

/-- The finite integral of the exponential damping majorant on `[0, T]`. -/
theorem dampingMajorantIntegral_eq
    (A T : Real)
    (hA : Not (A = 0)) :
    intervalIntegral
        (fun x : Real => Real.exp ((-A) * x))
        0
        T
        volume =
      ((1 : Real) - Real.exp ((-A) * T)) / A := by
  have hderiv :
      forall x : Real,
        HasDerivAt
          (fun y : Real => Real.exp ((-A) * y) / (-A))
          (Real.exp ((-A) * x))
          x := by
    intro x
    have hlin :
        HasDerivAt (fun y : Real => (-A) * y) (-A) x := by
      simpa only [id_eq, one_mul, mul_one] using
        (hasDerivAt_id x).const_mul (-A)
    have hExp :=
      (Real.hasDerivAt_exp ((-A) * x)).comp x hlin
    have hdiv := hExp.div_const (-A)
    convert hdiv using 1
    field_simp [hA]
  calc
    intervalIntegral
        (fun x : Real => Real.exp ((-A) * x))
        0
        T
        volume
        =
      (Real.exp ((-A) * T) / (-A)) -
          (Real.exp ((-A) * 0) / (-A)) := by
        exact
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x hx => hderiv x)
            (by
              apply Continuous.intervalIntegrable
              fun_prop)
    _ = ((1 : Real) - Real.exp ((-A) * T)) / A := by
        field_simp [hA]
        ring

/-- The exponential majorant integral is bounded by `1 / A`. -/
theorem dampingMajorantIntegral_le_inv
    (A T : Real)
    (hA : 0 < A)
    (hT : 0 <= T) :
    intervalIntegral
        (fun x : Real => Real.exp ((-A) * x))
        0
        T
        volume <=
      (1 : Real) / A := by
  rw [dampingMajorantIntegral_eq A T hA.ne']
  have hexp_le_one : Real.exp ((-A) * T) <= 1 := by
    have hnonpos : (-A) * T <= 0 := by nlinarith
    simpa using (Real.exp_le_one_iff).mpr hnonpos
  have hnum : (1 : Real) - Real.exp ((-A) * T) <= 1 := by
    linarith [Real.exp_pos ((-A) * T)]
  exact div_le_div_of_nonneg_right hnum hA.le

/-- Pointwise high-damping domination of the damped Dirichlet kernel. -/
theorem dampedDirichletKernel_norm_le_exp
    (A x : Real) :
    norm (TS229.Goldbach.dampedDirichletKernel A x) <=
      Real.exp ((-A) * x) := by
  have hkernel :
      |TS213.Goldbach.sineDirichletKernel 1 x| <= (1 : Real) :=
    TS228.Goldbach.sineDirichletKernel_one_abs_le_one x
  unfold TS229.Goldbach.dampedDirichletKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos ((-A) * x))]
  calc
    Real.exp ((-A) * x) *
        |TS213.Goldbach.sineDirichletKernel 1 x|
        <= Real.exp ((-A) * x) * 1 := by
          exact mul_le_mul_of_nonneg_left hkernel (Real.exp_pos _).le
    _ = Real.exp ((-A) * x) := by ring

/-- The damped partial integral is bounded by the exponential majorant. -/
theorem dampedPartialIntegral_abs_le_majorant
    (A T : Real)
    (hT : 0 <= T) :
    |TS232.Goldbach.dampedPartialIntegral A T| <=
      intervalIntegral
        (fun x : Real => Real.exp ((-A) * x))
        0
        T
        volume := by
  unfold TS232.Goldbach.dampedPartialIntegral
  have hbound :
      forall x : Real,
        norm (TS229.Goldbach.dampedDirichletKernel A x) <=
          Real.exp ((-A) * x) := by
    intro x
    exact dampedDirichletKernel_norm_le_exp A x
  have hmajorant :
      IntervalIntegrable
        (fun x : Real => Real.exp ((-A) * x))
        volume
        0
        T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le
      (a := (0 : Real))
      (b := T)
      (f := fun x : Real => TS229.Goldbach.dampedDirichletKernel A x)
      (g := fun x : Real => Real.exp ((-A) * x))
      (Filter.Eventually.of_forall hbound)
      hmajorant
  have hnonneg :
      0 <=
        intervalIntegral
          (fun x : Real => Real.exp ((-A) * x))
          0
          T
          volume := by
    exact
      intervalIntegral.integral_nonneg hT
        (fun x hx => (Real.exp_pos ((-A) * x)).le)
  have hnorm_abs :
      |intervalIntegral
          (fun x : Real => TS229.Goldbach.dampedDirichletKernel A x)
          0
          T
          volume| <=
        |intervalIntegral
          (fun x : Real => Real.exp ((-A) * x))
          0
          T
          volume| := by
    simpa [Real.norm_eq_abs] using hnorm
  exact hnorm_abs.trans_eq (abs_of_nonneg hnonneg)

/-- The auxiliary high-damping bound from TS232. -/
theorem auxiliaryDampingUniformBound :
    TS232.Goldbach.AuxiliaryDampingUniformBoundStatement := by
  intro A T hA hT
  exact
    (dampedPartialIntegral_abs_le_majorant A T hT).trans
      (dampingMajorantIntegral_le_inv A T hA hT)

/-- Ledger recording the TS236 auxiliary damping discharge. -/
structure AuxiliaryDampingUniformBoundDischargeLedger where
  ts235_damped_difference :
    TS235.Goldbach.DampedDifferenceAtTopDischargeLedger

  auxiliary_damping_uniform_bound_statement : Prop
  auxiliary_damping_uniform_bound_statement_eq :
    auxiliary_damping_uniform_bound_statement =
      TS232.Goldbach.AuxiliaryDampingUniformBoundStatement
  auxiliary_damping_uniform_bound_proved :
    auxiliary_damping_uniform_bound_statement

  kernel_abs_bound_used : True
  exponential_majorant_integral_evaluated : True
  exponential_majorant_bound_proved : True

  corrected_fubini_execution_not_proved : True
  damped_dirichlet_evaluation_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  dirichlet_cutoff_value_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS236 discharge ledger. -/
noncomputable def auxiliaryDampingUniformBoundDischargeLedger :
    AuxiliaryDampingUniformBoundDischargeLedger where
  ts235_damped_difference :=
    TS235.Goldbach.dampedDifferenceAtTopDischargeLedger
  auxiliary_damping_uniform_bound_statement :=
    TS232.Goldbach.AuxiliaryDampingUniformBoundStatement
  auxiliary_damping_uniform_bound_statement_eq := rfl
  auxiliary_damping_uniform_bound_proved :=
    auxiliaryDampingUniformBound
  kernel_abs_bound_used := True.intro
  exponential_majorant_integral_evaluated := True.intro
  exponential_majorant_bound_proved := True.intro
  corrected_fubini_execution_not_proved := True.intro
  damped_dirichlet_evaluation_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  dirichlet_cutoff_value_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS236. -/
def AuxiliaryDampingUniformBoundDischargeTarget : Prop :=
  Nonempty AuxiliaryDampingUniformBoundDischargeLedger

/-- TS236 target: the auxiliary damping bound is discharged. -/
theorem auxiliaryDampingUniformBoundDischargeTarget :
    AuxiliaryDampingUniformBoundDischargeTarget :=
  Nonempty.intro auxiliaryDampingUniformBoundDischargeLedger

end Goldbach
end TS236
