import Mathlib.Tactic
import TS.Goldbach.Strong.TS233.CompactFubiniIdentityDischarge

/-!
# TS234 - Laplace Boundary Uniform Limit Discharge

TS233 discharged the compact Fubini identity isolated by TS232.  This sprint
discharges the next TS232 obligation: the integrated TS231 boundary term
vanishes as `T -> +infty`, uniformly for the Laplace parameter on each compact
interval `[b, A]` with `0 < b < A`.

The proof uses a direct uniform bound by a constant multiple of `exp(-b*T)`.
It does not prove the damped-difference limit, the auxiliary high-damping
bound, the corrected Fubini execution statement, any Abel-to-cutoff bridge, or
any final Dirichlet cutoff value.
-/

namespace TS234
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The TS231 boundary kernel viewed as a two-variable function. -/
noncomputable def laplaceBoundaryKernel (s T : Real) : Real :=
  Real.exp (-(s * T)) *
    ((s * Real.sin T + Real.cos T) / (1 + s ^ 2))

/--
Pointwise uniform bound on the TS231 boundary kernel over `s in [b, A]`.

The denominator is at least `1`, the trigonometric coefficient is bounded by
`A + 1`, and `exp(-s*T) <= exp(-b*T)` for `0 <= T` and `b <= s`.
-/
theorem laplaceBoundaryKernel_abs_le
    (b A s T : Real)
    (hb : 0 < b)
    (hA : b < A)
    (hT : 0 <= T)
    (hs : Set.Mem (Set.uIoc b A) s) :
    |laplaceBoundaryKernel s T| <=
      Real.exp (-(b * T)) * (A + 1) := by
  have hsIcc : Set.Mem (Set.Icc b A) s := by
    have hsUcc : Set.Mem (Set.uIcc b A) s :=
      Set.uIoc_subset_uIcc hs
    simpa [Set.uIcc_of_le hA.le] using hsUcc
  have hbs : b <= s := hsIcc.1
  have hsA : s <= A := hsIcc.2
  have hspos : 0 < s := lt_of_lt_of_le hb hbs
  have hApos : 0 < A := lt_trans hb hA
  have hA1_nonneg : 0 <= A + 1 := by
    nlinarith
  have hsin : |Real.sin T| <= (1 : Real) :=
    Real.abs_sin_le_one T
  have hcos : |Real.cos T| <= (1 : Real) :=
    Real.abs_cos_le_one T
  have hs_abs : |s| = s :=
    abs_of_pos hspos
  have hnum :
      |s * Real.sin T + Real.cos T| <= A + 1 := by
    calc
      |s * Real.sin T + Real.cos T|
          <= |s * Real.sin T| + |Real.cos T| := abs_add _ _
      _ = |s| * |Real.sin T| + |Real.cos T| := by
        rw [abs_mul]
      _ <= A + 1 := by
        rw [hs_abs]
        nlinarith [hsA, hsin, hcos, abs_nonneg (Real.sin T),
          abs_nonneg (Real.cos T)]
  have hden_pos : 0 < (1 + s ^ 2 : Real) :=
    TS231.Goldbach.one_add_sq_pos s
  have hden_ge_one : (1 : Real) <= 1 + s ^ 2 := by
    nlinarith [sq_nonneg s]
  have hcoeff :
      |(s * Real.sin T + Real.cos T) / (1 + s ^ 2)| <= A + 1 := by
    have hdiv_le :
        |s * Real.sin T + Real.cos T| / (1 + s ^ 2) <=
          |s * Real.sin T + Real.cos T| := by
      have hone_div_le :
          (1 : Real) / (1 + s ^ 2) <= 1 := by
        have hbase :
            (1 : Real) / (1 + s ^ 2) <= (1 : Real) / 1 :=
          one_div_le_one_div_of_le zero_lt_one hden_ge_one
        simpa using hbase
      calc
        |s * Real.sin T + Real.cos T| / (1 + s ^ 2)
            =
          |s * Real.sin T + Real.cos T| *
            ((1 : Real) / (1 + s ^ 2)) := by
              ring
        _ <= |s * Real.sin T + Real.cos T| * 1 := by
              exact mul_le_mul_of_nonneg_left hone_div_le
                (abs_nonneg (s * Real.sin T + Real.cos T))
        _ = |s * Real.sin T + Real.cos T| := by
              ring
    rw [abs_div, abs_of_pos hden_pos]
    exact hdiv_le.trans hnum
  have hmul : b * T <= s * T :=
    mul_le_mul_of_nonneg_right hbs hT
  have hneg : -(s * T) <= -(b * T) := by
    linarith
  have hexp_le :
      Real.exp (-(s * T)) <= Real.exp (-(b * T)) :=
    Real.exp_le_exp.mpr hneg
  unfold laplaceBoundaryKernel
  rw [abs_mul, abs_of_pos (Real.exp_pos (-(s * T)))]
  calc
    Real.exp (-(s * T)) *
        |(s * Real.sin T + Real.cos T) / (1 + s ^ 2)|
        <= Real.exp (-(s * T)) * (A + 1) := by
          exact mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos _).le
    _ <= Real.exp (-(b * T)) * (A + 1) := by
          exact mul_le_mul_of_nonneg_right hexp_le hA1_nonneg

/-- Bound the interval integral of the boundary kernel by the uniform majorant. -/
theorem laplaceBoundaryIntegral_abs_le
    (b A T : Real)
    (hb : 0 < b)
    (hA : b < A)
    (hT : 0 <= T) :
    |intervalIntegral
        (fun s : Real => laplaceBoundaryKernel s T)
        b
        A
        volume| <=
      (Real.exp (-(b * T)) * (A + 1)) * |A - b| := by
  have hbound :
      forall s : Real,
        Set.Mem (Set.uIoc b A) s ->
          norm (laplaceBoundaryKernel s T) <=
            Real.exp (-(b * T)) * (A + 1) := by
    intro s hs
    simpa [Real.norm_eq_abs] using
      laplaceBoundaryKernel_abs_le b A s T hb hA hT hs
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b)
      (b := A)
      (C := Real.exp (-(b * T)) * (A + 1))
      (f := fun s : Real => laplaceBoundaryKernel s T)
      hbound
  simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using hnorm

/-- The scalar uniform majorant tends to zero as `T -> +infty`. -/
theorem laplaceBoundaryMajorant_tendsto_zero
    (b A : Real)
    (hb : 0 < b) :
    Tendsto
      (fun T : Real =>
        (Real.exp (-(b * T)) * (A + 1)) * |A - b|)
      atTop
      (nhds (0 : Real)) := by
  have hExp :
      Tendsto (fun T : Real => Real.exp (-(b * T)))
        atTop
        (nhds (0 : Real)) := by
    have hlin :
        Tendsto (fun T : Real => (-b) * T) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hExp0 :
        Tendsto (fun T : Real => Real.exp ((-b) * T))
          atTop
          (nhds (0 : Real)) :=
      Real.tendsto_exp_atBot.comp hlin
    simpa [neg_mul] using hExp0
  have hmul :
      Tendsto
        (fun T : Real =>
          (Real.exp (-(b * T)) * (A + 1)) * |A - b|)
        atTop
        (nhds ((0 * (A + 1)) * |A - b|)) := by
    exact (hExp.mul tendsto_const_nhds).mul tendsto_const_nhds
  simpa using hmul

/-- The integrated TS231 boundary term vanishes uniformly over compact `s`-ranges. -/
theorem laplaceBoundaryUniformLimit :
    TS232.Goldbach.LaplaceBoundaryUniformLimitStatement := by
  intro b A hb hA
  have hAbs :
      Tendsto
        (fun T : Real =>
          |intervalIntegral
            (fun s : Real => laplaceBoundaryKernel s T)
            b
            A
            volume|)
        atTop
        (nhds (0 : Real)) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds
        (laplaceBoundaryMajorant_tendsto_zero b A hb)
        ?_
        ?_
    next =>
      exact Eventually.of_forall fun T => abs_nonneg _
    next =>
      filter_upwards [eventually_ge_atTop (0 : Real)] with T hT
      exact laplaceBoundaryIntegral_abs_le b A T hb hA hT
  have hmain :
      Tendsto
        (fun T : Real =>
          intervalIntegral
            (fun s : Real => laplaceBoundaryKernel s T)
            b
            A
            volume)
        atTop
        (nhds (0 : Real)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hAbs
  simpa [laplaceBoundaryKernel, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hmain

/-- Ledger recording the TS234 uniform boundary discharge. -/
structure LaplaceBoundaryUniformLimitDischargeLedger where
  ts233_compact_fubini :
    TS233.Goldbach.CompactFubiniIdentityDischargeLedger

  laplace_boundary_uniform_limit_statement : Prop
  laplace_boundary_uniform_limit_statement_eq :
    laplace_boundary_uniform_limit_statement =
      TS232.Goldbach.LaplaceBoundaryUniformLimitStatement
  laplace_boundary_uniform_limit_proved :
    laplace_boundary_uniform_limit_statement

  boundary_kernel_defined : True
  pointwise_uniform_bound_proved : True
  integral_uniform_bound_proved : True
  scalar_majorant_vanishing_proved : True

  damped_difference_atTop_not_proved : True
  auxiliary_damping_uniform_bound_not_proved : True
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

/-- Concrete TS234 discharge ledger. -/
noncomputable def laplaceBoundaryUniformLimitDischargeLedger :
    LaplaceBoundaryUniformLimitDischargeLedger where
  ts233_compact_fubini :=
    TS233.Goldbach.compactFubiniIdentityDischargeLedger
  laplace_boundary_uniform_limit_statement :=
    TS232.Goldbach.LaplaceBoundaryUniformLimitStatement
  laplace_boundary_uniform_limit_statement_eq := rfl
  laplace_boundary_uniform_limit_proved := laplaceBoundaryUniformLimit
  boundary_kernel_defined := True.intro
  pointwise_uniform_bound_proved := True.intro
  integral_uniform_bound_proved := True.intro
  scalar_majorant_vanishing_proved := True.intro
  damped_difference_atTop_not_proved := True.intro
  auxiliary_damping_uniform_bound_not_proved := True.intro
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

/-- Target proposition for TS234. -/
def LaplaceBoundaryUniformLimitDischargeTarget : Prop :=
  Nonempty LaplaceBoundaryUniformLimitDischargeLedger

/-- TS234 target: the Laplace boundary uniform limit is discharged. -/
theorem laplaceBoundaryUniformLimitDischargeTarget :
    LaplaceBoundaryUniformLimitDischargeTarget :=
  Nonempty.intro laplaceBoundaryUniformLimitDischargeLedger

end Goldbach
end TS234
