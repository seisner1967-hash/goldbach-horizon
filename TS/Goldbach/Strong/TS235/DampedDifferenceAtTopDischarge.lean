import Mathlib.Tactic
import TS.Goldbach.Strong.TS234.LaplaceBoundaryUniformLimitDischarge

/-!
# TS235 - Damped Difference AtTop Discharge

TS234 discharged the uniform vanishing of the integrated Laplace boundary term.
This sprint discharges the next TS232 obligation:

`TS232.Goldbach.DampedDifferenceAtTopStatement`.

The proof is deliberately short.  It uses:

* TS231: the finite Laplace sine formula with its boundary term;
* TS230: the arctangent primitive for `1 / (1 + s^2)`;
* TS234: the integrated boundary term tends to zero;
* TS233: the compact Fubini identity, eventually for `T >= 0`.

It does not prove the auxiliary high-damping bound, the corrected Fubini
execution statement, the damped Dirichlet evaluation target, any Abel-to-cutoff
bridge, or any final Dirichlet cutoff value.
-/

namespace TS235
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The TS231 boundary term in the exact syntactic form used by TS232. -/
noncomputable def laplaceBoundaryTerm (s T : Real) : Real :=
  Real.exp (-(s * T)) *
    (s * Real.sin T + Real.cos T) /
      (1 + s ^ 2)

/--
Integrating the TS231 finite Laplace formula over the parameter interval
rewrites the Laplace partial integral as an arctangent difference minus the
integrated boundary term.
-/
theorem laplaceParameterIntegral_eq_arctan_sub_boundary
    (b A T : Real) :
    intervalIntegral
        (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T)
        b
        A
        volume =
      (Real.arctan A - Real.arctan b) -
        intervalIntegral
          (fun s : Real => laplaceBoundaryTerm s T)
          b
          A
          volume := by
  have hmain :
      IntervalIntegrable
        (fun s : Real => (1 : Real) / (1 + s ^ 2))
        volume
        b
        A := by
    apply ContinuousOn.intervalIntegrable
    have hnum :
        ContinuousOn (fun s : Real => (1 : Real)) (Set.uIcc b A) :=
      continuousOn_const
    have hden :
        ContinuousOn (fun s : Real => 1 + s ^ 2) (Set.uIcc b A) := by
      fun_prop
    exact hnum.div hden
      (fun s hs => ne_of_gt (TS231.Goldbach.one_add_sq_pos s))
  have hboundary :
      IntervalIntegrable
        (fun s : Real => laplaceBoundaryTerm s T)
        volume
        b
        A := by
    apply ContinuousOn.intervalIntegrable
    unfold laplaceBoundaryTerm
    have hnum :
        ContinuousOn
          (fun s : Real =>
            Real.exp (-(s * T)) * (s * Real.sin T + Real.cos T))
          (Set.uIcc b A) := by
      fun_prop
    have hden :
        ContinuousOn (fun s : Real => 1 + s ^ 2) (Set.uIcc b A) := by
      fun_prop
    exact hnum.div hden
      (fun s hs => ne_of_gt (TS231.Goldbach.one_add_sq_pos s))
  calc
    intervalIntegral
        (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T)
        b
        A
        volume
        =
      intervalIntegral
        (fun s : Real =>
          (1 : Real) / (1 + s ^ 2) - laplaceBoundaryTerm s T)
        b
        A
        volume := by
          apply intervalIntegral.integral_congr
          intro s hs
          simpa [laplaceBoundaryTerm, div_eq_mul_inv, mul_comm, mul_left_comm,
            mul_assoc] using
            TS231.Goldbach.laplaceSinePartialIntegral_eq_boundary s T
    _ =
      intervalIntegral
          (fun s : Real => (1 : Real) / (1 + s ^ 2))
          b
          A
          volume -
        intervalIntegral
          (fun s : Real => laplaceBoundaryTerm s T)
          b
          A
          volume := by
            exact intervalIntegral.integral_sub hmain hboundary
    _ =
      (Real.arctan A - Real.arctan b) -
        intervalIntegral
          (fun s : Real => laplaceBoundaryTerm s T)
          b
          A
          volume := by
            rw [TS230.Goldbach.arctan_intervalIntegral_inv_one_add_sq b A]

/-- The damped difference tends to the arctangent difference at infinity. -/
theorem dampedDifferenceAtTop :
    TS232.Goldbach.DampedDifferenceAtTopStatement := by
  intro b A hb hA
  have hBoundary :
      Tendsto
        (fun T : Real =>
          intervalIntegral
            (fun s : Real => laplaceBoundaryTerm s T)
            b
            A
            volume)
        atTop
        (nhds (0 : Real)) := by
    simpa [laplaceBoundaryTerm, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using
      TS234.Goldbach.laplaceBoundaryUniformLimit b A hb hA
  have hParameter :
      Tendsto
        (fun T : Real =>
          intervalIntegral
            (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T)
            b
            A
            volume)
        atTop
        (nhds (Real.arctan A - Real.arctan b)) := by
    have hlim :
        Tendsto
          (fun T : Real =>
            (Real.arctan A - Real.arctan b) -
              intervalIntegral
                (fun s : Real => laplaceBoundaryTerm s T)
                b
                A
                volume)
          atTop
          (nhds ((Real.arctan A - Real.arctan b) - 0)) :=
      tendsto_const_nhds.sub hBoundary
    simpa using
      hlim.congr'
        (Eventually.of_forall fun T =>
          (laplaceParameterIntegral_eq_arctan_sub_boundary b A T).symm)
  have hFubini :
      Filter.Eventually
        (fun T : Real =>
          TS232.Goldbach.dampedPartialIntegral b T -
              TS232.Goldbach.dampedPartialIntegral A T =
            intervalIntegral
              (fun s : Real => TS230.Goldbach.laplaceSinePartialIntegral s T)
              b
              A
              volume)
        atTop := by
    filter_upwards [eventually_ge_atTop (0 : Real)] with T hT
    exact TS233.Goldbach.compactFubiniIdentity b A T hb hA hT
  exact hParameter.congr' (hFubini.mono fun T hT => hT.symm)

/-- Ledger recording the TS235 damped-difference discharge. -/
structure DampedDifferenceAtTopDischargeLedger where
  ts234_boundary_limit :
    TS234.Goldbach.LaplaceBoundaryUniformLimitDischargeLedger

  ts233_compact_fubini :
    TS233.Goldbach.CompactFubiniIdentityDischargeLedger

  ts230_arctan_tail :
    TS230.Goldbach.DampedDirichletEvaluationReductionEvidence

  ts231_laplace_transform :
    TS231.Goldbach.LaplaceSineTransformDischargeLedger

  damped_difference_atTop_statement : Prop
  damped_difference_atTop_statement_eq :
    damped_difference_atTop_statement =
      TS232.Goldbach.DampedDifferenceAtTopStatement
  damped_difference_atTop_proved :
    damped_difference_atTop_statement

  parameter_integral_decomposition_proved : True
  eventual_compact_fubini_used : True
  boundary_limit_used : True

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

/-- Concrete TS235 discharge ledger. -/
noncomputable def dampedDifferenceAtTopDischargeLedger :
    DampedDifferenceAtTopDischargeLedger where
  ts234_boundary_limit :=
    TS234.Goldbach.laplaceBoundaryUniformLimitDischargeLedger
  ts233_compact_fubini :=
    TS233.Goldbach.compactFubiniIdentityDischargeLedger
  ts230_arctan_tail :=
    TS230.Goldbach.dampedDirichletEvaluationReductionEvidence
  ts231_laplace_transform :=
    TS231.Goldbach.laplaceSineTransformDischargeLedger
  damped_difference_atTop_statement :=
    TS232.Goldbach.DampedDifferenceAtTopStatement
  damped_difference_atTop_statement_eq := rfl
  damped_difference_atTop_proved :=
    dampedDifferenceAtTop
  parameter_integral_decomposition_proved := True.intro
  eventual_compact_fubini_used := True.intro
  boundary_limit_used := True.intro
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

/-- Target proposition for TS235. -/
def DampedDifferenceAtTopDischargeTarget : Prop :=
  Nonempty DampedDifferenceAtTopDischargeLedger

/-- TS235 target: the damped difference atTop statement is discharged. -/
theorem dampedDifferenceAtTopDischargeTarget :
    DampedDifferenceAtTopDischargeTarget :=
  Nonempty.intro dampedDifferenceAtTopDischargeLedger

end Goldbach
end TS235
