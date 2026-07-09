import Mathlib.Tactic
import TS.Goldbach.Strong.TS240.DirichletTailBoundDischarge

/-!
# TS241 - Dirichlet Cutoff Cauchy Convergence Discharge

TS240 proved the quantitative direct tail estimate

`|F(U) - F(T)| <= 2 / T` for `0 < T <= U`,

where `F(T) = int_0^T sin x / x dx` is the repository unit Dirichlet
partial integral.  This sprint uses that estimate to prove that `F` is a
Cauchy net along `atTop`, hence converges in `Real`.

The limit is constructed as a canonical real number, but its value is not
identified as `Real.pi / 2` here.  No Abel-to-cutoff bridge, cos-square value,
`sinc^4` value, Plancherel evidence, or Goldbach claim is made.
-/

namespace TS241
namespace Goldbach

open Filter

/-- The direct cutoff partial integrals have some real limit at `+infty`. -/
def DirichletUnitPartialIntegralConvergesStatement : Prop :=
  Exists fun L : Real =>
    Tendsto
      TS228.Goldbach.dirichletUnitPartialIntegral
      atTop
      (nhds L)

private theorem two_div_le_two_div_of_le
    {N m : Real}
    (hN : 0 < N)
    (hm : N <= m) :
    (2 : Real) / m <= 2 / N := by
  have hmpos : 0 < m := lt_of_lt_of_le hN hm
  have hone : (1 : Real) / m <= (1 : Real) / N := by
    exact one_div_le_one_div_of_le hN hm
  have hmul := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : Real) <= 2)
  simpa [div_eq_mul_inv] using hmul

private theorem two_div_four_div_lt
    {epsilon : Real}
    (hepsilon : 0 < epsilon) :
    (2 : Real) / (4 / epsilon) < epsilon := by
  have hcalc : (2 : Real) / (4 / epsilon) = epsilon / 2 := by
    field_simp [hepsilon.ne']
    ring
  rw [hcalc]
  linarith

/-- The TS228 unit Dirichlet partial integral is Cauchy along `atTop`. -/
theorem dirichletUnitPartialIntegral_cauchySeq :
    CauchySeq TS228.Goldbach.dirichletUnitPartialIntegral := by
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  let N : Real := 4 / epsilon
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have htail_small : (2 : Real) / N < epsilon := by
    dsimp [N]
    exact two_div_four_div_lt hepsilon
  refine Exists.intro N ?_
  intro m hm n hn
  have hmpos : 0 < m := lt_of_lt_of_le hNpos hm
  have hnpos : 0 < n := lt_of_lt_of_le hNpos hn
  cases le_total m n with
  | inl hmn =>
    have htail :
        |TS228.Goldbach.dirichletUnitPartialIntegral m -
            TS228.Goldbach.dirichletUnitPartialIntegral n| <=
          (2 : Real) / m := by
      have h :=
        TS240.Goldbach.dirichletTailBound m n hmpos hmn
      simpa [abs_sub_comm] using h
    have hmono : (2 : Real) / m <= 2 / N :=
      two_div_le_two_div_of_le hNpos hm
    have hdist :
        dist
          (TS228.Goldbach.dirichletUnitPartialIntegral m)
          (TS228.Goldbach.dirichletUnitPartialIntegral n) <=
            (2 : Real) / m := by
      simpa [Real.dist_eq] using htail
    exact lt_of_le_of_lt (le_trans hdist hmono) htail_small
  | inr hnm =>
    have htail :
        |TS228.Goldbach.dirichletUnitPartialIntegral m -
            TS228.Goldbach.dirichletUnitPartialIntegral n| <=
          (2 : Real) / n := by
      exact TS240.Goldbach.dirichletTailBound n m hnpos hnm
    have hmono : (2 : Real) / n <= 2 / N :=
      two_div_le_two_div_of_le hNpos hn
    have hdist :
        dist
          (TS228.Goldbach.dirichletUnitPartialIntegral m)
          (TS228.Goldbach.dirichletUnitPartialIntegral n) <=
            (2 : Real) / n := by
      simpa [Real.dist_eq] using htail
    exact lt_of_le_of_lt (le_trans hdist hmono) htail_small

/-- Existence of a real cutoff limit for the unit Dirichlet partial integrals. -/
theorem dirichletUnitPartialIntegralConverges :
    DirichletUnitPartialIntegralConvergesStatement := by
  unfold DirichletUnitPartialIntegralConvergesStatement
  exact cauchySeq_tendsto_of_complete dirichletUnitPartialIntegral_cauchySeq

/-- The canonical cutoff limit extracted from Cauchy convergence. -/
noncomputable def dirichletCutoffLimit : Real :=
  Classical.choose dirichletUnitPartialIntegralConverges

/-- The unit Dirichlet partial integrals tend to the canonical cutoff limit. -/
theorem tendsto_dirichletCutoffLimit :
    Tendsto
      TS228.Goldbach.dirichletUnitPartialIntegral
      atTop
      (nhds dirichletCutoffLimit) :=
  Classical.choose_spec dirichletUnitPartialIntegralConverges

/-- Ledger recording the TS241 Cauchy convergence discharge. -/
structure DirichletCutoffCauchyConvergenceDischargeLedger where
  ts240_tail_bound :
    TS240.Goldbach.DirichletTailBoundDischargeLedger

  tail_bound_input :
    TS239.Goldbach.DirichletTailBoundStatement

  partial_integral_cauchySeq_proved :
    CauchySeq TS228.Goldbach.dirichletUnitPartialIntegral

  cutoff_convergence_statement : Prop
  cutoff_convergence_statement_eq :
    cutoff_convergence_statement =
      DirichletUnitPartialIntegralConvergesStatement
  cutoff_convergence_proved :
    cutoff_convergence_statement

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

/-- Concrete TS241 discharge ledger. -/
noncomputable def dirichletCutoffCauchyConvergenceDischargeLedger :
    DirichletCutoffCauchyConvergenceDischargeLedger where
  ts240_tail_bound :=
    TS240.Goldbach.dirichletTailBoundDischargeLedger
  tail_bound_input :=
    TS240.Goldbach.dirichletTailBound
  partial_integral_cauchySeq_proved :=
    dirichletUnitPartialIntegral_cauchySeq
  cutoff_convergence_statement :=
    DirichletUnitPartialIntegralConvergesStatement
  cutoff_convergence_statement_eq :=
    rfl
  cutoff_convergence_proved :=
    dirichletUnitPartialIntegralConverges
  cutoff_limit_value :=
    dirichletCutoffLimit
  cutoff_limit_tendsto :=
    tendsto_dirichletCutoffLimit
  cutoff_value_pi_over_two_not_proved := True.intro
  abel_identification_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS241. -/
def DirichletCutoffCauchyConvergenceDischargeTarget : Prop :=
  Nonempty DirichletCutoffCauchyConvergenceDischargeLedger

/-- TS241 target: the unit Dirichlet partial integral has a real cutoff limit. -/
theorem dirichletCutoffCauchyConvergenceDischargeTarget :
    DirichletCutoffCauchyConvergenceDischargeTarget :=
  Nonempty.intro dirichletCutoffCauchyConvergenceDischargeLedger

end Goldbach
end TS241
