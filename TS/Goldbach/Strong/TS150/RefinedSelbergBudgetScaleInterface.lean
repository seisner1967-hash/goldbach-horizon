import Mathlib.Tactic
import TS.Goldbach.Strong.TS140.LargePrimeAdmissibility
import TS.Goldbach.Strong.TS149.SelbergDivisorEnvelopeJordanRefinement

namespace TS150
namespace Goldbach

/-!
# TS150 - Refined Selberg Budget Scale Interface

TS149 proves the unconditional rational estimate

`squareMajorant <= intervalLength / D + (level / D)^2`.

This sprint packages that expression as the refined Selberg budget, proves the
monotone bridge from the TS138 ceiling majorant to the ceiling of the refined
budget, and isolates the remaining Brun-Titchmarsh comparison as a single
parametric contract.

No growth claim for `D(level)` and no final choice of `level` is made here.
When the scale contract and the TS140 large-prime admissibility package are
both supplied, TS150 constructs the complete TS139 interval-sieve ledger and
therefore exposes the TS99 and TS97 outputs.
-/

/-- Rational TS149 upper budget, independent of the interval left endpoint. -/
def refinedSelbergBudgetRat
    (level x Q : Nat) :
    Rat :=
  ((TS15.Goldbach.intervalScale x Q + 1 : Nat) : Rat) *
      (1 / TS122.Goldbach.selbergOptimizationDenominator level) +
    ((level : Rat) /
      TS122.Goldbach.selbergOptimizationDenominator level) ^ 2

/-- Natural ceiling of the refined rational Selberg budget. -/
noncomputable def refinedSelbergBudgetCeil
    (level x Q : Nat) :
    Nat :=
  Nat.ceil (refinedSelbergBudgetRat level x Q : Real)

/-- TS149 supplies the rational square-majorant bound in named TS150 form. -/
theorem selbergConcreteSquareMajorantRat_le_refinedSelbergBudgetRat
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n <=
      refinedSelbergBudgetRat level x Q := by
  exact TS149.Goldbach.selbergConcreteSquareMajorantRat_le_refinedBudget
    level x Q n hlevel

/-- The TS138 natural majorant is bounded by the refined-budget ceiling. -/
theorem selbergConcreteMajorantValue_le_refinedSelbergBudgetCeil
    (level x Q n : Nat)
    (hlevel : 0 < level) :
    TS138.Goldbach.selbergConcreteMajorantValue level x Q n <=
      refinedSelbergBudgetCeil level x Q := by
  unfold TS138.Goldbach.selbergConcreteMajorantValue
  unfold refinedSelbergBudgetCeil
  apply Nat.ceil_mono
  exact_mod_cast
    selbergConcreteSquareMajorantRat_le_refinedSelbergBudgetRat
      level x Q n hlevel

/--
Local comparison contract between the refined Selberg ceiling and the TS22
Brun-Titchmarsh ceiling.
-/
def RefinedSelbergBudgetLeBrunTitchmarsh
    (level x Q : Nat) :
    Prop :=
  refinedSelbergBudgetCeil level x Q <=
    TS22.Goldbach.brunTitchmarshCeilBudget x Q

/-- A local scale comparison immediately bounds the concrete TS138 majorant. -/
theorem selbergConcreteMajorantValue_le_brunTitchmarshCeilBudget
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (hscale : RefinedSelbergBudgetLeBrunTitchmarsh level x Q) :
    TS138.Goldbach.selbergConcreteMajorantValue level x Q n <=
      TS22.Goldbach.brunTitchmarshCeilBudget x Q := by
  exact le_trans
    (selbergConcreteMajorantValue_le_refinedSelbergBudgetCeil
      level x Q n hlevel)
    hscale

/--
Uniform scale contract in exactly the parameter regime consumed by TS139.

The interval endpoint `n` is deliberately absent: the refined budget itself
depends only on `level`, `x`, and `Q`.
-/
structure RefinedSelbergBudgetScaleComparison
    (level : Nat) where
  hlevel :
    0 < level

  refined_budget_le_brun_titchmarsh :
    forall x Q : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
        RefinedSelbergBudgetLeBrunTitchmarsh level x Q

  level_selection_obligation :
    True

  refined_budget_comparison_obligation :
    True

/-- The TS150 scale contract supplies the TS139 budget-comparison package. -/
noncomputable def concreteSelbergSquareBudgetComparison
    {level : Nat}
    (scale : RefinedSelbergBudgetScaleComparison level) :
    TS139.Goldbach.ConcreteSelbergSquareBudgetComparison level where
  majorant_le_budget := by
    intro x Q n hx hQ _hn
    exact
      selbergConcreteMajorantValue_le_brunTitchmarshCeilBudget
        level
        x
        Q
        n
        scale.hlevel
        (scale.refined_budget_le_brun_titchmarsh x Q hx hQ)
  brun_titchmarsh_budget_comparison_obligation :=
    scale.refined_budget_comparison_obligation

/--
TS140 admissibility plus the TS150 scale comparison populate the full TS139
interval-sieve ledger.
-/
noncomputable def concreteSelbergIntervalSieveTheoremLedger
    {level : Nat}
    (admissibility :
      TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem level)
    (scale : RefinedSelbergBudgetScaleComparison level) :
    TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremLedger level :=
  TS139.Goldbach.concreteSelbergIntervalSieveTheoremLedger
    (TS140.Goldbach.concreteSelbergIntervalSieveTheorem admissibility)
    (concreteSelbergSquareBudgetComparison scale)

/-- The combined TS150 package exposes the TS99 Selberg infrastructure. -/
def selbergSieveWeightInfrastructure
    {level : Nat}
    (H : TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremLedger level) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure :=
  TS139.Goldbach.selbergSieveWeightInfrastructure_of_intervalSieveTheorem H

/-- The combined TS150 package exposes the TS97 Brun-Titchmarsh input. -/
def brunTitchmarshFinalInputLedger
    {level : Nat}
    (H : TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremLedger level) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger :=
  TS139.Goldbach.brunTitchmarshFinalInputLedger_of_intervalSieveTheorem H

/-- TS150 ledger recording the complete parametric scale bridge. -/
structure RefinedSelbergBudgetScaleLedger
    (level : Nat) where
  admissibility :
    TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem level

  scale :
    RefinedSelbergBudgetScaleComparison level

  intervalSieveLedger :
    TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremLedger level

  interval_sieve_ledger_eq :
    intervalSieveLedger =
      concreteSelbergIntervalSieveTheoremLedger admissibility scale

  weightInfrastructure :
    TS99.Goldbach.SelbergSieveWeightInfrastructure

  brunTitchmarshInput :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger

  level_selection_obligation :
    True

  refined_budget_comparison_obligation :
    True

/-- Build the TS150 ledger from admissibility and scale comparison data. -/
noncomputable def refinedSelbergBudgetScaleLedger
    {level : Nat}
    (admissibility :
      TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem level)
    (scale : RefinedSelbergBudgetScaleComparison level) :
    RefinedSelbergBudgetScaleLedger level where
  admissibility := admissibility
  scale := scale
  intervalSieveLedger :=
    concreteSelbergIntervalSieveTheoremLedger admissibility scale
  interval_sieve_ledger_eq := rfl
  weightInfrastructure :=
    selbergSieveWeightInfrastructure
      (concreteSelbergIntervalSieveTheoremLedger admissibility scale)
  brunTitchmarshInput :=
    brunTitchmarshFinalInputLedger
      (concreteSelbergIntervalSieveTheoremLedger admissibility scale)
  level_selection_obligation :=
    scale.level_selection_obligation
  refined_budget_comparison_obligation :=
    scale.refined_budget_comparison_obligation

/--
Bridge target: once the geometric admissibility and refined scale comparison
are supplied at one level, the complete TS150 ledger is populated.
-/
def RefinedSelbergBudgetScaleBridgeTarget : Prop :=
  forall level : Nat,
    TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem level ->
      RefinedSelbergBudgetScaleComparison level ->
        Nonempty (RefinedSelbergBudgetScaleLedger level)

/-- The TS150 bridge target is populated. -/
theorem refinedSelbergBudgetScaleBridgeTarget :
    RefinedSelbergBudgetScaleBridgeTarget := by
  intro level admissibility scale
  exact Nonempty.intro
    (refinedSelbergBudgetScaleLedger admissibility scale)

end Goldbach
end TS150
