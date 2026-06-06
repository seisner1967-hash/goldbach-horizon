import Mathlib.Tactic
import TS.Goldbach.Strong.TS140.LargePrimeAdmissibility

namespace TS141
namespace Goldbach

/-!
# TS141 - Concrete Selberg Square Majorant Expansion

TS138 defines the concrete interval square majorant

`sum_k (sum_{d | k} lambda_d)^2`.

TS139 and TS140 use this square majorant to bound prime counts under a
large-prime admissibility condition.  This sprint prepares the remaining
budget comparison by expanding the square and moving to pair-first order:

`sum_{d1,d2} lambda_d1 lambda_d2 * #{k in interval | lcm(d1,d2) | k}`.

No asymptotic estimate for the multiple count is proved here.
-/

/-- The local Selberg divisor term in the TS138 square bracket. -/
def selbergConcreteDivisorTerm
    (level k d : Nat) :
    Rat :=
  if Dvd.dvd d k then
    TS136.Goldbach.selbergOptimalIntervalWeight level d
  else
    0

/-- The pair contribution after expanding a local square bracket. -/
def selbergConcretePairTerm
    (level k d1 d2 : Nat) :
    Rat :=
  selbergConcreteDivisorTerm level k d1 *
    selbergConcreteDivisorTerm level k d2

/-- Count interval points divisible by `lcm(d1,d2)`. -/
def selbergConcreteLcmMultiplicity
    (x Q n d1 d2 : Nat) :
    Nat :=
  ((TS138.Goldbach.selbergConcreteInterval x Q n).filter fun k =>
    Dvd.dvd (Nat.lcm d1 d2) k).card

/-- The pair-first lcm expansion of the TS138 rational square majorant. -/
def selbergConcreteLcmExpandedMajorantRat
    (level x Q n : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
    Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
      TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
        TS136.Goldbach.selbergOptimalIntervalWeight level d2 *
          (selbergConcreteLcmMultiplicity x Q n d1 d2 : Rat)

/-- The TS138 divisor weight is the sum of the local divisor terms. -/
theorem selbergConcreteDivisorWeight_eq_sum_divisorTerm
    (level k : Nat) :
    TS138.Goldbach.selbergConcreteDivisorWeight level k =
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
        selbergConcreteDivisorTerm level k d := by
  rfl

/-- Expand one local square bracket into a double sum over the support. -/
theorem selbergConcreteDivisorWeight_sq_expand_double
    (level k : Nat) :
    TS138.Goldbach.selbergConcreteDivisorWeight level k ^ (2 : Nat) =
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
          selbergConcretePairTerm level k d1 d2 := by
  unfold TS138.Goldbach.selbergConcreteDivisorWeight
  rw [pow_two]
  unfold selbergConcretePairTerm
  unfold selbergConcreteDivisorTerm
  exact
    Finset.sum_mul_sum
      (TS122.Goldbach.selbergOptimizationSupport level)
      (TS122.Goldbach.selbergOptimizationSupport level)
      (fun d =>
        if Dvd.dvd d k then
          TS136.Goldbach.selbergOptimalIntervalWeight level d
        else
          0)
      (fun d =>
        if Dvd.dvd d k then
          TS136.Goldbach.selbergOptimalIntervalWeight level d
        else
          0)

/-- Expand the concrete square majorant and move to pair-first order. -/
theorem selbergConcreteSquareMajorantRat_expand_pairFirst
    (level x Q n : Nat) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n =
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
          Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n) fun k =>
            selbergConcretePairTerm level k d1 d2 := by
  unfold TS138.Goldbach.selbergConcreteSquareMajorantRat
  simp_rw [selbergConcreteDivisorWeight_sq_expand_double]
  calc
    Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n)
        (fun k =>
          Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
            (fun d1 =>
              Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
                (fun d2 => selbergConcretePairTerm level k d1 d2))) =
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        (fun d1 =>
          Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n)
            (fun k =>
              Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
                (fun d2 => selbergConcretePairTerm level k d1 d2))) := by
        rw [Finset.sum_comm]
    _ =
      Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
        (fun d1 =>
          Finset.sum (TS122.Goldbach.selbergOptimizationSupport level)
            (fun d2 =>
              Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n)
                (fun k => selbergConcretePairTerm level k d1 d2))) := by
        apply Finset.sum_congr rfl
        intro d1 _hd1
        rw [Finset.sum_comm]

/-- Divisibility by `d1` and `d2` is the same as divisibility by their lcm. -/
theorem divisorPair_filter_eq_lcm_filter
    (d1 d2 k : Nat) :
    (Dvd.dvd d1 k /\ Dvd.dvd d2 k) <->
      Dvd.dvd (Nat.lcm d1 d2) k := by
  exact (Nat.lcm_dvd_iff (m := d1) (n := d2) (k := k)).symm

/-- The pointwise pair contribution is an lcm-divisibility indicator. -/
theorem selbergConcretePairTerm_eq_lcmIndicator
    (level k d1 d2 : Nat) :
    selbergConcretePairTerm level k d1 d2 =
      if Dvd.dvd (Nat.lcm d1 d2) k then
        TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
          TS136.Goldbach.selbergOptimalIntervalWeight level d2
      else
        0 := by
  unfold selbergConcretePairTerm
  unfold selbergConcreteDivisorTerm
  by_cases h1 : Dvd.dvd d1 k
  case pos =>
    by_cases h2 : Dvd.dvd d2 k
    case pos =>
      have hlcm :
          Dvd.dvd (Nat.lcm d1 d2) k :=
        Nat.lcm_dvd h1 h2
      simp [h1, h2, hlcm]
    case neg =>
      have hnot_lcm :
          Not (Dvd.dvd (Nat.lcm d1 d2) k) := by
        intro hlcm
        exact h2 ((Nat.lcm_dvd_iff.mp hlcm).2)
      simp [h1, h2, hnot_lcm]
  case neg =>
    have hnot_lcm :
        Not (Dvd.dvd (Nat.lcm d1 d2) k) := by
      intro hlcm
      exact h1 ((Nat.lcm_dvd_iff.mp hlcm).1)
    simp [h1, hnot_lcm]

/-- Sum a fixed pair contribution over the interval as an lcm multiple count. -/
theorem selbergConcretePairSum_eq_lcmMultiplicity
    (level x Q n d1 d2 : Nat) :
    (Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n) fun k =>
        selbergConcretePairTerm level k d1 d2) =
      TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
        TS136.Goldbach.selbergOptimalIntervalWeight level d2 *
          (selbergConcreteLcmMultiplicity x Q n d1 d2 : Rat) := by
  calc
    Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n)
        (fun k => selbergConcretePairTerm level k d1 d2) =
      Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n)
        (fun k =>
          if Dvd.dvd (Nat.lcm d1 d2) k then
            TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
              TS136.Goldbach.selbergOptimalIntervalWeight level d2
          else
            0) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact selbergConcretePairTerm_eq_lcmIndicator level k d1 d2
    _ =
      Finset.sum
        ((TS138.Goldbach.selbergConcreteInterval x Q n).filter fun k =>
          Dvd.dvd (Nat.lcm d1 d2) k)
        (fun _k =>
          TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
            TS136.Goldbach.selbergOptimalIntervalWeight level d2) := by
        exact
          (Finset.sum_filter
            (s := TS138.Goldbach.selbergConcreteInterval x Q n)
            (p := fun k => Dvd.dvd (Nat.lcm d1 d2) k)
            (f := fun _k =>
              TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
                TS136.Goldbach.selbergOptimalIntervalWeight level d2)).symm
    _ =
      (selbergConcreteLcmMultiplicity x Q n d1 d2 : Rat) *
        (TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
          TS136.Goldbach.selbergOptimalIntervalWeight level d2) := by
        simp [selbergConcreteLcmMultiplicity]
    _ =
      TS136.Goldbach.selbergOptimalIntervalWeight level d1 *
        TS136.Goldbach.selbergOptimalIntervalWeight level d2 *
          (selbergConcreteLcmMultiplicity x Q n d1 d2 : Rat) := by
        ring

/-- The concrete square majorant equals its pair-first lcm expansion. -/
theorem selbergConcreteSquareMajorantRat_expand_lcm
    (level x Q n : Nat) :
    TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n =
      selbergConcreteLcmExpandedMajorantRat level x Q n := by
  rw [selbergConcreteSquareMajorantRat_expand_pairFirst]
  unfold selbergConcreteLcmExpandedMajorantRat
  apply Finset.sum_congr rfl
  intro d1 _hd1
  apply Finset.sum_congr rfl
  intro d2 _hd2
  exact selbergConcretePairSum_eq_lcmMultiplicity level x Q n d1 d2

/--
TS141 ledger: the TS138 square majorant has been expanded to pair-first lcm
form.  Estimating the lcm multiplicity count remains the next interval
analysis input.
-/
structure ConcreteSelbergSquareMajorantExpansionLedger
    (level : Nat) where
  pair_first_expansion :
    forall x Q n : Nat,
      TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n =
        Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d1 =>
          Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d2 =>
            Finset.sum (TS138.Goldbach.selbergConcreteInterval x Q n) fun k =>
              selbergConcretePairTerm level k d1 d2

  lcm_expansion :
    forall x Q n : Nat,
      TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n =
        selbergConcreteLcmExpandedMajorantRat level x Q n

  lcm_multiple_count_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Concrete TS141 ledger for any support level. -/
def concreteSelbergSquareMajorantExpansionLedger
    (level : Nat) :
    ConcreteSelbergSquareMajorantExpansionLedger level where
  pair_first_expansion := by
    intro x Q n
    exact selbergConcreteSquareMajorantRat_expand_pairFirst level x Q n
  lcm_expansion := by
    intro x Q n
    exact selbergConcreteSquareMajorantRat_expand_lcm level x Q n
  lcm_multiple_count_obligation := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/-- Bridge target: the TS141 expansion ledger is populated. -/
def ConcreteSelbergSquareMajorantExpansionBridgeTarget : Prop :=
  forall level : Nat,
    Nonempty (ConcreteSelbergSquareMajorantExpansionLedger level)

/-- The TS141 bridge target is populated. -/
theorem concreteSelbergSquareMajorantExpansionBridgeTarget :
    ConcreteSelbergSquareMajorantExpansionBridgeTarget := by
  intro level
  exact
    Nonempty.intro
      (concreteSelbergSquareMajorantExpansionLedger level)

/-- TS141 keeps the TS140 bridge target available. -/
theorem largePrimeAdmissibilityBridgeTarget :
    TS140.Goldbach.LargePrimeAdmissibilityBridgeTarget :=
  TS140.Goldbach.largePrimeAdmissibilityBridgeTarget

end Goldbach
end TS141
