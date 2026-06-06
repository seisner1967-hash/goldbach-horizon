import Mathlib.Tactic
import TS.Goldbach.Strong.TS137.ConcreteSelbergIntervalMajorantInterface

namespace TS138
namespace Goldbach

/-!
# TS138 - Concrete Selberg Interval Majorant Formulation

TS137 names the analytic interval-majorant interface needed by TS30/TS136.

This sprint instantiates the data side of that interface with the concrete
finite Selberg square majorant attached to the TS136 optimal reconstructed
weights.  It does not prove the interval sieve theorem or the comparison with
the Brun-Titchmarsh ceiling.  Instead it names those two analytic proof fields
for this concrete majorant and shows that supplying them populates the TS137
ledger.
-/

/-- The closed natural interval used by the TS22 prime-counting window. -/
def selbergConcreteInterval
    (x Q n : Nat) :
    Finset Nat :=
  Finset.Icc n (n + TS15.Goldbach.intervalScale x Q)

/--
The inner Selberg divisor weight at an integer `k`.

This is the finite square-bracket expression
`sum_{d | k, d <= level} lambda_d`, where `lambda_d` is the TS136 optimal
reconstructed Selberg weight.
-/
def selbergConcreteDivisorWeight
    (level k : Nat) :
    Rat :=
  Finset.sum (TS122.Goldbach.selbergOptimizationSupport level) fun d =>
    if Dvd.dvd d k then
      TS136.Goldbach.selbergOptimalIntervalWeight level d
    else
      0

/--
The concrete rational Selberg square sum over the TS22 interval.

This is the finite expression
`sum_{n <= k <= n+h} (sum_{d | k} lambda_d)^2`.
-/
def selbergConcreteSquareMajorantRat
    (level x Q n : Nat) :
    Rat :=
  Finset.sum (selbergConcreteInterval x Q n) fun k =>
    selbergConcreteDivisorWeight level k ^ (2 : Nat)

/--
The natural-valued TS30 majorant obtained by taking the ceiling of the rational
Selberg square sum.
-/
noncomputable def selbergConcreteMajorantValue
    (level x Q n : Nat) :
    Nat :=
  Nat.ceil (selbergConcreteSquareMajorantRat level x Q n : Real)

/-- The main term recorded in the TS137 rational decomposition. -/
def selbergConcreteMainTerm
    (level x Q n : Nat) :
    Rat :=
  selbergConcreteSquareMajorantRat level x Q n

/-- The remainder term recorded in the TS137 rational decomposition. -/
def selbergConcreteErrorTerm
    (_level _x _Q _n : Nat) :
    Rat :=
  0

/-- The rational majorant recorded in the TS137 data object. -/
def selbergConcreteMajorantRat
    (level x Q n : Nat) :
    Rat :=
  selbergConcreteSquareMajorantRat level x Q n

/-- The TS137 rational decomposition is definitionally the square sum plus `0`. -/
theorem selbergConcreteMajorantRat_formula
    (level x Q n : Nat) :
    selbergConcreteMajorantRat level x Q n =
      selbergConcreteMainTerm level x Q n +
        selbergConcreteErrorTerm level x Q n := by
  simp [
    selbergConcreteMajorantRat,
    selbergConcreteMainTerm,
    selbergConcreteErrorTerm,
  ]

/-- The concrete TS138 error term is nonnegative. -/
theorem selbergConcreteErrorTerm_nonnegative
    (level x Q n : Nat) :
    0 <= selbergConcreteErrorTerm level x Q n := by
  simp [selbergConcreteErrorTerm]

/--
Concrete TS137 data attached to the finite Selberg square majorant.

The data side is now explicit.  The two genuine analytic inequalities remain
separate proof fields below.
-/
noncomputable def concreteSelbergIntervalMajorantData
    (level : Nat)
    (hlevel : 0 < level) :
    TS137.Goldbach.ConcreteSelbergIntervalMajorantData where
  level := level
  hlevel := hlevel
  majorantValue := selbergConcreteMajorantValue level
  mainTerm := selbergConcreteMainTerm level
  errorTerm := selbergConcreteErrorTerm level
  majorantRat := selbergConcreteMajorantRat level
  majorant_rat_formula := by
    intro x Q n
    exact selbergConcreteMajorantRat_formula level x Q n
  error_nonnegative := by
    intro x Q n
    exact selbergConcreteErrorTerm_nonnegative level x Q n
  denominator_evaluation_obligation := True.intro
  interval_remainder_obligation := True.intro

/--
The concrete analytic obligations remaining for the TS138 square majorant.

These are precisely the TS137 proof fields specialized to the explicit
`selbergConcreteMajorantValue`.
-/
structure ConcreteSelbergSquareMajorantProofs
    (level : Nat) where
  hlevel :
    0 < level

  sieve_bound :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      TS22.Goldbach.primeIntervalCard n
          (TS15.Goldbach.intervalScale x Q) <=
        selbergConcreteMajorantValue level x Q n

  majorant_le_budget :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      selbergConcreteMajorantValue level x Q n <=
        TS22.Goldbach.brunTitchmarshCeilBudget x Q

  interval_sieve_theorem_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- TS138 concrete proofs specialize to the TS137 proof package. -/
noncomputable def concreteSelbergIntervalMajorantProofs
    {level : Nat}
    (proofs : ConcreteSelbergSquareMajorantProofs level) :
    TS137.Goldbach.ConcreteSelbergIntervalMajorantProofs
      (concreteSelbergIntervalMajorantData level proofs.hlevel) where
  sieve_bound := by
    intro x Q n hx hQ hn
    exact proofs.sieve_bound x Q n hx hQ hn
  majorant_le_budget := by
    intro x Q n hx hQ hn
    exact proofs.majorant_le_budget x Q n hx hQ hn
  interval_sieve_theorem_obligation :=
    proofs.interval_sieve_theorem_obligation
  brun_titchmarsh_budget_comparison_obligation :=
    proofs.brun_titchmarsh_budget_comparison_obligation

/--
Concrete square-majorant ledger for TS138.

Supplying the two analytic inequalities for the explicit square majorant
populates the TS137 ledger and hence the TS99/TS97 route.
-/
structure ConcreteSelbergSquareMajorantLedger
    (level : Nat) where
  proofs :
    ConcreteSelbergSquareMajorantProofs level

  data :
    TS137.Goldbach.ConcreteSelbergIntervalMajorantData

  data_eq :
    data =
      concreteSelbergIntervalMajorantData level proofs.hlevel

  concreteLedger :
    TS137.Goldbach.ConcreteSelbergIntervalMajorantLedger data

  square_majorant_formula :
    forall x Q n : Nat,
      data.majorantRat x Q n =
        selbergConcreteSquareMajorantRat level x Q n

  error_nonnegative :
    forall x Q n : Nat,
      0 <= data.errorTerm x Q n

  selberg_square_formula_ready :
    True

  interval_sieve_theorem_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Build the TS138 ledger from the two concrete analytic proof fields. -/
noncomputable def concreteSelbergSquareMajorantLedger
    {level : Nat}
    (proofs : ConcreteSelbergSquareMajorantProofs level) :
    ConcreteSelbergSquareMajorantLedger level where
  proofs := proofs
  data :=
    concreteSelbergIntervalMajorantData level proofs.hlevel
  data_eq := rfl
  concreteLedger :=
    TS137.Goldbach.concreteSelbergIntervalMajorantLedger
      (concreteSelbergIntervalMajorantData level proofs.hlevel)
      (concreteSelbergIntervalMajorantProofs proofs)
  square_majorant_formula := by
    intro x Q n
    rfl
  error_nonnegative := by
    intro x Q n
    exact selbergConcreteErrorTerm_nonnegative level x Q n
  selberg_square_formula_ready := True.intro
  interval_sieve_theorem_obligation :=
    proofs.interval_sieve_theorem_obligation
  brun_titchmarsh_budget_comparison_obligation :=
    proofs.brun_titchmarsh_budget_comparison_obligation

/--
Bridge target: concrete TS138 square-majorant proofs populate the TS137
interval-majorant ledger.
-/
def ConcreteSelbergSquareMajorantBridgeTarget : Prop :=
  forall level : Nat,
    ConcreteSelbergSquareMajorantProofs level ->
      Nonempty (ConcreteSelbergSquareMajorantLedger level)

/-- The TS138 bridge target is populated. -/
theorem concreteSelbergSquareMajorantBridgeTarget :
    ConcreteSelbergSquareMajorantBridgeTarget := by
  intro level proofs
  exact
    Nonempty.intro
      (concreteSelbergSquareMajorantLedger proofs)

/-- A TS138 ledger supplies the TS99 Selberg weight infrastructure. -/
def selbergSieveWeightInfrastructure_of_squareMajorant
    {level : Nat}
    (H : ConcreteSelbergSquareMajorantLedger level) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure :=
  TS137.Goldbach.selbergSieveWeightInfrastructure_of_concreteIntervalMajorant
    H.concreteLedger

/-- A TS138 ledger supplies the TS97 final Brun-Titchmarsh input. -/
def brunTitchmarshFinalInputLedger_of_squareMajorant
    {level : Nat}
    (H : ConcreteSelbergSquareMajorantLedger level) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger :=
  TS137.Goldbach.brunTitchmarshFinalInputLedger_of_concreteIntervalMajorant
    H.concreteLedger

/-- A fully supplied TS138 ledger feeds the TS99 target. -/
theorem selbergSieveWeightInfrastructureTarget_of_squareMajorantTarget
    (H : Nonempty (Sigma fun level : Nat =>
      ConcreteSelbergSquareMajorantLedger level)) :
    TS99.Goldbach.SelbergSieveWeightInfrastructureTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level package =>
          exact
            Nonempty.intro
              (selbergSieveWeightInfrastructure_of_squareMajorant package)

/-- A fully supplied TS138 ledger feeds the TS97 target. -/
theorem brunTitchmarshFinalInputLedgerTarget_of_squareMajorantTarget
    (H : Nonempty (Sigma fun level : Nat =>
      ConcreteSelbergSquareMajorantLedger level)) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level package =>
          exact
            Nonempty.intro
              (brunTitchmarshFinalInputLedger_of_squareMajorant package)

/--
The prime interval count is bounded by the cardinality of its ambient interval.

This sanity lemma is not the Selberg sieve theorem; it only confirms that the
TS22 prime-counting window is the same finite interval used in TS138.
-/
theorem primeIntervalCard_le_concreteInterval_card
    (x Q n : Nat) :
    TS22.Goldbach.primeIntervalCard n
        (TS15.Goldbach.intervalScale x Q) <=
      (selbergConcreteInterval x Q n).card := by
  unfold TS22.Goldbach.primeIntervalCard
  unfold selbergConcreteInterval
  exact Finset.card_filter_le _ _

/-- TS138 keeps the TS137 bridge target available. -/
theorem concreteSelbergIntervalMajorantBridgeTarget :
    TS137.Goldbach.ConcreteSelbergIntervalMajorantBridgeTarget :=
  TS137.Goldbach.concreteSelbergIntervalMajorantBridgeTarget

end Goldbach
end TS138
