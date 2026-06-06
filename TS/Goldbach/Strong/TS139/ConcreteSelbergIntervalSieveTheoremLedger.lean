import Mathlib.Tactic
import TS.Goldbach.Strong.TS138.ConcreteSelbergIntervalMajorantFormulation

namespace TS139
namespace Goldbach

/-!
# TS139 - Concrete Selberg Interval Sieve Theorem Ledger

TS138 defines the concrete finite Selberg square majorant on the TS22 interval.

This sprint proves the first purely order-theoretic bridge toward the interval
sieve theorem: if every prime in the interval contributes at least `1` to the
square bracket, then the prime interval count is bounded by the natural ceiling
of the TS138 square sum.

The remaining analytic work is now local and explicit: prove that pointwise
prime lower-bound for the chosen level/support, and compare the resulting
majorant with the Brun-Titchmarsh ceiling.
-/

/--
Generic finite counting lemma.

If `f` is nonnegative on a finite set and is at least `1` on the filtered
points, then the cardinality of the filtered set is bounded by `sum f`.
-/
theorem finset_card_filter_cast_le_sum_of_pointwise
    {alpha : Type}
    (support : Finset alpha)
    (predicate : alpha -> Prop)
    [DecidablePred predicate]
    (f : alpha -> Rat)
    (h_nonneg : forall a : alpha,
      Membership.mem support a -> 0 <= f a)
    (h_one : forall a : alpha,
      Membership.mem support a -> predicate a -> 1 <= f a) :
    ((support.filter predicate).card : Rat) <=
      Finset.sum support f := by
  have hsum :
      Finset.sum support
          (fun a : alpha => if predicate a then (1 : Rat) else 0) <=
        Finset.sum support f := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hp : predicate a
    case pos =>
      simp [hp, h_one a ha hp]
    case neg =>
      simp [hp, h_nonneg a ha]
  have hcard :
      ((support.filter predicate).card : Rat) =
        Finset.sum support
          (fun a : alpha => if predicate a then (1 : Rat) else 0) := by
    rw [<- Finset.sum_filter]
    simp
  exact hcard.trans_le hsum

/--
Local pointwise condition needed for the TS138 square majorant to count primes.

This condition is deliberately separated from the finite summation bridge.  In
classical Selberg applications it is supplied by the admissibility of the
support relative to the primes being counted.
-/
def SelbergConcretePrimePointwiseMajorant
    (level x Q n : Nat) :
    Prop :=
  forall k : Nat,
    Membership.mem (TS138.Goldbach.selbergConcreteInterval x Q n) k ->
      Nat.Prime k ->
        (1 : Rat) <=
          TS138.Goldbach.selbergConcreteDivisorWeight level k ^
            (2 : Nat)

/--
Under the pointwise prime lower-bound, the rational square sum dominates the
prime interval count.
-/
theorem primeIntervalCard_cast_le_squareMajorantRat_of_pointwise
    (level x Q n : Nat)
    (hpointwise :
      SelbergConcretePrimePointwiseMajorant level x Q n) :
    ((TS22.Goldbach.primeIntervalCard n
        (TS15.Goldbach.intervalScale x Q) : Nat) : Rat) <=
      TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n := by
  have hsum :=
    finset_card_filter_cast_le_sum_of_pointwise
      (support := TS138.Goldbach.selbergConcreteInterval x Q n)
      (predicate := Nat.Prime)
      (f := fun k : Nat =>
        TS138.Goldbach.selbergConcreteDivisorWeight level k ^
          (2 : Nat))
      (h_nonneg := by
        intro k _hk
        exact sq_nonneg
          (TS138.Goldbach.selbergConcreteDivisorWeight level k))
      (h_one := by
        intro k hk hprime
        exact hpointwise k hk hprime)
  simpa [
    TS22.Goldbach.primeIntervalCard,
    TS138.Goldbach.selbergConcreteSquareMajorantRat,
    TS138.Goldbach.selbergConcreteInterval
  ] using hsum

/--
Under the pointwise prime lower-bound, the natural ceiling of the square sum
is a TS22 prime interval majorant.
-/
theorem primeIntervalCard_le_concreteMajorantValue_of_pointwise
    (level x Q n : Nat)
    (hpointwise :
      SelbergConcretePrimePointwiseMajorant level x Q n) :
    TS22.Goldbach.primeIntervalCard n
        (TS15.Goldbach.intervalScale x Q) <=
      TS138.Goldbach.selbergConcreteMajorantValue level x Q n := by
  have hrat :
      ((TS22.Goldbach.primeIntervalCard n
          (TS15.Goldbach.intervalScale x Q) : Nat) : Rat) <=
        TS138.Goldbach.selbergConcreteSquareMajorantRat level x Q n :=
    primeIntervalCard_cast_le_squareMajorantRat_of_pointwise
      level
      x
      Q
      n
      hpointwise
  have hreal :
      (TS22.Goldbach.primeIntervalCard n
          (TS15.Goldbach.intervalScale x Q) : Real) <=
        (TS138.Goldbach.selbergConcreteSquareMajorantRat
          level
          x
          Q
          n : Real) := by
    exact_mod_cast hrat
  have hceil :
      (TS138.Goldbach.selbergConcreteSquareMajorantRat
          level
          x
          Q
          n : Real) <=
        (TS138.Goldbach.selbergConcreteMajorantValue level x Q n :
          Real) := by
    unfold TS138.Goldbach.selbergConcreteMajorantValue
    exact Nat.le_ceil _
  exact Nat.cast_le.mp (hreal.trans hceil)

/--
Pointwise exact weight `1` implies the local square lower-bound.

This small lemma separates the future arithmetic/admissibility proof from the
finite interval counting argument above.
-/
theorem selbergConcretePrimePointwiseMajorant_of_weight_eq_one
    (level x Q n : Nat)
    (hweight : forall k : Nat,
      Membership.mem (TS138.Goldbach.selbergConcreteInterval x Q n) k ->
        Nat.Prime k ->
          TS138.Goldbach.selbergConcreteDivisorWeight level k = 1) :
    SelbergConcretePrimePointwiseMajorant level x Q n := by
  intro k hk hprime
  rw [hweight k hk hprime]
  norm_num

/--
Concrete interval sieve theorem data for the TS138 square majorant.

The field `pointwise_prime_square_lower_bound` is the remaining local
prime-admissibility input for the first TS138 inequality.
-/
structure ConcreteSelbergIntervalSieveTheorem
    (level : Nat) where
  hlevel :
    0 < level

  pointwise_prime_square_lower_bound :
    forall x Q n k : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      Membership.mem (TS138.Goldbach.selbergConcreteInterval x Q n) k ->
      Nat.Prime k ->
        (1 : Rat) <=
          TS138.Goldbach.selbergConcreteDivisorWeight level k ^
            (2 : Nat)

  pointwise_prime_admissibility_obligation :
    True

/-- A TS139 pointwise package supplies the TS30 interval sieve bound. -/
noncomputable def concreteSelbergSieveIntervalBound
    {level : Nat}
    (sieve : ConcreteSelbergIntervalSieveTheorem level) :
    TS30.Goldbach.SelbergSieveIntervalBound
      (TS137.Goldbach.concreteSelbergIntervalMajorant
        (TS138.Goldbach.concreteSelbergIntervalMajorantData
          level
          sieve.hlevel)) where
  sieve_bound := by
    intro x Q n hx hQ hn
    exact
      primeIntervalCard_le_concreteMajorantValue_of_pointwise
        level
        x
        Q
        n
        (by
          intro k hk hprime
          exact
            sieve.pointwise_prime_square_lower_bound
              x
              Q
              n
              k
              hx
              hQ
              hn
              hk
              hprime)

/--
The remaining budget comparison for the explicit TS138 square majorant.
-/
structure ConcreteSelbergSquareBudgetComparison
    (level : Nat) where
  majorant_le_budget :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
      TS138.Goldbach.selbergConcreteMajorantValue level x Q n <=
        TS22.Goldbach.brunTitchmarshCeilBudget x Q

  brun_titchmarsh_budget_comparison_obligation :
    True

/--
TS139 closes the interval-sieve-bound field of TS138 from the pointwise prime
lower-bound, leaving only the explicit Brun-Titchmarsh budget comparison.
-/
noncomputable def concreteSelbergSquareMajorantProofs
    {level : Nat}
    (sieve : ConcreteSelbergIntervalSieveTheorem level)
    (budget : ConcreteSelbergSquareBudgetComparison level) :
    TS138.Goldbach.ConcreteSelbergSquareMajorantProofs level where
  hlevel :=
    sieve.hlevel
  sieve_bound := by
    intro x Q n hx hQ hn
    exact
      primeIntervalCard_le_concreteMajorantValue_of_pointwise
        level
        x
        Q
        n
        (by
          intro k hk hprime
          exact
            sieve.pointwise_prime_square_lower_bound
              x
              Q
              n
              k
              hx
              hQ
              hn
              hk
              hprime)
  majorant_le_budget := by
    intro x Q n hx hQ hn
    exact budget.majorant_le_budget x Q n hx hQ hn
  interval_sieve_theorem_obligation :=
    sieve.pointwise_prime_admissibility_obligation
  brun_titchmarsh_budget_comparison_obligation :=
    budget.brun_titchmarsh_budget_comparison_obligation

/--
TS139 ledger: once the pointwise interval sieve theorem and budget comparison
are supplied, the TS138 square-majorant ledger is populated.
-/
structure ConcreteSelbergIntervalSieveTheoremLedger
    (level : Nat) where
  sieve :
    ConcreteSelbergIntervalSieveTheorem level

  budget :
    ConcreteSelbergSquareBudgetComparison level

  squareMajorantProofs :
    TS138.Goldbach.ConcreteSelbergSquareMajorantProofs level

  square_majorant_proofs_eq :
    squareMajorantProofs =
      concreteSelbergSquareMajorantProofs sieve budget

  squareMajorantLedger :
    TS138.Goldbach.ConcreteSelbergSquareMajorantLedger level

  interval_sieve_bound :
    TS30.Goldbach.SelbergSieveIntervalBound
      (TS137.Goldbach.concreteSelbergIntervalMajorant
        (TS138.Goldbach.concreteSelbergIntervalMajorantData
          level
          sieve.hlevel))

  pointwise_prime_admissibility_obligation :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Build the TS139 ledger from the two remaining concrete analytic packages. -/
noncomputable def concreteSelbergIntervalSieveTheoremLedger
    {level : Nat}
    (sieve : ConcreteSelbergIntervalSieveTheorem level)
    (budget : ConcreteSelbergSquareBudgetComparison level) :
    ConcreteSelbergIntervalSieveTheoremLedger level where
  sieve := sieve
  budget := budget
  squareMajorantProofs :=
    concreteSelbergSquareMajorantProofs sieve budget
  square_majorant_proofs_eq := rfl
  squareMajorantLedger :=
    TS138.Goldbach.concreteSelbergSquareMajorantLedger
      (concreteSelbergSquareMajorantProofs sieve budget)
  interval_sieve_bound :=
    concreteSelbergSieveIntervalBound sieve
  pointwise_prime_admissibility_obligation :=
    sieve.pointwise_prime_admissibility_obligation
  brun_titchmarsh_budget_comparison_obligation :=
    budget.brun_titchmarsh_budget_comparison_obligation

/--
Bridge target: the pointwise interval sieve theorem plus the budget comparison
populate the TS139 ledger.
-/
def ConcreteSelbergIntervalSieveTheoremBridgeTarget : Prop :=
  forall level : Nat,
    ConcreteSelbergIntervalSieveTheorem level ->
      ConcreteSelbergSquareBudgetComparison level ->
        Nonempty (ConcreteSelbergIntervalSieveTheoremLedger level)

/-- The TS139 bridge target is populated. -/
theorem concreteSelbergIntervalSieveTheoremBridgeTarget :
    ConcreteSelbergIntervalSieveTheoremBridgeTarget := by
  intro level sieve budget
  exact
    Nonempty.intro
      (concreteSelbergIntervalSieveTheoremLedger sieve budget)

/-- A TS139 ledger supplies the TS99 Selberg weight infrastructure. -/
def selbergSieveWeightInfrastructure_of_intervalSieveTheorem
    {level : Nat}
    (H : ConcreteSelbergIntervalSieveTheoremLedger level) :
    TS99.Goldbach.SelbergSieveWeightInfrastructure :=
  TS138.Goldbach.selbergSieveWeightInfrastructure_of_squareMajorant
    H.squareMajorantLedger

/-- A TS139 ledger supplies the TS97 final Brun-Titchmarsh input. -/
def brunTitchmarshFinalInputLedger_of_intervalSieveTheorem
    {level : Nat}
    (H : ConcreteSelbergIntervalSieveTheoremLedger level) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedger :=
  TS138.Goldbach.brunTitchmarshFinalInputLedger_of_squareMajorant
    H.squareMajorantLedger

/-- A fully supplied TS139 ledger feeds the TS99 target. -/
theorem selbergSieveWeightInfrastructureTarget_of_intervalSieveTheoremTarget
    (H : Nonempty (Sigma fun level : Nat =>
      ConcreteSelbergIntervalSieveTheoremLedger level)) :
    TS99.Goldbach.SelbergSieveWeightInfrastructureTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level package =>
          exact
            Nonempty.intro
              (selbergSieveWeightInfrastructure_of_intervalSieveTheorem
                package)

/-- A fully supplied TS139 ledger feeds the TS97 target. -/
theorem brunTitchmarshFinalInputLedgerTarget_of_intervalSieveTheoremTarget
    (H : Nonempty (Sigma fun level : Nat =>
      ConcreteSelbergIntervalSieveTheoremLedger level)) :
    TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget := by
  cases H with
  | intro h =>
      cases h with
      | mk level package =>
          exact
            Nonempty.intro
              (brunTitchmarshFinalInputLedger_of_intervalSieveTheorem
                package)

/-- TS139 keeps the TS138 bridge target available. -/
theorem concreteSelbergSquareMajorantBridgeTarget :
    TS138.Goldbach.ConcreteSelbergSquareMajorantBridgeTarget :=
  TS138.Goldbach.concreteSelbergSquareMajorantBridgeTarget

end Goldbach
end TS139
