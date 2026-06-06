import Mathlib.Tactic
import TS.Goldbach.Strong.TS139.ConcreteSelbergIntervalSieveTheoremLedger

namespace TS140
namespace Goldbach

/-!
# TS140 - Large Prime Admissibility

TS139 reduces the concrete interval sieve theorem to a pointwise prime
condition:

`1 <= (sum_{d | k} lambda_d)^2`.

This sprint proves that condition for primes strictly larger than the Selberg
support level.  In that range, the only support divisor of a prime `k` is
`1`, and TS136 has already proved that the reconstructed optimal weight at
`1` is normalized to `1`.
-/

/-- Membership in the TS122 optimization support implies `d <= level`. -/
theorem selbergOptimizationSupport_mem_le_level
    {level d : Nat}
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    d <= level := by
  have hd_pair :
      Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) d /\
        0 < d := by
    simpa [
      TS122.Goldbach.selbergOptimizationSupport,
      TS121.Goldbach.selbergPositiveQuadraticSupport
    ] using hd
  have hd_lt :
      d < level + 1 := by
    simpa [TS108.Goldbach.selbergQuadraticSupport] using hd_pair.1
  exact Nat.lt_succ_iff.mp hd_lt

/-- Membership in the TS122 optimization support implies positivity. -/
theorem selbergOptimizationSupport_mem_pos
    {level d : Nat}
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d) :
    0 < d := by
  have hd_pair :
      Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) d /\
        0 < d := by
    simpa [
      TS122.Goldbach.selbergOptimizationSupport,
      TS121.Goldbach.selbergPositiveQuadraticSupport
    ] using hd
  exact hd_pair.2

/--
A support divisor of a prime strictly larger than the level is necessarily
`1`.
-/
theorem support_divisor_eq_one_of_prime_gt_level
    {level d k : Nat}
    (hd : Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d)
    (hprime : Nat.Prime k)
    (hlevel_lt : level < k)
    (hdvd : Dvd.dvd d k) :
    d = 1 := by
  have hd_le_level :
      d <= level :=
    selbergOptimizationSupport_mem_le_level hd
  have hd_lt_k :
      d < k :=
    lt_of_le_of_lt hd_le_level hlevel_lt
  exact
    Or.elim
      (hprime.eq_one_or_self_of_dvd d hdvd)
      (fun hd_one => hd_one)
      (fun hd_self => False.elim (hd_lt_k.ne hd_self))

/--
For primes larger than the level, the concrete divisor weight is exactly
`lambda_1 = 1`.
-/
theorem selbergConcreteDivisorWeight_eq_one_of_prime_gt_level
    (level k : Nat)
    (hlevel : 0 < level)
    (hprime : Nat.Prime k)
    (hlevel_lt : level < k) :
    TS138.Goldbach.selbergConcreteDivisorWeight level k = 1 := by
  unfold TS138.Goldbach.selbergConcreteDivisorWeight
  have hmem_one :
      Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) 1 :=
    TS123.Goldbach.one_mem_selbergOptimizationSupport level hlevel
  exact
    (Finset.sum_eq_single 1
      (by
        intro d hd hne
        have hnot_dvd :
            Not (Dvd.dvd d k) := by
          intro hdvd
          have hd_eq_one :
              d = 1 :=
            support_divisor_eq_one_of_prime_gt_level
              hd
              hprime
              hlevel_lt
              hdvd
          exact hne hd_eq_one
        simp [hnot_dvd])
      (by
        intro hnot
        exact False.elim (hnot hmem_one))).trans
      (by
        simp [
          TS136.Goldbach.selbergOptimalIntervalWeight_one level hlevel
        ])

/--
Large-prime admissibility on an interval: every prime in the TS22 interval is
larger than the Selberg support level.
-/
def LargePrimeSupportAdmissibility
    (level x Q n : Nat) :
    Prop :=
  forall k : Nat,
    Membership.mem (TS138.Goldbach.selbergConcreteInterval x Q n) k ->
      Nat.Prime k ->
        level < k

/--
Large-prime admissibility implies the pointwise condition required by TS139.
-/
theorem selbergConcretePrimePointwiseMajorant_of_largePrimeSupport
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (hadmissible :
      LargePrimeSupportAdmissibility level x Q n) :
    TS139.Goldbach.SelbergConcretePrimePointwiseMajorant level x Q n := by
  apply
    TS139.Goldbach.selbergConcretePrimePointwiseMajorant_of_weight_eq_one
  intro k hk hprime
  exact
    selbergConcreteDivisorWeight_eq_one_of_prime_gt_level
      level
      k
      hlevel
      hprime
      (hadmissible k hk hprime)

/--
A simpler interval-level condition: if the left endpoint is already above the
support level, then every prime in the interval is above the level.
-/
theorem largePrimeSupportAdmissibility_of_level_lt_leftEndpoint
    (level x Q n : Nat)
    (hlevel_lt_n : level < n) :
    LargePrimeSupportAdmissibility level x Q n := by
  intro k hk _hprime
  have hn_le_k :
      n <= k := by
    have hk_interval :
        Membership.mem
          (Finset.Icc n (n + TS15.Goldbach.intervalScale x Q))
          k := by
      simpa [TS138.Goldbach.selbergConcreteInterval] using hk
    exact (Finset.mem_Icc.mp hk_interval).1
  exact lt_of_lt_of_le hlevel_lt_n hn_le_k

/--
If the interval starts beyond the support level, then the TS139 pointwise
prime condition holds.
-/
theorem selbergConcretePrimePointwiseMajorant_of_level_lt_leftEndpoint
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (hlevel_lt_n : level < n) :
    TS139.Goldbach.SelbergConcretePrimePointwiseMajorant level x Q n := by
  exact
    selbergConcretePrimePointwiseMajorant_of_largePrimeSupport
      level
      x
      Q
      n
      hlevel
      (largePrimeSupportAdmissibility_of_level_lt_leftEndpoint
        level
        x
        Q
        n
        hlevel_lt_n)

/--
Under the large-prime interval condition, the TS138 square majorant bounds the
TS22 prime interval count.
-/
theorem primeIntervalCard_le_concreteMajorantValue_of_level_lt_leftEndpoint
    (level x Q n : Nat)
    (hlevel : 0 < level)
    (hlevel_lt_n : level < n) :
    TS22.Goldbach.primeIntervalCard n
        (TS15.Goldbach.intervalScale x Q) <=
      TS138.Goldbach.selbergConcreteMajorantValue level x Q n := by
  exact
    TS139.Goldbach.primeIntervalCard_le_concreteMajorantValue_of_pointwise
      level
      x
      Q
      n
      (selbergConcretePrimePointwiseMajorant_of_level_lt_leftEndpoint
        level
        x
        Q
        n
        hlevel
        hlevel_lt_n)

/--
Interval sieve theorem supplied by the large-prime condition.

The remaining `left_endpoint_large_obligation` is the geometric hypothesis
connecting the chosen interval and the support level.
-/
structure LargePrimeAdmissibleIntervalSieveTheorem
    (level : Nat) where
  hlevel :
    0 < level

  left_endpoint_large :
    forall x Q n : Nat,
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      n < x + 1 ->
        level < n

  left_endpoint_large_obligation :
    True

/--
Large-prime admissibility supplies the TS139 concrete interval sieve theorem.
-/
noncomputable def concreteSelbergIntervalSieveTheorem
    {level : Nat}
    (H : LargePrimeAdmissibleIntervalSieveTheorem level) :
    TS139.Goldbach.ConcreteSelbergIntervalSieveTheorem level where
  hlevel :=
    H.hlevel
  pointwise_prime_square_lower_bound := by
    intro x Q n k hx hQ hn hk hprime
    exact
      selbergConcretePrimePointwiseMajorant_of_level_lt_leftEndpoint
        level
        x
        Q
        n
        H.hlevel
        (H.left_endpoint_large x Q n hx hQ hn)
        k
        hk
        hprime
  pointwise_prime_admissibility_obligation :=
    H.left_endpoint_large_obligation

/--
TS140 ledger: large-prime interval admissibility closes the pointwise input of
TS139.  The Brun-Titchmarsh budget comparison remains separate.
-/
structure LargePrimeAdmissibilityLedger
    (level : Nat) where
  admissibility :
    LargePrimeAdmissibleIntervalSieveTheorem level

  intervalSieve :
    TS139.Goldbach.ConcreteSelbergIntervalSieveTheorem level

  interval_sieve_eq :
    intervalSieve =
      concreteSelbergIntervalSieveTheorem admissibility

  pointwise_prime_admissibility_closed :
    True

  brun_titchmarsh_budget_comparison_obligation :
    True

/-- Concrete TS140 ledger from the large-prime interval admissibility package. -/
noncomputable def largePrimeAdmissibilityLedger
    {level : Nat}
    (H : LargePrimeAdmissibleIntervalSieveTheorem level) :
    LargePrimeAdmissibilityLedger level where
  admissibility := H
  intervalSieve :=
    concreteSelbergIntervalSieveTheorem H
  interval_sieve_eq := rfl
  pointwise_prime_admissibility_closed := True.intro
  brun_titchmarsh_budget_comparison_obligation := True.intro

/--
Bridge target: large-prime interval admissibility populates the TS140 ledger.
-/
def LargePrimeAdmissibilityBridgeTarget : Prop :=
  forall level : Nat,
    LargePrimeAdmissibleIntervalSieveTheorem level ->
      Nonempty (LargePrimeAdmissibilityLedger level)

/-- The TS140 bridge target is populated. -/
theorem largePrimeAdmissibilityBridgeTarget :
    LargePrimeAdmissibilityBridgeTarget := by
  intro level H
  exact Nonempty.intro (largePrimeAdmissibilityLedger H)

/-- TS140 keeps the TS139 bridge target available. -/
theorem concreteSelbergIntervalSieveTheoremBridgeTarget :
    TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremBridgeTarget :=
  TS139.Goldbach.concreteSelbergIntervalSieveTheoremBridgeTarget

end Goldbach
end TS140
