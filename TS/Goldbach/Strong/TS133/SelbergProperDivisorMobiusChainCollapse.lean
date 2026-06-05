import Mathlib.Tactic
import TS.Goldbach.Strong.TS132.SelbergMobiusChainCoefficientCollapseLedger

namespace TS133
namespace Goldbach

/-!
# TS133 - Selberg Proper Divisor Mobius Chain Collapse

TS132 reduces the local Mobius chain coefficient collapse to the proper
divisor case `d | e` and `d != e`.

This sprint proves the quotient side of that reduction:

* a positive proper divisor has quotient `e / d > 1`;
* the Mobius divisor sum over that quotient is zero by TS105;
* therefore the TS132 proper-divisor collapse follows from the single
  remaining finite reindexing statement that identifies the chain coefficient
  with the quotient divisor sum.

The actual `m = d * r` finite reindexing is kept as the next exact local
obligation.
-/

/-- A positive proper divisor gives a quotient strictly larger than `1`. -/
theorem quotient_one_lt_of_proper_dvd
    {d e : Nat}
    (hdpos : 0 < d)
    (hepos : 0 < e)
    (hdvd : Dvd.dvd d e)
    (hne : Not (d = e)) :
    1 < e / d := by
  cases hdvd with
  | intro q hq =>
      subst e
      have hqpos : 0 < q := by
        by_contra hnot
        have hqzero : q = 0 := Nat.eq_zero_of_not_pos hnot
        subst q
        simp at hepos
      have hqne_one : Not (q = 1) := by
        intro hqone
        apply hne
        subst q
        simp
      have hq_one_lt : 1 < q := by
        omega
      have hdiv : d * q / d = q := by
        rw [Nat.mul_comm]
        exact Nat.mul_div_left q hdpos
      simpa [hdiv] using hq_one_lt

/-- The quotient Mobius divisor sum is zero away from quotient `1`. -/
theorem quotientMobiusDivisorSum_eq_zero_of_one_lt
    (n : Nat)
    (hn : 1 < n) :
    Finset.sum (Nat.divisors n) (fun r =>
        TS122.Goldbach.selbergMobiusRatCoefficient (n / r)) = 0 := by
  have hsum :
      Finset.sum (Nat.divisors n) (fun r =>
          TS122.Goldbach.selbergMobiusRatCoefficient (n / r)) =
        Finset.sum (Nat.divisors n)
          TS122.Goldbach.selbergMobiusRatCoefficient := by
    simpa using
      (Nat.sum_div_divisors
        (n := n)
        (f := TS122.Goldbach.selbergMobiusRatCoefficient))
  have hdelta := TS105.Goldbach.mathlibMoebiusDivisorSum_eq_ite n
  have hn_ne_one : Not (n = 1) := by
    omega
  rw [hsum]
  simpa
    [TS104.Goldbach.mathlibDivisorSum,
      TS104.Goldbach.mathlibMoebiusFun,
      TS122.Goldbach.selbergMobiusRatCoefficient,
      hn_ne_one]
    using hdelta

/--
Finite quotient reindexing still needed for the proper-divisor chain
coefficient.

It is the exact statement that the finite chain sum over `m` with
`d | m | e` is the quotient divisor sum over divisors of `e / d`.
-/
def SelbergMobiusProperDivisorQuotientReindexing
    (level : Nat) :
    Prop :=
  forall d : Nat,
    Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) d ->
      forall e : Nat,
        Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) e ->
          Dvd.dvd d e ->
            TS131.Goldbach.selbergMobiusChainCoefficient level d e =
              Finset.sum (Nat.divisors (e / d)) fun r =>
                TS122.Goldbach.selbergMobiusRatCoefficient ((e / d) / r)

/--
Once the quotient reindexing is available, the remaining TS132 proper-divisor
case collapses by the TS105 Mobius-delta identity.
-/
theorem selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
    (level : Nat)
    (hreindex :
      SelbergMobiusProperDivisorQuotientReindexing level) :
    TS132.Goldbach.SelbergMobiusProperDivisorChainCollapse level := by
  intro d hd e he hdvd hne
  have hd_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) d := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using hd
  have he_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) e := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using he
  have hdpos : 0 < d :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos hd_support
  have hepos : 0 < e :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos he_support
  have hquot : 1 < e / d :=
    quotient_one_lt_of_proper_dvd
      hdpos
      hepos
      hdvd
      hne
  rw [hreindex d hd e he hdvd]
  exact quotientMobiusDivisorSum_eq_zero_of_one_lt (e / d) hquot

/--
The quotient reindexing obligation supplies the full TS131 chain coefficient
collapse through TS132.
-/
theorem selbergMobiusChainCoefficientCollapse_of_quotientReindexing
    (level : Nat)
    (hreindex :
      SelbergMobiusProperDivisorQuotientReindexing level) :
    TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level := by
  exact
    TS132.Goldbach.selbergMobiusChainCoefficientCollapse_of_properDivisorCollapse
      level
      (selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
        level
        hreindex)

/--
The TS131 expansion plus the quotient reindexing discharge the TS130 finite
Mobius reconstruction identity.
-/
theorem selbergFiniteMobiusReconstructionIdentity_of_expansion_quotientReindexing
    (level : Nat)
    (Y : Nat -> Rat)
    (hexpansion :
      TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y)
    (hreindex :
      SelbergMobiusProperDivisorQuotientReindexing level) :
    TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y := by
  exact
    TS132.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_properDivisorCollapse
      level
      Y
      hexpansion
      (selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
        level
        hreindex)

/-- TS133 package around the proper-divisor quotient collapse. -/
structure SelbergProperDivisorMobiusChainCollapse
    (level : Nat) where
  ts132 :
    TS132.Goldbach.SelbergMobiusChainCoefficientCollapseLedger level

  quotient_one_lt :
    forall d e : Nat,
      0 < d ->
        0 < e ->
          Dvd.dvd d e ->
            Not (d = e) ->
              1 < e / d

  quotient_mobius_sum_zero :
    forall n : Nat,
      1 < n ->
        Finset.sum (Nat.divisors n) (fun r =>
          TS122.Goldbach.selbergMobiusRatCoefficient (n / r)) = 0

  quotient_reindexing_obligation :
    Prop

  quotient_reindexing_obligation_eq :
    quotient_reindexing_obligation =
      SelbergMobiusProperDivisorQuotientReindexing level

  proper_divisor_collapse_if_reindexing :
    quotient_reindexing_obligation ->
      TS132.Goldbach.SelbergMobiusProperDivisorChainCollapse level

  full_chain_collapse_if_reindexing :
    quotient_reindexing_obligation ->
      TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level

  reconstruction_identity_if_expansion_and_reindexing :
    forall Y : Nat -> Rat,
      TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y ->
        quotient_reindexing_obligation ->
          TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y

  mobius_delta_input :
    TS105.Goldbach.MobiusConcreteDeltaDischargeTarget

  finite_quotient_reindexing_obligation :
    True

  reconstruction_fubini_expansion_obligation :
    True

  selberg_sieve_application_obligation :
    True

/-- Concrete TS133 proper-divisor quotient collapse package. -/
def selbergProperDivisorMobiusChainCollapse
    (level : Nat) :
    SelbergProperDivisorMobiusChainCollapse level where
  ts132 :=
    TS132.Goldbach.selbergMobiusChainCoefficientCollapseLedger level
  quotient_one_lt := by
    intro d e hdpos hepos hdvd hne
    exact quotient_one_lt_of_proper_dvd hdpos hepos hdvd hne
  quotient_mobius_sum_zero := by
    intro n hn
    exact quotientMobiusDivisorSum_eq_zero_of_one_lt n hn
  quotient_reindexing_obligation :=
    SelbergMobiusProperDivisorQuotientReindexing level
  quotient_reindexing_obligation_eq := rfl
  proper_divisor_collapse_if_reindexing := by
    intro hreindex
    exact
      selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
        level
        hreindex
  full_chain_collapse_if_reindexing := by
    intro hreindex
    exact
      selbergMobiusChainCoefficientCollapse_of_quotientReindexing
        level
        hreindex
  reconstruction_identity_if_expansion_and_reindexing := by
    intro Y hexpansion hreindex
    exact
      selbergFiniteMobiusReconstructionIdentity_of_expansion_quotientReindexing
        level
        Y
        hexpansion
        hreindex
  mobius_delta_input :=
    TS105.Goldbach.mobiusConcreteDeltaDischargeTarget
  finite_quotient_reindexing_obligation := True.intro
  reconstruction_fubini_expansion_obligation := True.intro
  selberg_sieve_application_obligation := True.intro

/-- Target proposition for the TS133 proper-divisor quotient collapse package. -/
def SelbergProperDivisorMobiusChainCollapseTarget : Prop :=
  forall level : Nat,
    Nonempty (SelbergProperDivisorMobiusChainCollapse level)

/-- The TS133 proper-divisor quotient collapse package is populated. -/
theorem selbergProperDivisorMobiusChainCollapseTarget :
    SelbergProperDivisorMobiusChainCollapseTarget := by
  intro level
  exact Nonempty.intro
    (selbergProperDivisorMobiusChainCollapse level)

/-- TS133 keeps the TS132 chain coefficient ledger target available. -/
theorem selbergMobiusChainCoefficientCollapseLedgerTarget :
    TS132.Goldbach.SelbergMobiusChainCoefficientCollapseLedgerTarget :=
  TS132.Goldbach.selbergMobiusChainCoefficientCollapseLedgerTarget

end Goldbach
end TS133
