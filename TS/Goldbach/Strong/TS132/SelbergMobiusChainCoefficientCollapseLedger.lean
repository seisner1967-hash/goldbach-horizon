import Mathlib.Tactic
import TS.Goldbach.Strong.TS131.SelbergFiniteMobiusReconstructionCollapse

namespace TS132
namespace Goldbach

/-!
# TS132 - Selberg Mobius Chain Coefficient Collapse Ledger

TS131 reduces the finite Mobius reconstruction identity to a local chain
coefficient

`sum_m 1_{d | m} * 1_{m | e} * mu(e / m)`.

This sprint proves the two immediate coefficient cases:

* if `d = e`, the coefficient is `1`;
* if `d` does not divide `e`, the coefficient is `0`.

The only remaining coefficient case is the proper-divisibility case
`d | e` and `d != e`, where the future proof must change variables from
`m` to a divisor of `e / d` and apply the Mobius-delta identity from TS105.
-/

/-- The rational Mobius coefficient at `1` is `1`. -/
theorem selbergMobiusRatCoefficient_one :
    TS122.Goldbach.selbergMobiusRatCoefficient 1 = 1 := by
  simp [TS122.Goldbach.selbergMobiusRatCoefficient]

/-- If `d` does not divide `e`, the chain coefficient is zero. -/
theorem selbergMobiusChainCoefficient_eq_zero_of_not_dvd
    (level d e : Nat)
    (hnot : Not (Dvd.dvd d e)) :
    TS131.Goldbach.selbergMobiusChainCoefficient level d e = 0 := by
  unfold TS131.Goldbach.selbergMobiusChainCoefficient
  apply Finset.sum_eq_zero
  intro m _hm
  by_cases hdm : Dvd.dvd d m
  case pos =>
    have hnme : Not (Dvd.dvd m e) := by
      intro hme
      exact hnot (dvd_trans hdm hme)
    simp [hdm, hnme]
  case neg =>
    simp [hdm]

/-- Diagonal chain coefficient: for support `d`, the coefficient of `Y d` is `1`. -/
theorem selbergMobiusChainCoefficient_eq_one_of_eq
    (level d : Nat)
    (hd :
      Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) d) :
    TS131.Goldbach.selbergMobiusChainCoefficient level d d = 1 := by
  classical
  unfold TS131.Goldbach.selbergMobiusChainCoefficient
  calc
    Finset.sum
        (TS131.Goldbach.selbergMobiusReconstructionSupport level)
        (fun m =>
          if Dvd.dvd d m then
            if Dvd.dvd m d then
              TS122.Goldbach.selbergMobiusRatCoefficient (d / m)
            else
              0
          else
            0) =
        (if Dvd.dvd d d then
          if Dvd.dvd d d then
            TS122.Goldbach.selbergMobiusRatCoefficient (d / d)
          else
            0
        else
          0) := by
      refine
        Finset.sum_eq_single
          (s := TS131.Goldbach.selbergMobiusReconstructionSupport level)
          (a := d)
          (f := fun m =>
            if Dvd.dvd d m then
              if Dvd.dvd m d then
                TS122.Goldbach.selbergMobiusRatCoefficient (d / m)
              else
                0
          else
            0)
          (by
            intro m _hm hne
            by_cases hdm : Dvd.dvd d m
            case pos =>
              by_cases hmd : Dvd.dvd m d
              case pos =>
                have h_eq : m = d := Nat.dvd_antisymm hmd hdm
                exact False.elim (hne h_eq)
              case neg =>
                simp [hdm, hmd]
            case neg =>
              simp [hdm])
          (by
            intro hnot
            exact False.elim (hnot hd))
    _ = 1 := by
      have hd_support :
          Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) d := by
        simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using hd
      have hdpos : 0 < d :=
        TS130.Goldbach.mem_selbergReconstructionSupport_pos hd_support
      have hdiv : d / d = 1 := Nat.div_self hdpos
      simp [hdiv, selbergMobiusRatCoefficient_one]

/--
The remaining proper-divisibility case for the chain coefficient.

This is the exact quotient-Mobius obligation left after TS132.
-/
def SelbergMobiusProperDivisorChainCollapse
    (level : Nat) :
    Prop :=
  forall d : Nat,
    Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) d ->
      forall e : Nat,
        Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) e ->
          Dvd.dvd d e ->
            Not (d = e) ->
              TS131.Goldbach.selbergMobiusChainCoefficient level d e = 0

/--
The proper-divisor coefficient collapse supplies the full TS131 chain
coefficient collapse.
-/
theorem selbergMobiusChainCoefficientCollapse_of_properDivisorCollapse
    (level : Nat)
    (hproper : SelbergMobiusProperDivisorChainCollapse level) :
    TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level := by
  intro d hd e he
  by_cases hde : d = e
  case pos =>
    subst e
    rw [selbergMobiusChainCoefficient_eq_one_of_eq level d hd]
    simp
  case neg =>
    by_cases hdvd : Dvd.dvd d e
    case pos =>
      rw [hproper d hd e he hdvd hde]
      simp [hde]
    case neg =>
      rw [selbergMobiusChainCoefficient_eq_zero_of_not_dvd level d e hdvd]
      simp [hde]

/--
If TS131's Fubini expansion and the proper-divisor chain collapse are both
available, then TS130's finite reconstruction identity follows.
-/
theorem selbergFiniteMobiusReconstructionIdentity_of_expansion_properDivisorCollapse
    (level : Nat)
    (Y : Nat -> Rat)
    (hexpansion :
      TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y)
    (hproper :
      SelbergMobiusProperDivisorChainCollapse level) :
    TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y := by
  exact
    TS131.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
      level
      Y
      hexpansion
      (selbergMobiusChainCoefficientCollapse_of_properDivisorCollapse
        level
        hproper)

/-- TS132 package around the chain coefficient collapse. -/
structure SelbergMobiusChainCoefficientCollapseLedger
    (level : Nat) where
  ts131 :
    forall Y : Nat -> Rat,
      TS131.Goldbach.SelbergFiniteMobiusReconstructionCollapse level Y

  diagonal_coefficient :
    forall d : Nat,
      Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) d ->
        TS131.Goldbach.selbergMobiusChainCoefficient level d d = 1

  non_divisor_coefficient :
    forall d e : Nat,
      Not (Dvd.dvd d e) ->
        TS131.Goldbach.selbergMobiusChainCoefficient level d e = 0

  proper_divisor_chain_collapse_obligation :
    Prop

  proper_divisor_chain_collapse_obligation_eq :
    proper_divisor_chain_collapse_obligation =
      SelbergMobiusProperDivisorChainCollapse level

  full_chain_collapse_if_proper :
    proper_divisor_chain_collapse_obligation ->
      TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level

  reconstruction_identity_if_expansion_and_proper :
    forall Y : Nat -> Rat,
      TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y ->
        proper_divisor_chain_collapse_obligation ->
          TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y

  mobius_delta_input :
    TS105.Goldbach.MobiusConcreteDeltaDischargeTarget

  quotient_change_of_variables_obligation :
    True

  selberg_sieve_application_obligation :
    True

/-- Concrete TS132 chain coefficient ledger. -/
def selbergMobiusChainCoefficientCollapseLedger
    (level : Nat) :
    SelbergMobiusChainCoefficientCollapseLedger level where
  ts131 := by
    intro Y
    exact TS131.Goldbach.selbergFiniteMobiusReconstructionCollapse level Y
  diagonal_coefficient := by
    intro d hd
    exact selbergMobiusChainCoefficient_eq_one_of_eq level d hd
  non_divisor_coefficient := by
    intro d e hnot
    exact selbergMobiusChainCoefficient_eq_zero_of_not_dvd level d e hnot
  proper_divisor_chain_collapse_obligation :=
    SelbergMobiusProperDivisorChainCollapse level
  proper_divisor_chain_collapse_obligation_eq := rfl
  full_chain_collapse_if_proper := by
    intro hproper
    exact
      selbergMobiusChainCoefficientCollapse_of_properDivisorCollapse
        level
        hproper
  reconstruction_identity_if_expansion_and_proper := by
    intro Y hexpansion hproper
    exact
      selbergFiniteMobiusReconstructionIdentity_of_expansion_properDivisorCollapse
        level
        Y
        hexpansion
        hproper
  mobius_delta_input :=
    TS105.Goldbach.mobiusConcreteDeltaDischargeTarget
  quotient_change_of_variables_obligation := True.intro
  selberg_sieve_application_obligation := True.intro

/-- Target proposition for the TS132 chain coefficient ledger. -/
def SelbergMobiusChainCoefficientCollapseLedgerTarget : Prop :=
  forall level : Nat,
    Nonempty (SelbergMobiusChainCoefficientCollapseLedger level)

/-- The TS132 chain coefficient ledger is populated. -/
theorem selbergMobiusChainCoefficientCollapseLedgerTarget :
    SelbergMobiusChainCoefficientCollapseLedgerTarget := by
  intro level
  exact Nonempty.intro
    (selbergMobiusChainCoefficientCollapseLedger level)

/-- TS132 keeps the TS131 collapse target available. -/
theorem selbergFiniteMobiusReconstructionCollapseTarget :
    TS131.Goldbach.SelbergFiniteMobiusReconstructionCollapseTarget :=
  TS131.Goldbach.selbergFiniteMobiusReconstructionCollapseTarget

end Goldbach
end TS132
