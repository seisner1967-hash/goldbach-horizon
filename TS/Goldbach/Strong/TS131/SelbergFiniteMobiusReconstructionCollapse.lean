import Mathlib.Tactic
import TS.Goldbach.Strong.TS130.SelbergOptimalWeightReconstructionLedger

namespace TS131
namespace Goldbach

/-!
# TS131 - Selberg Finite Mobius Reconstruction Collapse

TS130 reconstructs original weights from a prescribed diagonal vector `Y` and
isolates the finite triangular Mobius inversion identity as the remaining
local obligation.

This sprint opens that obligation one level lower. It names the local chain
coefficient attached to the finite divisor chain

`d | m | e`

and proves that if the absorbed reconstruction expands through those
coefficients, and if the coefficients collapse to the Kronecker delta on the
positive finite support, then the TS130 reconstruction identity follows.

The hard finite Mobius calculation is now concentrated in the coefficient
collapse proposition.
-/

/-- Positive finite support used throughout TS130/TS131. -/
def selbergMobiusReconstructionSupport
    (level : Nat) :
    Finset Nat :=
  TS130.Goldbach.selbergReconstructionSupport level

/--
Local chain coefficient for the triangular reconstruction.

For fixed `d` and `e`, this is the coefficient of `Y e` after expanding

`sum_{d | m} sum_{m | e} mu(e / m) * Y e`.

The expected Mobius inversion statement is that this coefficient is `1` when
`d = e` and `0` otherwise, on the positive finite support.
-/
def selbergMobiusChainCoefficient
    (level d e : Nat) :
    Rat :=
  Finset.sum (selbergMobiusReconstructionSupport level) fun m =>
    if Dvd.dvd d m then
      if Dvd.dvd m e then
        TS122.Goldbach.selbergMobiusRatCoefficient (e / m)
      else
        0
    else
      0

/-- Pair-first expansion side obtained after collecting coefficients of `Y e`. -/
def selbergFiniteMobiusReconstructionExpandedSide
    (level : Nat)
    (Y : Nat -> Rat)
    (d : Nat) :
    Rat :=
  Finset.sum (selbergMobiusReconstructionSupport level) fun e =>
    Y e * selbergMobiusChainCoefficient level d e

/--
Expansion obligation for the reconstructed absorbed diagonal vector.

This is the remaining finite Fubini step from the concrete TS130 definitions to
the coefficient side above.
-/
def SelbergFiniteMobiusReconstructionExpansion
    (level : Nat)
    (Y : Nat -> Rat) :
    Prop :=
  forall d : Nat,
    Membership.mem (selbergMobiusReconstructionSupport level) d ->
      TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (TS130.Goldbach.reconstructedSelbergWeight level Y)
          d =
        selbergFiniteMobiusReconstructionExpandedSide level Y d

/--
Local coefficient collapse for the finite triangular Mobius inversion.

This is the exact remaining arithmetic/combinatorial atom:
the chain coefficient over `d | m | e` must be the delta coefficient.
-/
def SelbergMobiusChainCoefficientCollapse
    (level : Nat) :
    Prop :=
  forall d : Nat,
    Membership.mem (selbergMobiusReconstructionSupport level) d ->
      forall e : Nat,
        Membership.mem (selbergMobiusReconstructionSupport level) e ->
          selbergMobiusChainCoefficient level d e =
            if d = e then 1 else 0

/-- Delta coefficients select the `d`-th value of a vector on the support. -/
theorem selbergSupport_delta_sum
    (level : Nat)
    (Y : Nat -> Rat)
    (d : Nat)
    (hd : Membership.mem (selbergMobiusReconstructionSupport level) d) :
    Finset.sum (selbergMobiusReconstructionSupport level) (fun e =>
        Y e * if d = e then 1 else 0) =
      Y d := by
  classical
  have hterm :
      (fun e : Nat => Y e * if d = e then 1 else 0) =
        (fun e : Nat => if d = e then Y e else 0) := by
    funext e
    by_cases hde : d = e
    case pos =>
      simp [hde]
    case neg =>
      simp [hde]
  rw [hterm]
  have hsum :=
    (Finset.sum_ite_eq
      (s := selbergMobiusReconstructionSupport level)
      (a := d)
      (b := Y))
  rw [if_pos hd] at hsum
  exact hsum

/--
If the expanded side has delta chain coefficients, it recovers the target
diagonal vector.
-/
theorem selbergFiniteMobiusExpandedSide_eq_target_of_chainCollapse
    (level : Nat)
    (Y : Nat -> Rat)
    (hcollapse : SelbergMobiusChainCoefficientCollapse level)
    (d : Nat)
    (hd : Membership.mem (selbergMobiusReconstructionSupport level) d) :
    selbergFiniteMobiusReconstructionExpandedSide level Y d =
      Y d := by
  classical
  unfold selbergFiniteMobiusReconstructionExpandedSide
  calc
    Finset.sum (selbergMobiusReconstructionSupport level) (fun e =>
        Y e * selbergMobiusChainCoefficient level d e) =
        Finset.sum (selbergMobiusReconstructionSupport level) (fun e =>
          Y e * if d = e then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hcollapse d hd e he]
    _ = Y d :=
      selbergSupport_delta_sum level Y d hd

/--
The two local TS131 obligations discharge the TS130 finite reconstruction
identity.
-/
theorem selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
    (level : Nat)
    (Y : Nat -> Rat)
    (hexpansion :
      SelbergFiniteMobiusReconstructionExpansion level Y)
    (hcollapse :
      SelbergMobiusChainCoefficientCollapse level) :
    TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y := by
  intro d hd
  have hd' :
      Membership.mem (selbergMobiusReconstructionSupport level) d := by
    simpa [selbergMobiusReconstructionSupport] using hd
  rw [hexpansion d hd']
  exact
    selbergFiniteMobiusExpandedSide_eq_target_of_chainCollapse
      level
      Y
      hcollapse
      d
      hd'

/--
TS131 finite Mobius collapse package.

The concrete theorem above proves that the two named local obligations are
sufficient to close the TS130 reconstruction identity.
-/
structure SelbergFiniteMobiusReconstructionCollapse
    (level : Nat)
    (Y : Nat -> Rat) where
  reconstruction :
    TS130.Goldbach.SelbergWeightReconstruction level Y

  chainCoefficient :
    Nat -> Nat -> Rat

  chain_coefficient_eq :
    forall d e : Nat,
      chainCoefficient d e =
        selbergMobiusChainCoefficient level d e

  expansion_obligation :
    Prop

  expansion_obligation_eq :
    expansion_obligation =
      SelbergFiniteMobiusReconstructionExpansion level Y

  chain_collapse_obligation :
    Prop

  chain_collapse_obligation_eq :
    chain_collapse_obligation =
      SelbergMobiusChainCoefficientCollapse level

  reconstruction_identity_if_obligations :
    expansion_obligation ->
      chain_collapse_obligation ->
        TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y

  mobius_delta_input :
    TS105.Goldbach.MobiusConcreteDeltaDischargeTarget

  finite_fubini_obligation :
    True

  selberg_sieve_application_obligation :
    True

/-- Concrete TS131 collapse ledger for an arbitrary diagonal vector. -/
def selbergFiniteMobiusReconstructionCollapse
    (level : Nat)
    (Y : Nat -> Rat) :
    SelbergFiniteMobiusReconstructionCollapse level Y where
  reconstruction :=
    TS130.Goldbach.selbergWeightReconstruction level Y
  chainCoefficient :=
    selbergMobiusChainCoefficient level
  chain_coefficient_eq := by
    intro d e
    rfl
  expansion_obligation :=
    SelbergFiniteMobiusReconstructionExpansion level Y
  expansion_obligation_eq := rfl
  chain_collapse_obligation :=
    SelbergMobiusChainCoefficientCollapse level
  chain_collapse_obligation_eq := rfl
  reconstruction_identity_if_obligations := by
    intro hexpansion hcollapse
    exact
      selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
        level
        Y
        hexpansion
        hcollapse
  mobius_delta_input :=
    TS105.Goldbach.mobiusConcreteDeltaDischargeTarget
  finite_fubini_obligation := True.intro
  selberg_sieve_application_obligation := True.intro

/-- Specialization of TS131 to the TS128 optimal diagonal vector. -/
def selbergOptimalFiniteMobiusReconstructionCollapse
    (level : Nat) :
    SelbergFiniteMobiusReconstructionCollapse
      level
      (TS128.Goldbach.selbergOptimalDiagonalVector level) :=
  selbergFiniteMobiusReconstructionCollapse
    level
    (TS128.Goldbach.selbergOptimalDiagonalVector level)

/--
If TS131's two local obligations are discharged for the optimal vector, the
TS130 optimal reconstructed weight reaches the exact budget.
-/
theorem optimalReconstructedWeight_denseSide_eq_optimal_budget_of_TS131_obligations
    (level : Nat)
    (hlevel : 0 < level)
    (hexpansion :
      SelbergFiniteMobiusReconstructionExpansion
        level
        (TS128.Goldbach.selbergOptimalDiagonalVector level))
    (hcollapse :
      SelbergMobiusChainCoefficientCollapse level) :
    TS110.Goldbach.selbergDenseSide
        level
        (TS130.Goldbach.optimalReconstructedSelbergWeight level) =
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  exact
    TS130.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget_of_reconstruction
      level
      hlevel
      (selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
        level
        (TS128.Goldbach.selbergOptimalDiagonalVector level)
        hexpansion
        hcollapse)

/-- Target proposition for the TS131 collapse ledger. -/
def SelbergFiniteMobiusReconstructionCollapseTarget : Prop :=
  forall level : Nat,
    forall Y : Nat -> Rat,
      Nonempty (SelbergFiniteMobiusReconstructionCollapse level Y)

/-- The TS131 finite Mobius collapse ledger is populated. -/
theorem selbergFiniteMobiusReconstructionCollapseTarget :
    SelbergFiniteMobiusReconstructionCollapseTarget := by
  intro level Y
  exact Nonempty.intro
    (selbergFiniteMobiusReconstructionCollapse level Y)

/-- TS131 keeps the TS130 optimal reconstruction target available. -/
theorem selbergOptimalWeightReconstructionTarget :
    TS130.Goldbach.SelbergOptimalWeightReconstructionTarget :=
  TS130.Goldbach.selbergOptimalWeightReconstructionTarget

end Goldbach
end TS131
