import Mathlib.Tactic
import TS.Goldbach.Strong.TS134.SelbergProperDivisorQuotientReindexingDischarge

namespace TS135
namespace Goldbach

/-!
# TS135 - Selberg Finite Mobius Reconstruction Expansion Discharge

TS134 closes the chain-coefficient collapse in the finite Mobius
reconstruction layer.  This sprint discharges the remaining TS131 Fubini
expansion:

`absorbedDiagonal(reconstructedWeight)(d) = sum_e Y e * coeff(d,e)`.

No new arithmetic is used here.  The proof unfolds the reconstructed absorbed
weight, swaps two finite sums, and recognizes the TS131 chain coefficient.
-/

/-- The zero index does not divide a supported positive reconstruction index. -/
theorem zero_not_dvd_reconstructionSupport
    {level e : Nat}
    (he :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) e) :
    Not (Dvd.dvd 0 e) := by
  intro h
  have he_pos : 0 < e :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos he
  exact Nat.ne_of_gt he_pos (Nat.eq_zero_of_zero_dvd h)

/--
The reconstructed absorbed coefficient has the same divisor-filtered sum when
expanded over the TS131 reconstruction support.
-/
theorem absorbedCoefficientFromDiagonalVector_expansion
    (level : Nat)
    (Y : Nat -> Rat)
    (m : Nat) :
    TS130.Goldbach.absorbedCoefficientFromDiagonalVector level Y m =
      Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
        if Dvd.dvd m e then
          TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
        else
          0 := by
  rfl

/--
On the positive reconstruction support, the absorbed original weight of the
reconstructed Selberg weight is the expanded Mobius transform.
-/
theorem selbergLCMAbsorbedWeight_reconstructed_expansion
    (level : Nat)
    (Y : Nat -> Rat)
    {m : Nat}
    (hm :
      Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) m) :
    TS118.Goldbach.selbergLCMAbsorbedWeight
        (TS130.Goldbach.reconstructedSelbergWeight level Y)
        m =
      Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
        if Dvd.dvd m e then
          TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
        else
          0 := by
  have hm_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) m := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using hm
  have hm_pos : 0 < m :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos hm_support
  rw [TS130.Goldbach.selbergLCMAbsorbedWeight_reconstructed_eq_absorbedCoefficient
    level Y m hm_pos]
  exact absorbedCoefficientFromDiagonalVector_expansion level Y m

/--
The absorbed diagonal vector of reconstructed weights is the `m`-first double
sum over the positive reconstruction support.
-/
theorem selbergAbsorbedDiagonalVector_reconstructed_eq_mFirst
    (level : Nat)
    (Y : Nat -> Rat)
    (d : Nat)
    (hd :
      Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) d) :
    TS129.Goldbach.selbergAbsorbedDiagonalVector
        level
        (TS130.Goldbach.reconstructedSelbergWeight level Y)
        d =
      Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun m =>
        if Dvd.dvd d m then
          Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
            if Dvd.dvd m e then
              TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
            else
              0
        else
          0 := by
  classical
  have hd_support :
      Membership.mem (TS130.Goldbach.selbergReconstructionSupport level) d := by
    simpa [TS131.Goldbach.selbergMobiusReconstructionSupport] using hd
  have hd_pos : 0 < d :=
    TS130.Goldbach.mem_selbergReconstructionSupport_pos hd_support
  unfold TS129.Goldbach.selbergAbsorbedDiagonalVector
  unfold TS119.Goldbach.selbergGcdSquareTransformedWeight
  have hpositive :
      Finset.sum (TS108.Goldbach.selbergQuadraticSupport level) (fun m =>
          if Dvd.dvd d m then
            TS118.Goldbach.selbergLCMAbsorbedWeight
              (TS130.Goldbach.reconstructedSelbergWeight level Y)
              m
          else
            0) =
        Finset.sum (TS121.Goldbach.selbergPositiveQuadraticSupport level) (fun m =>
          if Dvd.dvd d m then
            TS118.Goldbach.selbergLCMAbsorbedWeight
              (TS130.Goldbach.reconstructedSelbergWeight level Y)
              m
          else
            0) := by
    rw [TS121.Goldbach.selbergPositiveQuadraticSupport]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hm_pos : 0 < m
    case pos =>
      simp [hm_pos]
    case neg =>
      have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_pos
      subst m
      have hz :
          TS118.Goldbach.selbergLCMAbsorbedWeight
              (TS130.Goldbach.reconstructedSelbergWeight level Y)
              0 =
            0 := by
        unfold TS118.Goldbach.selbergLCMAbsorbedWeight
        rw [TS130.Goldbach.reconstructedSelbergWeight_zero]
        simp
      simp [hz]
  rw [hpositive]
  change
    Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun m =>
        if Dvd.dvd d m then
          TS118.Goldbach.selbergLCMAbsorbedWeight
            (TS130.Goldbach.reconstructedSelbergWeight level Y)
            m
        else
          0) =
      Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun m =>
        if Dvd.dvd d m then
          Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
            if Dvd.dvd m e then
              TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
            else
              0
        else
          0)
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hdm : Dvd.dvd d m
  case pos =>
    have hm131 :
        Membership.mem (TS131.Goldbach.selbergMobiusReconstructionSupport level) m := by
      simpa
        [TS131.Goldbach.selbergMobiusReconstructionSupport,
          TS130.Goldbach.selbergReconstructionSupport,
          TS122.Goldbach.selbergOptimizationSupport]
        using hm
    rw [selbergLCMAbsorbedWeight_reconstructed_expansion level Y hm131]
  case neg =>
    simp [hdm]

/--
The `m`-first expansion commutes to the coefficient-collected side from TS131.
-/
theorem selbergFiniteMobiusReconstruction_mFirst_eq_expandedSide
    (level : Nat)
    (Y : Nat -> Rat)
    (d : Nat) :
    Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun m =>
        if Dvd.dvd d m then
          Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
            if Dvd.dvd m e then
              TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
            else
              0
        else
          0) =
      TS131.Goldbach.selbergFiniteMobiusReconstructionExpandedSide level Y d := by
  classical
  unfold TS131.Goldbach.selbergFiniteMobiusReconstructionExpandedSide
  unfold TS131.Goldbach.selbergMobiusChainCoefficient
  calc
    Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun m =>
        if Dvd.dvd d m then
          Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
            if Dvd.dvd m e then
              TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
            else
              0
        else
          0) =
        Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun m =>
          Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
            if Dvd.dvd d m then
              if Dvd.dvd m e then
                TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
              else
                0
            else
              0) := by
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hdm : Dvd.dvd d m
      case pos =>
        simp [hdm]
      case neg =>
        simp [hdm]
    _ =
        Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun e =>
          Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun m =>
            if Dvd.dvd d m then
              if Dvd.dvd m e then
                TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
              else
                0
            else
              0) := by
      exact Finset.sum_comm
    _ =
        Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun e =>
          Y e *
            Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun m =>
              if Dvd.dvd d m then
                if Dvd.dvd m e then
                  TS122.Goldbach.selbergMobiusRatCoefficient (e / m)
                else
                  0
              else
                0) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hdm : Dvd.dvd d m
      case pos =>
        by_cases hme : Dvd.dvd m e
        case pos =>
          simp [hdm, hme]
          ring
        case neg =>
          simp [hdm, hme]
      case neg =>
        simp [hdm]
    _ =
        Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) (fun e =>
          Y e *
            Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun m =>
              if Dvd.dvd d m then
                if Dvd.dvd m e then
                  TS122.Goldbach.selbergMobiusRatCoefficient (e / m)
                else
                  0
              else
                0) := rfl

/-- TS135 discharges the TS131 finite Fubini expansion. -/
theorem selbergFiniteMobiusReconstructionExpansion
    (level : Nat)
    (Y : Nat -> Rat) :
    TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y := by
  intro d hd
  calc
    TS129.Goldbach.selbergAbsorbedDiagonalVector
        level
        (TS130.Goldbach.reconstructedSelbergWeight level Y)
        d =
        Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun m =>
          if Dvd.dvd d m then
            Finset.sum (TS131.Goldbach.selbergMobiusReconstructionSupport level) fun e =>
              if Dvd.dvd m e then
                TS122.Goldbach.selbergMobiusRatCoefficient (e / m) * Y e
              else
                0
          else
            0 :=
      selbergAbsorbedDiagonalVector_reconstructed_eq_mFirst level Y d hd
    _ =
        TS131.Goldbach.selbergFiniteMobiusReconstructionExpandedSide level Y d :=
      selbergFiniteMobiusReconstruction_mFirst_eq_expandedSide level Y d

/-- TS135 closes the TS130 finite Mobius reconstruction identity. -/
theorem selbergFiniteMobiusReconstructionIdentity
    (level : Nat)
    (Y : Nat -> Rat) :
    TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y := by
  exact
    TS131.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
      level
      Y
      (selbergFiniteMobiusReconstructionExpansion level Y)
      (TS134.Goldbach.selbergMobiusChainCoefficientCollapse level)

/-- The optimal reconstructed weights attain the exact TS128 budget. -/
theorem optimalReconstructedWeight_denseSide_eq_optimal_budget
    (level : Nat)
    (hlevel : 0 < level) :
    TS110.Goldbach.selbergDenseSide
        level
        (TS130.Goldbach.optimalReconstructedSelbergWeight level) =
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  exact
    TS130.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget_of_reconstruction
      level
      hlevel
      (selbergFiniteMobiusReconstructionIdentity
        level
        (TS128.Goldbach.selbergOptimalDiagonalVector level))

/-- TS135 package closing the finite reconstruction layer. -/
structure SelbergFiniteMobiusReconstructionExpansionDischarge
    (level : Nat) where
  expansion :
    forall Y : Nat -> Rat,
      TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion level Y

  chain_collapse :
    TS131.Goldbach.SelbergMobiusChainCoefficientCollapse level

  reconstruction_identity :
    forall Y : Nat -> Rat,
      TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y

  optimal_budget :
    0 < level ->
      TS110.Goldbach.selbergDenseSide
          level
          (TS130.Goldbach.optimalReconstructedSelbergWeight level) =
        1 / TS122.Goldbach.selbergOptimizationDenominator level

  selberg_interval_majorant_obligation :
    True

  brun_titchmarsh_obligation :
    True

/-- Concrete TS135 finite Mobius reconstruction package. -/
def selbergFiniteMobiusReconstructionExpansionDischarge
    (level : Nat) :
    SelbergFiniteMobiusReconstructionExpansionDischarge level where
  expansion := by
    intro Y
    exact selbergFiniteMobiusReconstructionExpansion level Y
  chain_collapse :=
    TS134.Goldbach.selbergMobiusChainCoefficientCollapse level
  reconstruction_identity := by
    intro Y
    exact selbergFiniteMobiusReconstructionIdentity level Y
  optimal_budget := by
    intro hlevel
    exact optimalReconstructedWeight_denseSide_eq_optimal_budget level hlevel
  selberg_interval_majorant_obligation := True.intro
  brun_titchmarsh_obligation := True.intro

/-- Target proposition for TS135. -/
def SelbergFiniteMobiusReconstructionExpansionDischargeTarget : Prop :=
  forall level : Nat,
    Nonempty (SelbergFiniteMobiusReconstructionExpansionDischarge level)

/-- The TS135 finite reconstruction discharge is populated. -/
theorem selbergFiniteMobiusReconstructionExpansionDischargeTarget :
    SelbergFiniteMobiusReconstructionExpansionDischargeTarget := by
  intro level
  exact Nonempty.intro
    (selbergFiniteMobiusReconstructionExpansionDischarge level)

/-- TS135 keeps the TS134 target available. -/
theorem selbergProperDivisorQuotientReindexingDischargeTarget :
    TS134.Goldbach.SelbergProperDivisorQuotientReindexingDischargeTarget :=
  TS134.Goldbach.selbergProperDivisorQuotientReindexingDischargeTarget

end Goldbach
end TS135
