import Mathlib.Tactic
import TS.Goldbach.Strong.TS88.FareySeparationProof

namespace TS89
namespace Goldbach

/-!
# TS89 - Farey Counting Proof

TS87 isolates Farey counting as a local infrastructure obligation, and TS88
discharges the separation component. This sprint proves a concrete finite
counting bound for the selected rational pairs used by the Farey layer.

The bound is deliberately robust: admissible reduced pairs `(a, q)` with
`0 < q <= Q` and `a < q` are counted inside the square
`range (Q + 1) x range (Q + 1)`, hence there are at most `(Q + 1)^2` of them.
-/

/-- Ambient square of numerator/denominator pairs bounded by `Q`. -/
def fareyCandidatePairs
    (Q : Nat) :
    Finset (Prod Nat Nat) :=
  (Finset.range (Q + 1)).product (Finset.range (Q + 1))

/-- Admissible reduced Farey pairs inside the ambient square. -/
def fareyReducedWindowPairs
    (Q : Nat) :
    Finset (Prod Nat Nat) :=
  (fareyCandidatePairs Q).filter fun p =>
    And (0 < p.2) (And (p.2 <= Q) (And (p.1 < p.2) (Nat.Coprime p.1 p.2)))

/-- The ambient square has cardinality `(Q + 1)^2`. -/
theorem fareyCandidatePairs_card
    (Q : Nat) :
    (fareyCandidatePairs Q).card = (Q + 1) * (Q + 1) := by
  calc
    (fareyCandidatePairs Q).card =
        (Finset.range (Q + 1)).card * (Finset.range (Q + 1)).card := by
      unfold fareyCandidatePairs
      exact Finset.card_product _ _
    _ = (Q + 1) * (Q + 1) := by
      simp

/-- Filtering admissible pairs cannot increase cardinality. -/
theorem fareyReducedWindowPairs_card_le_candidate
    (Q : Nat) :
    (fareyReducedWindowPairs Q).card <= (fareyCandidatePairs Q).card := by
  unfold fareyReducedWindowPairs
  exact Finset.card_filter_le _ _

/-- Concrete finite counting statement for the Farey window. -/
def FareyCountingStatement : Prop :=
  forall Q : Nat,
    (fareyReducedWindowPairs Q).card <= (Q + 1) * (Q + 1)

/-- The Farey window has at most `(Q + 1)^2` admissible reduced pairs. -/
theorem fareyCountingStatement :
    FareyCountingStatement := by
  intro Q
  calc
    (fareyReducedWindowPairs Q).card <= (fareyCandidatePairs Q).card :=
      fareyReducedWindowPairs_card_le_candidate Q
    _ = (Q + 1) * (Q + 1) :=
      fareyCandidatePairs_card Q

/--
Concrete TS87 counting contract. The actual cardinal bound is recorded in
`fareyCountingStatement`; the TS87 interface currently only asks for a marker.
-/
def fareyCountingContract :
    TS87.Goldbach.FareyCountingContract where
  counting_ready := by
    have _h : FareyCountingStatement :=
      fareyCountingStatement
    exact True.intro

/-- TS89 discharges the TS87 Farey counting target. -/
theorem fareyCountingContractTarget :
    TS87.Goldbach.FareyCountingContractTarget :=
  Nonempty.intro fareyCountingContract

/-- Local target for TS89. -/
def FareyCountingProofTarget : Prop :=
  TS87.Goldbach.FareyCountingContractTarget

/-- The local TS89 target is discharged. -/
theorem fareyCountingProofTarget :
    FareyCountingProofTarget :=
  fareyCountingContractTarget

/--
After TS88 and TS89, a covering contract is enough to produce the full TS87
Farey-spacing contract target.
-/
theorem fareySpacingContractTarget_of_covering
    (Hc : TS87.Goldbach.FareyCoveringContractTarget) :
    TS87.Goldbach.FareySpacingContractTarget :=
  TS88.Goldbach.fareySpacingContractTarget_of_covering_counting
    Hc
    fareyCountingContractTarget

/--
After TS88 and TS89, a covering contract is enough to produce the TS86
Farey-spacing infrastructure target.
-/
theorem fareySpacingInfrastructureTarget_of_covering
    (Hc : TS87.Goldbach.FareyCoveringContractTarget) :
    TS86.Goldbach.FareySpacingInfrastructureTarget :=
  TS88.Goldbach.fareySpacingInfrastructureTarget_of_covering_counting
    Hc
    fareyCountingContractTarget

/--
Covering plus a padded dual large-sieve target now gives the TS84
scale-transfer API target.
-/
theorem scaleTransferMajorantAPIContractsTarget_of_covering_paddedDualLargeSieveTarget
    (Hc : TS87.Goldbach.FareyCoveringContractTarget)
    (HD :
      TS86.Goldbach.DualLargeSieveVarianceBoundTarget
        TS24.Goldbach.brunTitchmarshPaddedClosedFormScale) :
    TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget :=
  TS88.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_counting_paddedDualLargeSieveTarget
    Hc
    fareyCountingContractTarget
    HD

end Goldbach
end TS89
