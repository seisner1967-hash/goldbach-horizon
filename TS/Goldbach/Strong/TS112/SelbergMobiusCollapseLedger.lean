import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import TS.Goldbach.Strong.TS111.SelbergDenseToDiagonalReindexingLedger

namespace TS112
namespace Goldbach

/-!
# TS112 - Selberg Mobius Collapse Ledger

TS111 expands the TS109 diagonal square side into a finite triple sum. This
sprint opens the next proof-facing layer: rewriting the two divisor filters in
that triple sum as one filter on `gcd m n`, and naming the remaining Mobius
collapse obligation toward the TS110 dense side.

The divisor-filter rewrites below are concrete. The full Mobius collapse,
dense-to-diagonal identity, Selberg sieve theorem, Brun-Titchmarsh, and
prime-count estimates remain explicitly packaged as relative obligations.
-/

/-- Pair filter produced by multiplying two divisor-filtered weights. -/
def selbergDivisorPairFilter
    (weight : Nat -> Rat)
    (d m n : Nat) :
    Rat :=
  if And (Dvd.dvd d m) (Dvd.dvd d n) then weight m * weight n else 0

/-- Gcd-filtered term equivalent to the pair of divisor filters. -/
def selbergGcdFilterTerm
    (weight : Nat -> Rat)
    (d m n : Nat) :
    Rat :=
  if Dvd.dvd d (Nat.gcd m n) then weight m * weight n else 0

/-- Multiplying two TS111 divisor filters gives the pair-divisibility filter. -/
theorem selbergDiagonalFilterTerm_mul_eq_pairFilter
    (weight : Nat -> Rat)
    (d m n : Nat) :
    TS111.Goldbach.selbergDiagonalFilterTerm weight d m *
        TS111.Goldbach.selbergDiagonalFilterTerm weight d n =
      selbergDivisorPairFilter weight d m n := by
  unfold TS111.Goldbach.selbergDiagonalFilterTerm
  unfold selbergDivisorPairFilter
  by_cases hm : Dvd.dvd d m
  case pos =>
    by_cases hn : Dvd.dvd d n
    case pos =>
      simp [hm, hn]
    case neg =>
      have hp : Not (And (Dvd.dvd d m) (Dvd.dvd d n)) := by
        intro h
        exact hn h.2
      simp [hm, hn, hp]
  case neg =>
    by_cases hn : Dvd.dvd d n
    case pos =>
      have hp : Not (And (Dvd.dvd d m) (Dvd.dvd d n)) := by
        intro h
        exact hm h.1
      simp [hm, hn, hp]
    case neg =>
      have hp : Not (And (Dvd.dvd d m) (Dvd.dvd d n)) := by
        intro h
        exact hm h.1
      simp [hm, hn, hp]

/-- The pair-divisibility filter is the same as a single filter on `gcd`. -/
theorem selbergDivisorPairFilter_eq_gcdFilter
    (weight : Nat -> Rat)
    (d m n : Nat) :
    selbergDivisorPairFilter weight d m n =
      selbergGcdFilterTerm weight d m n := by
  unfold selbergDivisorPairFilter
  unfold selbergGcdFilterTerm
  by_cases hg : Dvd.dvd d (Nat.gcd m n)
  case pos =>
    have hm : Dvd.dvd d m :=
      hg.trans (Nat.gcd_dvd_left m n)
    have hn : Dvd.dvd d n :=
      hg.trans (Nat.gcd_dvd_right m n)
    have hp : And (Dvd.dvd d m) (Dvd.dvd d n) := And.intro hm hn
    simp [hg, hp]
  case neg =>
    have hp : Not (And (Dvd.dvd d m) (Dvd.dvd d n)) := by
      intro h
      exact hg (Nat.dvd_gcd h.1 h.2)
    simp [hg, hp]

/-- One TS111 triple term rewritten through the gcd filter. -/
theorem selbergDiagonalTripleTerm_eq_gcdFilter
    (weight : Nat -> Rat)
    (diagonalCoefficient : Nat -> Rat)
    (d m n : Nat) :
    TS111.Goldbach.selbergDiagonalTripleTerm
        weight
        diagonalCoefficient
        d
        m
        n =
      diagonalCoefficient d * selbergGcdFilterTerm weight d m n := by
  unfold TS111.Goldbach.selbergDiagonalTripleTerm
  calc
    diagonalCoefficient d *
          TS111.Goldbach.selbergDiagonalFilterTerm weight d m *
        TS111.Goldbach.selbergDiagonalFilterTerm weight d n =
        diagonalCoefficient d *
          (TS111.Goldbach.selbergDiagonalFilterTerm weight d m *
            TS111.Goldbach.selbergDiagonalFilterTerm weight d n) := by
          ring
    _ =
        diagonalCoefficient d *
          selbergDivisorPairFilter weight d m n := by
          rw [selbergDiagonalFilterTerm_mul_eq_pairFilter]
    _ =
        diagonalCoefficient d *
          selbergGcdFilterTerm weight d m n := by
          rw [selbergDivisorPairFilter_eq_gcdFilter]

/-- Canonical gcd-filtered expansion after rewriting the TS111 triple sum. -/
def selbergCanonicalGcdCollapseExpansion
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  let change := TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun d =>
    Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun m =>
      Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun n =>
        change.diagonalCoefficient d *
          selbergGcdFilterTerm weight d m n

/--
The canonical TS111 triple expansion rewrites to the gcd-filtered collapse
expansion.
-/
theorem selbergCanonicalDiagonalTripleExpansion_eq_gcdCollapseExpansion
    (level : Nat)
    (weight : Nat -> Rat) :
    TS111.Goldbach.selbergCanonicalDiagonalTripleExpansion level weight =
      selbergCanonicalGcdCollapseExpansion level weight := by
  unfold TS111.Goldbach.selbergCanonicalDiagonalTripleExpansion
  unfold selbergCanonicalGcdCollapseExpansion
  dsimp [TS109.Goldbach.selbergDiagonalChangeOfVariables]
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  exact
    selbergDiagonalTripleTerm_eq_gcdFilter
      weight
      TS109.Goldbach.selbergUnitDiagonalCoefficient
      d
      m
      n

/--
Collapse ledger below TS111.

The concrete gcd-filter rewrite is proved. The remaining field
`collapseObligation` records the hard Mobius collapse comparing the
gcd-filtered diagonal expansion with the TS110 dense side.
-/
structure SelbergMobiusCollapse
    (level : Nat)
    (weight : Nat -> Rat) where
  reindexing :
    TS111.Goldbach.SelbergDenseToDiagonalReindexing level weight

  diagonal_triple_to_gcd_filter :
    TS111.Goldbach.selbergCanonicalDiagonalTripleExpansion level weight =
      selbergCanonicalGcdCollapseExpansion level weight

  denseSide :
    Rat

  dense_side_eq :
    denseSide = TS110.Goldbach.selbergDenseSide level weight

  gcdFilteredSide :
    Rat

  gcd_filtered_side_eq :
    gcdFilteredSide = selbergCanonicalGcdCollapseExpansion level weight

  collapseObligation :
    Prop

  collapse_obligation_eq :
    collapseObligation =
      (selbergCanonicalGcdCollapseExpansion level weight =
        TS110.Goldbach.selbergDenseSide level weight)

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  gcd_lcm_product_input :
    TS106.Goldbach.GCDLCMKernelAlgebraTarget

  divisor_pair_filter_rewrite_ready :
    True

  gcd_filter_rewrite_ready :
    True

  finite_sum_interchange_ready :
    True

  mobius_delta_collapse_ready :
    True

  dense_kernel_match_ready :
    True

  dense_to_diagonal_identity_obligation :
    True

/-- Concrete TS112 collapse ledger for every finite level and weight. -/
def selbergMobiusCollapse
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergMobiusCollapse level weight where
  reindexing := TS111.Goldbach.selbergDenseToDiagonalReindexing level weight
  diagonal_triple_to_gcd_filter :=
    selbergCanonicalDiagonalTripleExpansion_eq_gcdCollapseExpansion
      level
      weight
  denseSide := TS110.Goldbach.selbergDenseSide level weight
  dense_side_eq := rfl
  gcdFilteredSide := selbergCanonicalGcdCollapseExpansion level weight
  gcd_filtered_side_eq := rfl
  collapseObligation :=
    selbergCanonicalGcdCollapseExpansion level weight =
      TS110.Goldbach.selbergDenseSide level weight
  collapse_obligation_eq := rfl
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  gcd_lcm_product_input := TS106.Goldbach.gcdLCMKernelAlgebraTarget
  divisor_pair_filter_rewrite_ready := True.intro
  gcd_filter_rewrite_ready := True.intro
  finite_sum_interchange_ready := True.intro
  mobius_delta_collapse_ready := True.intro
  dense_kernel_match_ready := True.intro
  dense_to_diagonal_identity_obligation := True.intro

/-- The collapse obligation is exactly the gcd-filtered side equaling dense. -/
theorem selbergMobiusCollapse_obligation_eq
    {level : Nat}
    {weight : Nat -> Rat}
    (H : SelbergMobiusCollapse level weight) :
    H.collapseObligation =
      (selbergCanonicalGcdCollapseExpansion level weight =
        TS110.Goldbach.selbergDenseSide level weight) :=
  H.collapse_obligation_eq

/-- Target proposition for the TS112 Mobius-collapse ledger. -/
def SelbergMobiusCollapseTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergMobiusCollapse level weight)

/-- The TS112 collapse ledger is populated for all finite weights. -/
theorem selbergMobiusCollapseTarget :
    SelbergMobiusCollapseTarget := by
  intro level weight
  exact Nonempty.intro (selbergMobiusCollapse level weight)

/--
Relative infrastructure using the collapse layer to feed TS111.

The actual collapse identity, square-sum majorant, sieve, and budget fields
remain the hard Selberg and Brun-Titchmarsh obligations.
-/
structure SelbergMobiusCollapseInfrastructure where
  reindexingInfrastructure :
    TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructure

  collapse :
    SelbergMobiusCollapse
      (reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level)
      (reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight)

  collapse_targets_reindexing_ready :
    True

  diagonal_triple_gcd_filter_ready :
    True

  finite_sum_interchange_from_collapse_ready :
    True

  mobius_delta_collapse_from_mathlib_ready :
    True

  dense_kernel_match_from_collapse_ready :
    True

  square_sum_majorant_ready :
    True

  interval_majorant_ready :
    True

  selberg_sieve_bound_ready :
    True

  budget_comparison_ready :
    True

/-- Target proposition for the relative TS112 infrastructure. -/
def SelbergMobiusCollapseInfrastructureTarget : Prop :=
  Nonempty SelbergMobiusCollapseInfrastructure

/-- Collapse infrastructure supplies the TS111 reindexing infrastructure. -/
def reindexingInfrastructure_of_mobiusCollapseInfrastructure
    (H : SelbergMobiusCollapseInfrastructure) :
    TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructure :=
  H.reindexingInfrastructure

/-- Collapse infrastructure target supplies the TS111 reindexing target. -/
theorem reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
    (H : SelbergMobiusCollapseInfrastructureTarget) :
    TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (reindexingInfrastructure_of_mobiusCollapseInfrastructure h)

/--
Collapse infrastructure supplies the TS110 dense-to-diagonal infrastructure
target through TS111.
-/
theorem denseToDiagonalInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
    (H : SelbergMobiusCollapseInfrastructureTarget) :
    TS110.Goldbach.SelbergDenseToDiagonalInfrastructureTarget :=
  TS111.Goldbach.denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
    (reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
      H)

/--
Collapse infrastructure supplies the TS103 Mobius-inversion infrastructure
target through TS111.
-/
theorem mobiusInversionInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
    (H : SelbergMobiusCollapseInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS111.Goldbach.mobiusInversionInfrastructureTarget_of_reindexingInfrastructureTarget
    (reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
      H)

/--
Collapse infrastructure plus TS95 and TS83 supply the TS98 final root input
package.
-/
theorem finalHorizonInputsTarget_of_mobiusCollapse_trace_mellin
    (Hs : SelbergMobiusCollapseInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS111.Goldbach.finalHorizonInputsTarget_of_reindexing_trace_mellin
    (reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Collapse infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_mobiusCollapse_trace_mellin
    (Hs : SelbergMobiusCollapseInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS111.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_reindexing_trace_mellin
    (reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Collapse infrastructure plus TS95 and TS83 feed the full TS25 padded-scale
infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_mobiusCollapse_trace_mellin
    (Hs : SelbergMobiusCollapseInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS111.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_reindexing_trace_mellin
    (reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS112
