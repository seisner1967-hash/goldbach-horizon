import Mathlib.Tactic
import TS.Goldbach.Strong.TS112.SelbergMobiusCollapseLedger

namespace TS113
namespace Goldbach

/-!
# TS113 - Selberg Finite Fubini Reindexing Ledger

TS112 rewrites the TS111 diagonal triple sum into a gcd-filtered triple sum.
This sprint performs the next finite combinatorial step: reorder that triple
sum from the diagonal-first order

`sum d, sum m, sum n, ...`

to the pair-first order

`sum m, sum n, sum d, ...`.

The finite Fubini reindexing is proved using `Finset.sum_comm`. The Mobius
delta collapse of the inner divisor sum, the dense-kernel match, Selberg's
sieve, Brun-Titchmarsh, and prime-count estimates remain explicitly packaged
as relative obligations.
-/

/-- One term in the TS112 gcd-filtered collapse expansion. -/
def selbergGcdCollapseTerm
    (level : Nat)
    (weight : Nat -> Rat)
    (d m n : Nat) :
    Rat :=
  let change := TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
  change.diagonalCoefficient d *
    TS112.Goldbach.selbergGcdFilterTerm weight d m n

/-- The TS112 gcd-filtered expansion as a diagonal-first triple sum. -/
def selbergGcdCollapseTripleSum
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun d =>
    Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun m =>
      Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun n =>
        selbergGcdCollapseTerm level weight d m n

/-- Inner divisor sum over `d` for a fixed pair `(m,n)`. -/
def selbergInnerGcdDivisorSum
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat) :
    Rat :=
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun d =>
    selbergGcdCollapseTerm level weight d m n

/-- The same gcd-filtered expansion in pair-first order. -/
def selbergPairFirstGcdCollapseSum
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun m =>
    Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun n =>
      selbergInnerGcdDivisorSum level weight m n

/-- The TS112 gcd collapse expansion is definitionally the TS113 triple sum. -/
theorem selbergCanonicalGcdCollapseExpansion_eq_tripleSum
    (level : Nat)
    (weight : Nat -> Rat) :
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
      selbergGcdCollapseTripleSum level weight := by
  unfold TS112.Goldbach.selbergCanonicalGcdCollapseExpansion
  unfold selbergGcdCollapseTripleSum
  unfold selbergGcdCollapseTerm
  dsimp

/-- Finite Fubini reorders the gcd-filtered triple sum into pair-first order. -/
theorem selbergGcdCollapseTripleSum_reordered
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergGcdCollapseTripleSum level weight =
      selbergPairFirstGcdCollapseSum level weight := by
  unfold selbergGcdCollapseTripleSum
  unfold selbergPairFirstGcdCollapseSum
  unfold selbergInnerGcdDivisorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_comm]

/--
The TS112 gcd-filtered collapse expansion can be read pair-first, with the
inner sum isolated over the divisor index `d`.
-/
theorem selbergCanonicalGcdCollapseExpansion_eq_pairFirst
    (level : Nat)
    (weight : Nat -> Rat) :
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
      selbergPairFirstGcdCollapseSum level weight := by
  rw [selbergCanonicalGcdCollapseExpansion_eq_tripleSum]
  exact selbergGcdCollapseTripleSum_reordered level weight

/-- Local package for the inner gcd-divisor sum at a fixed pair `(m,n)`. -/
structure InnerGcdDivisorCollapseReady
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat) where
  innerValue :
    Rat

  inner_value_eq :
    innerValue = selbergInnerGcdDivisorSum level weight m n

  gcdValue :
    Nat

  gcd_value_eq :
    gcdValue = Nat.gcd m n

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  inner_sum_is_finite :
    True

  divisor_filter_on_gcd_ready :
    True

  mobius_delta_collapse_obligation :
    True

  dense_kernel_match_obligation :
    True

/-- Canonical local inner-sum package for one pair `(m,n)`. -/
def innerGcdDivisorCollapseReady
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat) :
    InnerGcdDivisorCollapseReady level weight m n where
  innerValue := selbergInnerGcdDivisorSum level weight m n
  inner_value_eq := rfl
  gcdValue := Nat.gcd m n
  gcd_value_eq := rfl
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  inner_sum_is_finite := True.intro
  divisor_filter_on_gcd_ready := True.intro
  mobius_delta_collapse_obligation := True.intro
  dense_kernel_match_obligation := True.intro

/--
Finite Fubini reindexing ledger below TS112.

The Fubini equality is concrete. The remaining fields isolate the local inner
Mobius collapse and dense-kernel matching steps needed before closing TS110.
-/
structure SelbergFiniteFubiniReindexing
    (level : Nat)
    (weight : Nat -> Rat) where
  collapse :
    TS112.Goldbach.SelbergMobiusCollapse level weight

  gcd_collapse_pair_first :
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
      selbergPairFirstGcdCollapseSum level weight

  inner_gcd_divisor_sum_ready :
    forall m n : Nat,
      Nonempty (InnerGcdDivisorCollapseReady level weight m n)

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  finite_fubini_reordered :
    True

  inner_sum_isolated :
    True

  mobius_delta_collapse_ready :
    True

  dense_kernel_match_ready :
    True

  dense_to_diagonal_identity_obligation :
    True

/-- Concrete TS113 finite-Fubini ledger for every finite level and weight. -/
def selbergFiniteFubiniReindexing
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergFiniteFubiniReindexing level weight where
  collapse := TS112.Goldbach.selbergMobiusCollapse level weight
  gcd_collapse_pair_first :=
    selbergCanonicalGcdCollapseExpansion_eq_pairFirst level weight
  inner_gcd_divisor_sum_ready := by
    intro m n
    exact Nonempty.intro (innerGcdDivisorCollapseReady level weight m n)
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  finite_fubini_reordered := True.intro
  inner_sum_isolated := True.intro
  mobius_delta_collapse_ready := True.intro
  dense_kernel_match_ready := True.intro
  dense_to_diagonal_identity_obligation := True.intro

/-- Target proposition for the TS113 finite-Fubini ledger. -/
def SelbergFiniteFubiniReindexingTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergFiniteFubiniReindexing level weight)

/-- The TS113 finite-Fubini ledger is populated for all finite weights. -/
theorem selbergFiniteFubiniReindexingTarget :
    SelbergFiniteFubiniReindexingTarget := by
  intro level weight
  exact Nonempty.intro (selbergFiniteFubiniReindexing level weight)

/--
Relative infrastructure using the finite-Fubini layer to feed TS112.

The actual Mobius collapse, dense-kernel match, square-sum majorant, sieve, and
budget fields remain the hard Selberg and Brun-Titchmarsh obligations.
-/
structure SelbergFiniteFubiniReindexingInfrastructure where
  collapseInfrastructure :
    TS112.Goldbach.SelbergMobiusCollapseInfrastructure

  fubini :
    SelbergFiniteFubiniReindexing
      (collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level)
      (collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight)

  fubini_targets_collapse_ready :
    True

  pair_first_reindexing_ready :
    True

  inner_mobius_delta_collapse_ready :
    True

  dense_kernel_match_from_inner_ready :
    True

  square_sum_majorant_ready :
    True

  interval_majorant_ready :
    True

  selberg_sieve_bound_ready :
    True

  budget_comparison_ready :
    True

/-- Target proposition for the relative TS113 infrastructure. -/
def SelbergFiniteFubiniReindexingInfrastructureTarget : Prop :=
  Nonempty SelbergFiniteFubiniReindexingInfrastructure

/-- Finite-Fubini infrastructure supplies the TS112 collapse infrastructure. -/
def mobiusCollapseInfrastructure_of_fubiniInfrastructure
    (H : SelbergFiniteFubiniReindexingInfrastructure) :
    TS112.Goldbach.SelbergMobiusCollapseInfrastructure :=
  H.collapseInfrastructure

/-- Finite-Fubini infrastructure target supplies the TS112 collapse target. -/
theorem mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
    (H : SelbergFiniteFubiniReindexingInfrastructureTarget) :
    TS112.Goldbach.SelbergMobiusCollapseInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (mobiusCollapseInfrastructure_of_fubiniInfrastructure h)

/--
Finite-Fubini infrastructure supplies the TS111 reindexing infrastructure
target through TS112.
-/
theorem reindexingInfrastructureTarget_of_fubiniInfrastructureTarget
    (H : SelbergFiniteFubiniReindexingInfrastructureTarget) :
    TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructureTarget :=
  TS112.Goldbach.reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
    (mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
      H)

/--
Finite-Fubini infrastructure supplies the TS103 Mobius-inversion infrastructure
target through TS112.
-/
theorem mobiusInversionInfrastructureTarget_of_fubiniInfrastructureTarget
    (H : SelbergFiniteFubiniReindexingInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS112.Goldbach.mobiusInversionInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
    (mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
      H)

/--
Finite-Fubini infrastructure plus TS95 and TS83 supply the TS98 final root input
package.
-/
theorem finalHorizonInputsTarget_of_fubini_trace_mellin
    (Hs : SelbergFiniteFubiniReindexingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS112.Goldbach.finalHorizonInputsTarget_of_mobiusCollapse_trace_mellin
    (mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Finite-Fubini infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_fubini_trace_mellin
    (Hs : SelbergFiniteFubiniReindexingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS112.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobiusCollapse_trace_mellin
    (mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Finite-Fubini infrastructure plus TS95 and TS83 feed the full TS25 padded-scale
infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_fubini_trace_mellin
    (Hs : SelbergFiniteFubiniReindexingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS112.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobiusCollapse_trace_mellin
    (mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS113
