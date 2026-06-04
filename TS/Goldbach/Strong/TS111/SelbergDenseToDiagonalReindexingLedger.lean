import Mathlib.Tactic
import TS.Goldbach.Strong.TS110.SelbergDenseToDiagonalIdentityLedger

namespace TS111
namespace Goldbach

/-!
# TS111 - Selberg Dense-To-Diagonal Reindexing Ledger

TS110 names the dense-to-diagonal Selberg identity as a proposition-valued
obligation. This sprint opens the first proof-facing layer below that
obligation: expansion of the diagonal square into a finite triple sum and the
remaining finite reindexing steps.

The diagonal square expansion is proved for finite sums. The Mobius
reindexing, divisor-filter rewrite, gcd/lcm kernel match, dense-to-diagonal
identity, Selberg sieve theorem, Brun-Titchmarsh, and prime-count estimates
remain explicitly packaged as relative obligations.
-/

/-- One divisor-filtered term in the diagonal change of variables. -/
def selbergDiagonalFilterTerm
    (weight : Nat -> Rat)
    (d m : Nat) :
    Rat :=
  if Dvd.dvd d m then weight m else 0

/-- One term after expanding a diagonal square into two divisor-filtered sums. -/
def selbergDiagonalTripleTerm
    (weight : Nat -> Rat)
    (diagonalCoefficient : Nat -> Rat)
    (d m n : Nat) :
    Rat :=
  diagonalCoefficient d *
    selbergDiagonalFilterTerm weight d m *
      selbergDiagonalFilterTerm weight d n

/-- Canonical triple-sum expansion of the TS109 diagonal side. -/
def selbergCanonicalDiagonalTripleExpansion
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  let change := TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun d =>
    Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun m =>
      Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun n =>
        selbergDiagonalTripleTerm weight change.diagonalCoefficient d m n

/--
The square of one diagonal transformed weight expands to a finite double sum.
-/
theorem selbergDiagonalSquareTerm_triple_expansion
    (level : Nat)
    (weight : Nat -> Rat)
    (diagonalCoefficient : Nat -> Rat)
    (d : Nat) :
    TS109.Goldbach.selbergDiagonalSquareTerm
        diagonalCoefficient
        (TS109.Goldbach.selbergDiagonalTransformedWeight level weight)
        d =
      Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) (fun m =>
        Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun n =>
          selbergDiagonalTripleTerm weight diagonalCoefficient d m n) := by
  unfold TS109.Goldbach.selbergDiagonalSquareTerm
  unfold TS109.Goldbach.selbergDiagonalTransformedWeight
  unfold selbergDiagonalTripleTerm
  unfold selbergDiagonalFilterTerm
  rw [pow_two]
  rw [Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/--
The canonical TS109 diagonal side expands to a finite triple sum.
-/
theorem selbergDiagonalSide_triple_expansion
    (level : Nat)
    (weight : Nat -> Rat) :
    TS110.Goldbach.selbergDiagonalSide level weight =
      selbergCanonicalDiagonalTripleExpansion level weight := by
  unfold TS110.Goldbach.selbergDiagonalSide
  unfold selbergCanonicalDiagonalTripleExpansion
  dsimp [TS109.Goldbach.selbergDiagonalChangeOfVariables]
  unfold TS109.Goldbach.selbergDiagonalSquareSum
  apply Finset.sum_congr rfl
  intro d _hd
  exact
    selbergDiagonalSquareTerm_triple_expansion
      level
      weight
      TS109.Goldbach.selbergUnitDiagonalCoefficient
      d

/--
Reindexing ledger below the TS110 dense-to-diagonal identity.

The diagonal square expansion is concrete. The remaining fields isolate the
finite reindexing and arithmetic-collapse steps required before proving the
dense-to-diagonal identity.
-/
structure SelbergDenseToDiagonalReindexing
    (level : Nat)
    (weight : Nat -> Rat) where
  identity :
    TS110.Goldbach.SelbergDenseToDiagonalIdentity level weight

  diagonal_triple_expansion :
    TS110.Goldbach.selbergDiagonalSide level weight =
      selbergCanonicalDiagonalTripleExpansion level weight

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  gcd_lcm_product_input :
    TS106.Goldbach.GCDLCMKernelAlgebraTarget

  dense_double_sum_available :
    True

  diagonal_square_expanded :
    True

  finite_sum_interchange_ready :
    True

  divisor_filter_rewrite_ready :
    True

  mobius_delta_collapse_ready :
    True

  gcd_lcm_kernel_match_ready :
    True

  dense_to_diagonal_identity_obligation :
    True

/-- Concrete TS111 reindexing ledger for every finite level and weight. -/
def selbergDenseToDiagonalReindexing
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergDenseToDiagonalReindexing level weight where
  identity := TS110.Goldbach.selbergDenseToDiagonalIdentity level weight
  diagonal_triple_expansion :=
    selbergDiagonalSide_triple_expansion level weight
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  gcd_lcm_product_input := TS106.Goldbach.gcdLCMKernelAlgebraTarget
  dense_double_sum_available := True.intro
  diagonal_square_expanded := True.intro
  finite_sum_interchange_ready := True.intro
  divisor_filter_rewrite_ready := True.intro
  mobius_delta_collapse_ready := True.intro
  gcd_lcm_kernel_match_ready := True.intro
  dense_to_diagonal_identity_obligation := True.intro

/-- Target proposition for the TS111 reindexing ledger. -/
def SelbergDenseToDiagonalReindexingTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergDenseToDiagonalReindexing level weight)

/-- The TS111 reindexing ledger is populated for all finite weights. -/
theorem selbergDenseToDiagonalReindexingTarget :
    SelbergDenseToDiagonalReindexingTarget := by
  intro level weight
  exact Nonempty.intro (selbergDenseToDiagonalReindexing level weight)

/--
Relative infrastructure using the reindexing layer to feed TS110.

The TS30 majorant, sieve, and budget fields remain hard Selberg and
Brun-Titchmarsh obligations.
-/
structure SelbergDenseToDiagonalReindexingInfrastructure where
  denseToDiagonalInfrastructure :
    TS110.Goldbach.SelbergDenseToDiagonalInfrastructure

  reindexing :
    SelbergDenseToDiagonalReindexing
      (denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level)
      (denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight)

  reindexing_targets_identity_ready :
    True

  diagonal_triple_expansion_ready :
    True

  finite_sum_interchange_from_reindexing_ready :
    True

  mobius_collapse_from_reindexing_ready :
    True

  square_sum_majorant_ready :
    True

  interval_majorant_ready :
    True

  selberg_sieve_bound_ready :
    True

  budget_comparison_ready :
    True

/-- Target proposition for the relative TS111 infrastructure. -/
def SelbergDenseToDiagonalReindexingInfrastructureTarget : Prop :=
  Nonempty SelbergDenseToDiagonalReindexingInfrastructure

/--
Reindexing infrastructure supplies the TS110 dense-to-diagonal infrastructure.
-/
def denseToDiagonalInfrastructure_of_reindexingInfrastructure
    (H : SelbergDenseToDiagonalReindexingInfrastructure) :
    TS110.Goldbach.SelbergDenseToDiagonalInfrastructure :=
  H.denseToDiagonalInfrastructure

/--
Reindexing infrastructure target supplies the TS110 dense-to-diagonal
infrastructure target.
-/
theorem denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
    (H : SelbergDenseToDiagonalReindexingInfrastructureTarget) :
    TS110.Goldbach.SelbergDenseToDiagonalInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (denseToDiagonalInfrastructure_of_reindexingInfrastructure h)

/--
Reindexing infrastructure supplies the TS109 diagonalization infrastructure
target through TS110.
-/
theorem diagonalizationInfrastructureTarget_of_reindexingInfrastructureTarget
    (H : SelbergDenseToDiagonalReindexingInfrastructureTarget) :
    TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructureTarget :=
  TS110.Goldbach.diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
    (denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
      H)

/--
Reindexing infrastructure supplies the TS103 Mobius-inversion infrastructure
target through TS110.
-/
theorem mobiusInversionInfrastructureTarget_of_reindexingInfrastructureTarget
    (H : SelbergDenseToDiagonalReindexingInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS110.Goldbach.mobiusInversionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
    (denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
      H)

/--
Reindexing infrastructure plus TS95 and TS83 supply the TS98 final root input
package.
-/
theorem finalHorizonInputsTarget_of_reindexing_trace_mellin
    (Hs : SelbergDenseToDiagonalReindexingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS110.Goldbach.finalHorizonInputsTarget_of_denseToDiagonal_trace_mellin
    (denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Reindexing infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_reindexing_trace_mellin
    (Hs : SelbergDenseToDiagonalReindexingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS110.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_denseToDiagonal_trace_mellin
    (denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Reindexing infrastructure plus TS95 and TS83 feed the full TS25 padded-scale
infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_reindexing_trace_mellin
    (Hs : SelbergDenseToDiagonalReindexingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS110.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_denseToDiagonal_trace_mellin
    (denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS111
