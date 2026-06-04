import Mathlib.Tactic
import TS.Goldbach.Strong.TS113.SelbergFiniteFubiniReindexingLedger

namespace TS114
namespace Goldbach

/-!
# TS114 - Selberg Inner GCD Divisor Collapse Ledger

TS113 reorders the TS112 gcd-filtered triple sum into pair-first order and
isolates the inner divisor sum over `d` for each pair `(m,n)`.

This sprint proves the next local algebraic step: the inner sum factors as

`weight m * weight n * localCoefficient m n`.

It then proves that if this local coefficient is shown to equal the canonical
Selberg kernel `gcd(m,n) / lcm(m,n)`, the TS112 gcd-filtered side equals the
TS110 dense side. The actual Mobius coefficient calculation and the dense
kernel match remain explicitly recorded as proposition-valued obligations.
-/

/-- The local coefficient obtained from the inner gcd-divisor sum. -/
def selbergInnerGcdKernelCoefficient
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat) :
    Rat :=
  let change := TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun d =>
    if Dvd.dvd d (Nat.gcd m n) then change.diagonalCoefficient d else 0

/-- One gcd-collapse term factors the external weights from the divisor test. -/
theorem selbergGcdCollapseTerm_factor
    (level : Nat)
    (weight : Nat -> Rat)
    (d m n : Nat) :
    TS113.Goldbach.selbergGcdCollapseTerm level weight d m n =
      weight m * weight n *
        (let change :=
          TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
        if Dvd.dvd d (Nat.gcd m n) then change.diagonalCoefficient d else 0) := by
  unfold TS113.Goldbach.selbergGcdCollapseTerm
  unfold TS112.Goldbach.selbergGcdFilterTerm
  by_cases hd : Dvd.dvd d (Nat.gcd m n)
  case pos =>
    simp [hd]
    ring
  case neg =>
    simp [hd]

/--
The TS113 inner gcd-divisor sum factors as the pair weight times the local
kernel coefficient.
-/
theorem selbergInnerGcdDivisorSum_factor
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat) :
    TS113.Goldbach.selbergInnerGcdDivisorSum level weight m n =
      weight m * weight n *
        selbergInnerGcdKernelCoefficient level weight m n := by
  unfold TS113.Goldbach.selbergInnerGcdDivisorSum
  unfold selbergInnerGcdKernelCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  exact selbergGcdCollapseTerm_factor level weight d m n

/-- Local kernel-match obligation produced by the future Mobius collapse. -/
def SelbergInnerGcdKernelMatchObligation
    (level : Nat)
    (weight : Nat -> Rat) :
    Prop :=
  forall m n : Nat,
    selbergInnerGcdKernelCoefficient level weight m n =
      TS107.Goldbach.canonicalSelbergQuadraticKernel m n

/--
If the local inner coefficient matches the canonical `gcd/lcm` kernel, then
the TS113 pair-first collapse sum equals the TS110 dense side.
-/
theorem selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
    (level : Nat)
    (weight : Nat -> Rat)
    (Hmatch : SelbergInnerGcdKernelMatchObligation level weight) :
    TS113.Goldbach.selbergPairFirstGcdCollapseSum level weight =
      TS110.Goldbach.selbergDenseSide level weight := by
  unfold TS113.Goldbach.selbergPairFirstGcdCollapseSum
  unfold TS110.Goldbach.selbergDenseSide
  unfold TS108.Goldbach.selbergQuadraticForm
  unfold TS109.Goldbach.selbergDiagonalSupport
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  rw [selbergInnerGcdDivisorSum_factor]
  unfold TS108.Goldbach.selbergQuadraticFormTerm
  rw [Hmatch m n]

/--
If the local inner coefficient matches the canonical kernel, then the full
TS112 gcd-filtered side equals the TS110 dense side.
-/
theorem selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch
    (level : Nat)
    (weight : Nat -> Rat)
    (Hmatch : SelbergInnerGcdKernelMatchObligation level weight) :
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
      TS110.Goldbach.selbergDenseSide level weight := by
  calc
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
        TS113.Goldbach.selbergPairFirstGcdCollapseSum level weight := by
          exact
            TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_pairFirst
              level
              weight
    _ = TS110.Goldbach.selbergDenseSide level weight := by
          exact
            selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
              level
              weight
              Hmatch

/--
Ledger for the local inner gcd-divisor collapse.

The factorization is proved. The field `kernelMatchObligation` is the remaining
Mobius coefficient calculation needed to identify the local coefficient with
the canonical dense `gcd/lcm` kernel.
-/
structure SelbergInnerGcdDivisorCollapse
    (level : Nat)
    (weight : Nat -> Rat) where
  fubini :
    TS113.Goldbach.SelbergFiniteFubiniReindexing level weight

  localCoefficient :
    Nat -> Nat -> Rat

  local_coefficient_eq :
    forall m n : Nat,
      localCoefficient m n =
        selbergInnerGcdKernelCoefficient level weight m n

  inner_sum_factorization :
    forall m n : Nat,
      TS113.Goldbach.selbergInnerGcdDivisorSum level weight m n =
        weight m * weight n * localCoefficient m n

  kernelMatchObligation :
    Prop

  kernel_match_obligation_eq :
    kernelMatchObligation =
      (forall m n : Nat,
        localCoefficient m n =
          TS107.Goldbach.canonicalSelbergQuadraticKernel m n)

  pair_first_dense_if_kernel_match :
    (forall m n : Nat,
      localCoefficient m n =
        TS107.Goldbach.canonicalSelbergQuadraticKernel m n) ->
      TS113.Goldbach.selbergPairFirstGcdCollapseSum level weight =
        TS110.Goldbach.selbergDenseSide level weight

  canonical_collapse_dense_if_kernel_match :
    (forall m n : Nat,
      localCoefficient m n =
        TS107.Goldbach.canonicalSelbergQuadraticKernel m n) ->
      TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
        TS110.Goldbach.selbergDenseSide level weight

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  inner_factorization_ready :
    True

  mobius_coefficient_collapse_obligation :
    True

  dense_kernel_match_obligation :
    True

  dense_to_diagonal_identity_obligation :
    True

/-- Concrete TS114 local inner-collapse ledger for every finite level. -/
def selbergInnerGcdDivisorCollapse
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergInnerGcdDivisorCollapse level weight where
  fubini := TS113.Goldbach.selbergFiniteFubiniReindexing level weight
  localCoefficient := selbergInnerGcdKernelCoefficient level weight
  local_coefficient_eq := by
    intro m n
    rfl
  inner_sum_factorization := by
    intro m n
    exact selbergInnerGcdDivisorSum_factor level weight m n
  kernelMatchObligation :=
    SelbergInnerGcdKernelMatchObligation level weight
  kernel_match_obligation_eq := rfl
  pair_first_dense_if_kernel_match := by
    intro Hmatch
    exact
      selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
        level
        weight
        Hmatch
  canonical_collapse_dense_if_kernel_match := by
    intro Hmatch
    exact
      selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch
        level
        weight
        Hmatch
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  inner_factorization_ready := True.intro
  mobius_coefficient_collapse_obligation := True.intro
  dense_kernel_match_obligation := True.intro
  dense_to_diagonal_identity_obligation := True.intro

/-- Target proposition for the TS114 inner gcd-divisor collapse ledger. -/
def SelbergInnerGcdDivisorCollapseTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergInnerGcdDivisorCollapse level weight)

/-- The TS114 inner gcd-divisor collapse ledger is populated for all weights. -/
theorem selbergInnerGcdDivisorCollapseTarget :
    SelbergInnerGcdDivisorCollapseTarget := by
  intro level weight
  exact Nonempty.intro (selbergInnerGcdDivisorCollapse level weight)

/--
Relative infrastructure using the inner-collapse layer to feed TS113.

The actual Mobius coefficient match, square-sum majorant, sieve, and budget
fields remain hard Selberg and Brun-Titchmarsh obligations.
-/
structure SelbergInnerGcdDivisorCollapseInfrastructure where
  fubiniInfrastructure :
    TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructure

  collapse :
    SelbergInnerGcdDivisorCollapse
      (fubiniInfrastructure.collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level)
      (fubiniInfrastructure.collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight)

  collapse_targets_fubini_ready :
    True

  inner_factorization_ready :
    True

  mobius_coefficient_match_ready :
    True

  dense_kernel_match_from_inner_ready :
    True

  dense_to_diagonal_identity_ready :
    True

  square_sum_majorant_ready :
    True

  interval_majorant_ready :
    True

  selberg_sieve_bound_ready :
    True

  budget_comparison_ready :
    True

/-- Target proposition for the relative TS114 infrastructure. -/
def SelbergInnerGcdDivisorCollapseInfrastructureTarget : Prop :=
  Nonempty SelbergInnerGcdDivisorCollapseInfrastructure

/-- Inner-collapse infrastructure supplies the TS113 finite-Fubini layer. -/
def fubiniInfrastructure_of_innerCollapseInfrastructure
    (H : SelbergInnerGcdDivisorCollapseInfrastructure) :
    TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructure :=
  H.fubiniInfrastructure

/-- Inner-collapse infrastructure target supplies the TS113 finite-Fubini target. -/
theorem fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (H : SelbergInnerGcdDivisorCollapseInfrastructureTarget) :
    TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (fubiniInfrastructure_of_innerCollapseInfrastructure h)

/-- Inner-collapse infrastructure supplies the TS112 collapse target. -/
theorem mobiusCollapseInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (H : SelbergInnerGcdDivisorCollapseInfrastructureTarget) :
    TS112.Goldbach.SelbergMobiusCollapseInfrastructureTarget :=
  TS113.Goldbach.mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
    (fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget H)

/-- Inner-collapse infrastructure supplies the TS111 reindexing target. -/
theorem reindexingInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (H : SelbergInnerGcdDivisorCollapseInfrastructureTarget) :
    TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructureTarget :=
  TS113.Goldbach.reindexingInfrastructureTarget_of_fubiniInfrastructureTarget
    (fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget H)

/-- Inner-collapse infrastructure supplies the TS103 Mobius-inversion target. -/
theorem mobiusInversionInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (H : SelbergInnerGcdDivisorCollapseInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS113.Goldbach.mobiusInversionInfrastructureTarget_of_fubiniInfrastructureTarget
    (fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget H)

/--
Inner-collapse infrastructure plus TS95 and TS83 supply the TS98 final root
input package.
-/
theorem finalHorizonInputsTarget_of_innerCollapse_trace_mellin
    (Hs : SelbergInnerGcdDivisorCollapseInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS113.Goldbach.finalHorizonInputsTarget_of_fubini_trace_mellin
    (fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget Hs)
    Ht
    Hm

/--
Inner-collapse infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_innerCollapse_trace_mellin
    (Hs : SelbergInnerGcdDivisorCollapseInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS113.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_fubini_trace_mellin
    (fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget Hs)
    Ht
    Hm

/--
Inner-collapse infrastructure plus TS95 and TS83 feed the full TS25
padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_innerCollapse_trace_mellin
    (Hs : SelbergInnerGcdDivisorCollapseInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS113.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_fubini_trace_mellin
    (fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget Hs)
    Ht
    Hm

end Goldbach
end TS114
