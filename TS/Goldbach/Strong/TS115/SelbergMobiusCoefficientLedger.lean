import Mathlib.Tactic
import TS.Goldbach.Strong.TS114.SelbergInnerGcdDivisorCollapseLedger

namespace TS115
namespace Goldbach

/-!
# TS115 - Selberg Mobius Coefficient Ledger

TS114 factors each pairwise inner gcd-divisor sum into an external pair weight
and a local coefficient. This sprint reduces that local coefficient to a
one-variable coefficient depending on `gcd(m,n)`, rewrites it as a filtered
finite divisor sum, and records the remaining coefficient-to-kernel match as
the exact local arithmetic obligation.

The actual Mobius coefficient calculation, dense-to-diagonal identity,
square-sum majorant, Selberg sieve theorem, Brun-Titchmarsh, and prime-count
estimates remain explicitly packaged as relative obligations.
-/

/-- Diagonal support filtered by divisibility into a fixed gcd value. -/
def selbergGcdCoefficientSupport
    (level : Nat)
    (g : Nat) :
    Finset Nat :=
  (TS109.Goldbach.selbergDiagonalSupport level).filter fun d =>
    Dvd.dvd d g

/-- One-variable coefficient obtained from the inner gcd-divisor sum. -/
def selbergGcdCoefficient
    (level : Nat)
    (weight : Nat -> Rat)
    (g : Nat) :
    Rat :=
  let change := TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
  Finset.sum (TS109.Goldbach.selbergDiagonalSupport level) fun d =>
    if Dvd.dvd d g then change.diagonalCoefficient d else 0

/--
The TS114 local coefficient depends on the pair `(m,n)` only through
`Nat.gcd m n`.
-/
theorem selbergInnerGcdKernelCoefficient_eq_gcdCoefficient
    (level : Nat)
    (weight : Nat -> Rat)
    (m n : Nat) :
    TS114.Goldbach.selbergInnerGcdKernelCoefficient level weight m n =
      selbergGcdCoefficient level weight (Nat.gcd m n) :=
  rfl

/-- The one-variable coefficient is the filtered finite sum over `d | g`. -/
theorem selbergGcdCoefficient_eq_filter_sum
    (level : Nat)
    (weight : Nat -> Rat)
    (g : Nat) :
    selbergGcdCoefficient level weight g =
      Finset.sum (selbergGcdCoefficientSupport level g) fun d =>
        (TS109.Goldbach.selbergDiagonalChangeOfVariables
          level
          weight).diagonalCoefficient d := by
  unfold selbergGcdCoefficient
  unfold selbergGcdCoefficientSupport
  rw [Finset.sum_filter]

/--
The remaining local coefficient obligation: the gcd-indexed coefficient must
match the canonical dense `gcd/lcm` kernel for every pair.
-/
def SelbergGcdCoefficientKernelMatchObligation
    (level : Nat)
    (weight : Nat -> Rat) :
    Prop :=
  forall m n : Nat,
    selbergGcdCoefficient level weight (Nat.gcd m n) =
      TS107.Goldbach.canonicalSelbergQuadraticKernel m n

/-- The TS115 coefficient match supplies the TS114 local kernel match. -/
theorem innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
    (level : Nat)
    (weight : Nat -> Rat)
    (Hmatch : SelbergGcdCoefficientKernelMatchObligation level weight) :
    TS114.Goldbach.SelbergInnerGcdKernelMatchObligation level weight := by
  intro m n
  rw [selbergInnerGcdKernelCoefficient_eq_gcdCoefficient]
  exact Hmatch m n

/--
The TS115 coefficient match closes the TS113 pair-first side conditionally
through TS114.
-/
theorem selbergPairFirstGcdCollapseSum_eq_denseSide_of_gcdCoefficientKernelMatch
    (level : Nat)
    (weight : Nat -> Rat)
    (Hmatch : SelbergGcdCoefficientKernelMatchObligation level weight) :
    TS113.Goldbach.selbergPairFirstGcdCollapseSum level weight =
      TS110.Goldbach.selbergDenseSide level weight :=
  TS114.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
    level
    weight
    (innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
      level
      weight
      Hmatch)

/--
The TS115 coefficient match closes the TS112 gcd-filtered side conditionally
through TS114.
-/
theorem selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch
    (level : Nat)
    (weight : Nat -> Rat)
    (Hmatch : SelbergGcdCoefficientKernelMatchObligation level weight) :
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
      TS110.Goldbach.selbergDenseSide level weight :=
  TS114.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch
    level
    weight
    (innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
      level
      weight
      Hmatch)

/--
Ledger for the Selberg Mobius coefficient layer.

The one-variable and filtered-sum rewrites are concrete. The remaining field
`kernelMatchObligation` is the arithmetic coefficient calculation needed to
identify the local coefficient with the canonical dense `gcd/lcm` kernel.
-/
structure SelbergMobiusCoefficient
    (level : Nat)
    (weight : Nat -> Rat) where
  innerCollapse :
    TS114.Goldbach.SelbergInnerGcdDivisorCollapse level weight

  gcdCoefficient :
    Nat -> Rat

  gcd_coefficient_eq :
    forall g : Nat,
      gcdCoefficient g = selbergGcdCoefficient level weight g

  local_coefficient_depends_on_gcd :
    forall m n : Nat,
      TS114.Goldbach.selbergInnerGcdKernelCoefficient level weight m n =
        gcdCoefficient (Nat.gcd m n)

  filtered_sum_expansion :
    forall g : Nat,
      gcdCoefficient g =
        Finset.sum (selbergGcdCoefficientSupport level g) fun d =>
          (TS109.Goldbach.selbergDiagonalChangeOfVariables
            level
            weight).diagonalCoefficient d

  kernelMatchObligation :
    Prop

  kernel_match_obligation_eq :
    kernelMatchObligation =
      (forall m n : Nat,
        gcdCoefficient (Nat.gcd m n) =
          TS107.Goldbach.canonicalSelbergQuadraticKernel m n)

  inner_kernel_match_of_coefficient_match :
    (forall m n : Nat,
      gcdCoefficient (Nat.gcd m n) =
        TS107.Goldbach.canonicalSelbergQuadraticKernel m n) ->
      TS114.Goldbach.SelbergInnerGcdKernelMatchObligation level weight

  canonical_collapse_dense_if_coefficient_match :
    (forall m n : Nat,
      gcdCoefficient (Nat.gcd m n) =
        TS107.Goldbach.canonicalSelbergQuadraticKernel m n) ->
      TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
        TS110.Goldbach.selbergDenseSide level weight

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  coefficient_gcd_reduction_ready :
    True

  filtered_sum_ready :
    True

  mobius_coefficient_calculation_obligation :
    True

  dense_kernel_match_obligation :
    True

  dense_to_diagonal_identity_obligation :
    True

/-- Concrete TS115 coefficient ledger for every finite level and weight. -/
def selbergMobiusCoefficient
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergMobiusCoefficient level weight where
  innerCollapse :=
    TS114.Goldbach.selbergInnerGcdDivisorCollapse level weight
  gcdCoefficient := selbergGcdCoefficient level weight
  gcd_coefficient_eq := by
    intro g
    rfl
  local_coefficient_depends_on_gcd := by
    intro m n
    exact
      selbergInnerGcdKernelCoefficient_eq_gcdCoefficient
        level
        weight
        m
        n
  filtered_sum_expansion := by
    intro g
    exact selbergGcdCoefficient_eq_filter_sum level weight g
  kernelMatchObligation :=
    SelbergGcdCoefficientKernelMatchObligation level weight
  kernel_match_obligation_eq := rfl
  inner_kernel_match_of_coefficient_match := by
    intro Hmatch
    exact
      innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
        level
        weight
        Hmatch
  canonical_collapse_dense_if_coefficient_match := by
    intro Hmatch
    exact
      selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch
        level
        weight
        Hmatch
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  coefficient_gcd_reduction_ready := True.intro
  filtered_sum_ready := True.intro
  mobius_coefficient_calculation_obligation := True.intro
  dense_kernel_match_obligation := True.intro
  dense_to_diagonal_identity_obligation := True.intro

/-- Target proposition for the TS115 Mobius coefficient ledger. -/
def SelbergMobiusCoefficientTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergMobiusCoefficient level weight)

/-- The TS115 Mobius coefficient ledger is populated for all weights. -/
theorem selbergMobiusCoefficientTarget :
    SelbergMobiusCoefficientTarget := by
  intro level weight
  exact Nonempty.intro (selbergMobiusCoefficient level weight)

/--
Relative infrastructure using the coefficient layer to feed TS114.

The actual coefficient calculation, square-sum majorant, sieve, and budget
fields remain hard Selberg and Brun-Titchmarsh obligations.
-/
structure SelbergMobiusCoefficientInfrastructure where
  innerCollapseInfrastructure :
    TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructure

  coefficient :
    SelbergMobiusCoefficient
      (innerCollapseInfrastructure.fubiniInfrastructure.collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level)
      (innerCollapseInfrastructure.fubiniInfrastructure.collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight)

  coefficient_targets_inner_collapse_ready :
    True

  coefficient_gcd_reduction_ready :
    True

  mobius_coefficient_match_ready :
    True

  dense_kernel_match_from_coefficient_ready :
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

/-- Target proposition for the relative TS115 infrastructure. -/
def SelbergMobiusCoefficientInfrastructureTarget : Prop :=
  Nonempty SelbergMobiusCoefficientInfrastructure

/-- Coefficient infrastructure supplies the TS114 inner-collapse layer. -/
def innerCollapseInfrastructure_of_coefficientInfrastructure
    (H : SelbergMobiusCoefficientInfrastructure) :
    TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructure :=
  H.innerCollapseInfrastructure

/-- Coefficient infrastructure target supplies the TS114 target. -/
theorem innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
    (H : SelbergMobiusCoefficientInfrastructureTarget) :
    TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (innerCollapseInfrastructure_of_coefficientInfrastructure h)

/-- Coefficient infrastructure supplies the TS113 finite-Fubini target. -/
theorem fubiniInfrastructureTarget_of_coefficientInfrastructureTarget
    (H : SelbergMobiusCoefficientInfrastructureTarget) :
    TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructureTarget :=
  TS114.Goldbach.fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget H)

/-- Coefficient infrastructure supplies the TS112 collapse target. -/
theorem mobiusCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
    (H : SelbergMobiusCoefficientInfrastructureTarget) :
    TS112.Goldbach.SelbergMobiusCollapseInfrastructureTarget :=
  TS114.Goldbach.mobiusCollapseInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget H)

/-- Coefficient infrastructure supplies the TS103 Mobius-inversion target. -/
theorem mobiusInversionInfrastructureTarget_of_coefficientInfrastructureTarget
    (H : SelbergMobiusCoefficientInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS114.Goldbach.mobiusInversionInfrastructureTarget_of_innerCollapseInfrastructureTarget
    (innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget H)

/--
Coefficient infrastructure plus TS95 and TS83 supply the TS98 final root input
package.
-/
theorem finalHorizonInputsTarget_of_coefficient_trace_mellin
    (Hs : SelbergMobiusCoefficientInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS114.Goldbach.finalHorizonInputsTarget_of_innerCollapse_trace_mellin
    (innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget Hs)
    Ht
    Hm

/--
Coefficient infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_coefficient_trace_mellin
    (Hs : SelbergMobiusCoefficientInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS114.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_innerCollapse_trace_mellin
    (innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget Hs)
    Ht
    Hm

/--
Coefficient infrastructure plus TS95 and TS83 feed the full TS25 padded-scale
infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_coefficient_trace_mellin
    (Hs : SelbergMobiusCoefficientInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS114.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_innerCollapse_trace_mellin
    (innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget Hs)
    Ht
    Hm

end Goldbach
end TS115
