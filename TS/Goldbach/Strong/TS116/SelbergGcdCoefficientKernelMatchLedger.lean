import Mathlib.Tactic
import TS.Goldbach.Strong.TS115.SelbergMobiusCoefficientLedger

namespace TS116
namespace Goldbach

/-!
# TS116 - Selberg GCD Coefficient Kernel Match Ledger

TS115 reduces the TS114 local coefficient to a one-variable coefficient
evaluated at `gcd(m,n)`. This sprint opens the next local layer: it exposes the
diagonal coefficient slot used by that one-variable sum, records the exact
`gcd`-indexed kernel value needed for the dense side, and proves that this
local compatibility supplies the TS115 coefficient-kernel match.

The current TS109 diagonal coefficient is still the unit placeholder. TS116
therefore does not claim the actual Mobius coefficient calculation. It isolates
the exact compatibility obligation needed before the dense-to-diagonal Selberg
identity can be closed.
-/

/-- The diagonal coefficient slot used by the TS115 one-variable sum. -/
def selbergDiagonalCoefficientFormula
    (level : Nat)
    (weight : Nat -> Rat)
    (d : Nat) :
    Rat :=
  (TS109.Goldbach.selbergDiagonalChangeOfVariables
    level
    weight).diagonalCoefficient d

/-- In the current TS109 normalization, the diagonal coefficient slot is unit. -/
theorem selbergDiagonalCoefficientFormula_eq_unit
    (level : Nat)
    (weight : Nat -> Rat)
    (d : Nat) :
    selbergDiagonalCoefficientFormula level weight d =
      TS109.Goldbach.selbergUnitDiagonalCoefficient d :=
  rfl

/--
The TS115 gcd coefficient is the filtered sum of the explicit diagonal
coefficient formula.
-/
theorem selbergGcdCoefficient_eq_formula_filter_sum
    (level : Nat)
    (weight : Nat -> Rat)
    (g : Nat) :
    TS115.Goldbach.selbergGcdCoefficient level weight g =
      Finset.sum (TS115.Goldbach.selbergGcdCoefficientSupport level g) fun d =>
        selbergDiagonalCoefficientFormula level weight d := by
  rw [TS115.Goldbach.selbergGcdCoefficient_eq_filter_sum]
  rfl

/--
Candidate dense-kernel value as seen from a gcd index.

This intentionally remains pair-indexed: the canonical dense kernel is
`gcd(m,n)/lcm(m,n)`, so matching it with a one-variable coefficient requires a
local compatibility obligation for every pair.
-/
def selbergCanonicalKernelFromGcd
    (m n : Nat) :
    Rat :=
  TS107.Goldbach.canonicalSelbergQuadraticKernel m n

/--
The explicit local compatibility obligation for the one-variable gcd
coefficient and the canonical dense kernel.
-/
def SelbergGcdCoefficientKernelCompatibility
    (level : Nat)
    (weight : Nat -> Rat) :
    Prop :=
  forall m n : Nat,
    TS115.Goldbach.selbergGcdCoefficient level weight (Nat.gcd m n) =
      selbergCanonicalKernelFromGcd m n

/-- The TS116 compatibility is definitionally the TS115 kernel-match obligation. -/
theorem gcdCoefficientKernelCompatibility_iff_ts115_match
    (level : Nat)
    (weight : Nat -> Rat) :
    Iff (SelbergGcdCoefficientKernelCompatibility level weight)
      (TS115.Goldbach.SelbergGcdCoefficientKernelMatchObligation
        level
        weight) := by
  unfold SelbergGcdCoefficientKernelCompatibility
  unfold TS115.Goldbach.SelbergGcdCoefficientKernelMatchObligation
  unfold selbergCanonicalKernelFromGcd
  exact Iff.rfl

/-- The TS116 compatibility supplies the TS115 kernel-match obligation. -/
theorem gcdCoefficientKernelMatchObligation_of_compatibility
    (level : Nat)
    (weight : Nat -> Rat)
    (Hcompat : SelbergGcdCoefficientKernelCompatibility level weight) :
    TS115.Goldbach.SelbergGcdCoefficientKernelMatchObligation
      level
      weight :=
  (gcdCoefficientKernelCompatibility_iff_ts115_match level weight).mp Hcompat

/-- The TS116 compatibility supplies the TS114 local kernel-match obligation. -/
theorem innerGcdKernelMatchObligation_of_compatibility
    (level : Nat)
    (weight : Nat -> Rat)
    (Hcompat : SelbergGcdCoefficientKernelCompatibility level weight) :
    TS114.Goldbach.SelbergInnerGcdKernelMatchObligation level weight :=
  TS115.Goldbach.innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
    level
    weight
    (gcdCoefficientKernelMatchObligation_of_compatibility
      level
      weight
      Hcompat)

/--
The TS116 compatibility closes the TS112 gcd-filtered side conditionally
through TS115 and TS114.
-/
theorem selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_compatibility
    (level : Nat)
    (weight : Nat -> Rat)
    (Hcompat : SelbergGcdCoefficientKernelCompatibility level weight) :
    TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
      TS110.Goldbach.selbergDenseSide level weight :=
  TS115.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch
    level
    weight
    (gcdCoefficientKernelMatchObligation_of_compatibility
      level
      weight
      Hcompat)

/--
Ledger for the TS116 gcd-coefficient kernel-match layer.

The coefficient formula and filtered-sum rewrite are concrete. The
`compatibilityObligation` is the remaining arithmetic calculation: the
gcd-indexed coefficient must equal the canonical dense `gcd/lcm` kernel for
every pair.
-/
structure SelbergGcdCoefficientKernelMatch
    (level : Nat)
    (weight : Nat -> Rat) where
  coefficient :
    TS115.Goldbach.SelbergMobiusCoefficient level weight

  diagonalCoefficient :
    Nat -> Rat

  diagonal_coefficient_eq :
    forall d : Nat,
      diagonalCoefficient d =
        selbergDiagonalCoefficientFormula level weight d

  gcd_coefficient_formula_expansion :
    forall g : Nat,
      TS115.Goldbach.selbergGcdCoefficient level weight g =
        Finset.sum (TS115.Goldbach.selbergGcdCoefficientSupport level g) fun d =>
          diagonalCoefficient d

  canonicalKernelFromGcd :
    Nat -> Nat -> Rat

  canonical_kernel_from_gcd_eq :
    forall m n : Nat,
      canonicalKernelFromGcd m n =
        TS107.Goldbach.canonicalSelbergQuadraticKernel m n

  compatibilityObligation :
    Prop

  compatibility_obligation_eq :
    compatibilityObligation =
      (forall m n : Nat,
        TS115.Goldbach.selbergGcdCoefficient level weight (Nat.gcd m n) =
          canonicalKernelFromGcd m n)

  ts115_match_of_compatibility :
    (forall m n : Nat,
      TS115.Goldbach.selbergGcdCoefficient level weight (Nat.gcd m n) =
        canonicalKernelFromGcd m n) ->
      TS115.Goldbach.SelbergGcdCoefficientKernelMatchObligation
        level
        weight

  canonical_collapse_dense_if_compatibility :
    (forall m n : Nat,
      TS115.Goldbach.selbergGcdCoefficient level weight (Nat.gcd m n) =
        canonicalKernelFromGcd m n) ->
      TS112.Goldbach.selbergCanonicalGcdCollapseExpansion level weight =
        TS110.Goldbach.selbergDenseSide level weight

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  diagonal_coefficient_formula_ready :
    True

  coefficient_filter_sum_ready :
    True

  gcd_only_compatibility_obligation :
    True

  dense_kernel_match_obligation :
    True

  dense_to_diagonal_identity_obligation :
    True

/-- Concrete TS116 kernel-match ledger for every finite level and weight. -/
def selbergGcdCoefficientKernelMatch
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergGcdCoefficientKernelMatch level weight where
  coefficient := TS115.Goldbach.selbergMobiusCoefficient level weight
  diagonalCoefficient := selbergDiagonalCoefficientFormula level weight
  diagonal_coefficient_eq := by
    intro d
    rfl
  gcd_coefficient_formula_expansion := by
    intro g
    exact selbergGcdCoefficient_eq_formula_filter_sum level weight g
  canonicalKernelFromGcd := selbergCanonicalKernelFromGcd
  canonical_kernel_from_gcd_eq := by
    intro m n
    rfl
  compatibilityObligation :=
    SelbergGcdCoefficientKernelCompatibility level weight
  compatibility_obligation_eq := rfl
  ts115_match_of_compatibility := by
    intro Hcompat
    exact
      gcdCoefficientKernelMatchObligation_of_compatibility
        level
        weight
        Hcompat
  canonical_collapse_dense_if_compatibility := by
    intro Hcompat
    exact
      selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_compatibility
        level
        weight
        Hcompat
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  diagonal_coefficient_formula_ready := True.intro
  coefficient_filter_sum_ready := True.intro
  gcd_only_compatibility_obligation := True.intro
  dense_kernel_match_obligation := True.intro
  dense_to_diagonal_identity_obligation := True.intro

/-- Target proposition for the TS116 gcd-coefficient kernel-match ledger. -/
def SelbergGcdCoefficientKernelMatchTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergGcdCoefficientKernelMatch level weight)

/-- The TS116 gcd-coefficient kernel-match ledger is populated for all weights. -/
theorem selbergGcdCoefficientKernelMatchTarget :
    SelbergGcdCoefficientKernelMatchTarget := by
  intro level weight
  exact Nonempty.intro (selbergGcdCoefficientKernelMatch level weight)

/--
Relative infrastructure using the kernel-match layer to feed TS115.

The actual compatibility proof, square-sum majorant, sieve, and budget fields
remain hard Selberg and Brun-Titchmarsh obligations.
-/
structure SelbergGcdCoefficientKernelMatchInfrastructure where
  coefficientInfrastructure :
    TS115.Goldbach.SelbergMobiusCoefficientInfrastructure

  kernelMatch :
    SelbergGcdCoefficientKernelMatch
      (coefficientInfrastructure.innerCollapseInfrastructure.fubiniInfrastructure.collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level)
      (coefficientInfrastructure.innerCollapseInfrastructure.fubiniInfrastructure.collapseInfrastructure.reindexingInfrastructure.denseToDiagonalInfrastructure.diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight)

  kernel_match_targets_coefficient_ready :
    True

  coefficient_formula_ready :
    True

  local_kernel_compatibility_ready :
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

/-- Target proposition for the relative TS116 infrastructure. -/
def SelbergGcdCoefficientKernelMatchInfrastructureTarget : Prop :=
  Nonempty SelbergGcdCoefficientKernelMatchInfrastructure

/-- Kernel-match infrastructure supplies the TS115 coefficient layer. -/
def coefficientInfrastructure_of_kernelMatchInfrastructure
    (H : SelbergGcdCoefficientKernelMatchInfrastructure) :
    TS115.Goldbach.SelbergMobiusCoefficientInfrastructure :=
  H.coefficientInfrastructure

/-- Kernel-match infrastructure target supplies the TS115 target. -/
theorem coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget
    (H : SelbergGcdCoefficientKernelMatchInfrastructureTarget) :
    TS115.Goldbach.SelbergMobiusCoefficientInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (coefficientInfrastructure_of_kernelMatchInfrastructure h)

/-- Kernel-match infrastructure supplies the TS114 inner-collapse target. -/
theorem innerCollapseInfrastructureTarget_of_kernelMatchInfrastructureTarget
    (H : SelbergGcdCoefficientKernelMatchInfrastructureTarget) :
    TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructureTarget :=
  TS115.Goldbach.innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget H)

/-- Kernel-match infrastructure supplies the TS113 finite-Fubini target. -/
theorem fubiniInfrastructureTarget_of_kernelMatchInfrastructureTarget
    (H : SelbergGcdCoefficientKernelMatchInfrastructureTarget) :
    TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructureTarget :=
  TS115.Goldbach.fubiniInfrastructureTarget_of_coefficientInfrastructureTarget
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget H)

/-- Kernel-match infrastructure supplies the TS112 collapse target. -/
theorem mobiusCollapseInfrastructureTarget_of_kernelMatchInfrastructureTarget
    (H : SelbergGcdCoefficientKernelMatchInfrastructureTarget) :
    TS112.Goldbach.SelbergMobiusCollapseInfrastructureTarget :=
  TS115.Goldbach.mobiusCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget H)

/-- Kernel-match infrastructure supplies the TS103 Mobius-inversion target. -/
theorem mobiusInversionInfrastructureTarget_of_kernelMatchInfrastructureTarget
    (H : SelbergGcdCoefficientKernelMatchInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS115.Goldbach.mobiusInversionInfrastructureTarget_of_coefficientInfrastructureTarget
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget H)

/--
Kernel-match infrastructure plus TS95 and TS83 supply the TS98 final root input
package.
-/
theorem finalHorizonInputsTarget_of_kernelMatch_trace_mellin
    (Hs : SelbergGcdCoefficientKernelMatchInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS115.Goldbach.finalHorizonInputsTarget_of_coefficient_trace_mellin
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget Hs)
    Ht
    Hm

/--
Kernel-match infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_kernelMatch_trace_mellin
    (Hs : SelbergGcdCoefficientKernelMatchInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS115.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_coefficient_trace_mellin
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget Hs)
    Ht
    Hm

/--
Kernel-match infrastructure plus TS95 and TS83 feed the full TS25 padded-scale
infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_kernelMatch_trace_mellin
    (Hs : SelbergGcdCoefficientKernelMatchInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS115.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_coefficient_trace_mellin
    (coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget Hs)
    Ht
    Hm

end Goldbach
end TS116
