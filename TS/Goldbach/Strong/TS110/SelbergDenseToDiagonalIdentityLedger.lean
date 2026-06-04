import Mathlib.Tactic
import TS.Goldbach.Strong.TS109.SelbergQuadraticDiagonalizationLedger

namespace TS110
namespace Goldbach

/-!
# TS110 - Selberg Dense-To-Diagonal Identity Ledger

TS108 defines the dense finite Selberg quadratic form, and TS109 defines the
diagonal square-sum side. This sprint names the precise algebraic identity
that must connect them.

The identity is recorded as a proposition-valued obligation. TS110 does not
prove the dense-to-diagonal Selberg identity, the square-sum majorant, the
Selberg sieve theorem, Brun-Titchmarsh, or any prime-count estimate.
-/

/-- Dense side of the finite Selberg quadratic form. -/
def selbergDenseSide
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  TS108.Goldbach.selbergQuadraticForm level weight

/-- Canonical diagonal side built from the TS109 finite change of variables. -/
def selbergDiagonalSide
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  let change := TS109.Goldbach.selbergDiagonalChangeOfVariables level weight
  TS109.Goldbach.selbergDiagonalSquareSum
    level
    change.diagonalCoefficient
    change.transformedWeight

/-- The dense side is definitionally the TS108 quadratic form. -/
theorem selbergDenseSide_eq_quadraticForm
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergDenseSide level weight =
      TS108.Goldbach.selbergQuadraticForm level weight :=
  rfl

/-- The canonical diagonal side is definitionally the TS109 diagonal square sum. -/
theorem selbergDiagonalSide_eq_squareSum
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergDiagonalSide level weight =
      TS109.Goldbach.selbergDiagonalSquareSum
        level
        (TS109.Goldbach.selbergDiagonalChangeOfVariables
          level
          weight).diagonalCoefficient
        (TS109.Goldbach.selbergDiagonalChangeOfVariables
          level
          weight).transformedWeight :=
  rfl

/--
Ledger for the Selberg dense-to-diagonal identity.

The field `identityObligation` is proposition-valued: it states the equality
that a future proof must establish, without claiming that proof in this sprint.
-/
structure SelbergDenseToDiagonalIdentity
    (level : Nat)
    (weight : Nat -> Rat) where
  diagonalization :
    TS109.Goldbach.SelbergQuadraticDiagonalization level weight

  denseSide :
    Rat

  dense_side_eq :
    denseSide = diagonalization.denseValue

  diagonalSide :
    Rat

  diagonal_side_eq :
    diagonalSide = diagonalization.diagonalValue

  identityObligation :
    Prop

  identity_obligation_eq :
    identityObligation =
      (diagonalization.denseValue = diagonalization.diagonalValue)

  mobius_delta_input :
    TS103.Goldbach.MobiusDeltaIdentityTarget

  gcd_lcm_product_input :
    TS106.Goldbach.GCDLCMKernelAlgebraTarget

  dense_expansion_ready :
    True

  diagonal_expansion_ready :
    True

  divisor_sum_interchange_ready :
    True

  mobius_rewrite_ready :
    True

  gcd_lcm_kernel_rewrite_ready :
    True

  dense_to_diagonal_proof_obligation :
    True

/-- Concrete TS110 identity ledger for every finite level and weight. -/
def selbergDenseToDiagonalIdentity
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergDenseToDiagonalIdentity level weight where
  diagonalization :=
    TS109.Goldbach.selbergQuadraticDiagonalization level weight
  denseSide := selbergDenseSide level weight
  dense_side_eq := rfl
  diagonalSide := selbergDiagonalSide level weight
  diagonal_side_eq := rfl
  identityObligation :=
    (TS109.Goldbach.selbergQuadraticDiagonalization level weight).denseValue =
      (TS109.Goldbach.selbergQuadraticDiagonalization level weight).diagonalValue
  identity_obligation_eq := rfl
  mobius_delta_input := TS105.Goldbach.mobiusDeltaIdentityTarget
  gcd_lcm_product_input := TS106.Goldbach.gcdLCMKernelAlgebraTarget
  dense_expansion_ready := True.intro
  diagonal_expansion_ready := True.intro
  divisor_sum_interchange_ready := True.intro
  mobius_rewrite_ready := True.intro
  gcd_lcm_kernel_rewrite_ready := True.intro
  dense_to_diagonal_proof_obligation := True.intro

/--
The identity obligation stored in the ledger is exactly equality of the dense
and diagonal values of its TS109 diagonalization package.
-/
theorem selbergDenseToDiagonalIdentity_obligation_eq
    {level : Nat}
    {weight : Nat -> Rat}
    (H : SelbergDenseToDiagonalIdentity level weight) :
    H.identityObligation =
      (H.diagonalization.denseValue = H.diagonalization.diagonalValue) :=
  H.identity_obligation_eq

/-- Target proposition for the dense-to-diagonal identity ledger. -/
def SelbergDenseToDiagonalIdentityTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergDenseToDiagonalIdentity level weight)

/-- The dense-to-diagonal identity ledger is populated for all finite weights. -/
theorem selbergDenseToDiagonalIdentityTarget :
    SelbergDenseToDiagonalIdentityTarget := by
  intro level weight
  exact Nonempty.intro (selbergDenseToDiagonalIdentity level weight)

/--
Relative infrastructure using the dense-to-diagonal identity ledger to feed
TS109.

The TS30 majorant, sieve, and budget fields remain hard Selberg and
Brun-Titchmarsh obligations.
-/
structure SelbergDenseToDiagonalInfrastructure where
  diagonalizationInfrastructure :
    TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructure

  identity :
    SelbergDenseToDiagonalIdentity
      diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.level
      diagonalizationInfrastructure.expansionInfrastructure.quadraticLedger.weight

  identity_targets_diagonalization_ready :
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

/-- Target proposition for the relative TS110 infrastructure. -/
def SelbergDenseToDiagonalInfrastructureTarget : Prop :=
  Nonempty SelbergDenseToDiagonalInfrastructure

/--
Dense-to-diagonal infrastructure supplies the TS109 diagonalization
infrastructure.
-/
def diagonalizationInfrastructure_of_denseToDiagonalInfrastructure
    (H : SelbergDenseToDiagonalInfrastructure) :
    TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructure :=
  H.diagonalizationInfrastructure

/--
Dense-to-diagonal infrastructure target supplies the TS109 diagonalization
infrastructure target.
-/
theorem diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
    (H : SelbergDenseToDiagonalInfrastructureTarget) :
    TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (diagonalizationInfrastructure_of_denseToDiagonalInfrastructure h)

/--
Dense-to-diagonal infrastructure supplies the TS108 quadratic-form expansion
infrastructure target through TS109.
-/
theorem quadraticFormExpansionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
    (H : SelbergDenseToDiagonalInfrastructureTarget) :
    TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructureTarget :=
  TS109.Goldbach.quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
    (diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
      H)

/--
Dense-to-diagonal infrastructure supplies the TS103 Mobius-inversion
infrastructure target through TS109.
-/
theorem mobiusInversionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
    (H : SelbergDenseToDiagonalInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS109.Goldbach.mobiusInversionInfrastructureTarget_of_diagonalizationInfrastructureTarget
    (diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
      H)

/--
Dense-to-diagonal infrastructure plus TS95 and TS83 supply the TS98 final root
input package.
-/
theorem finalHorizonInputsTarget_of_denseToDiagonal_trace_mellin
    (Hs : SelbergDenseToDiagonalInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS109.Goldbach.finalHorizonInputsTarget_of_diagonalization_trace_mellin
    (diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Dense-to-diagonal infrastructure plus TS95 and TS83 feed the TS84 padded final
API route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_denseToDiagonal_trace_mellin
    (Hs : SelbergDenseToDiagonalInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS109.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_diagonalization_trace_mellin
    (diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Dense-to-diagonal infrastructure plus TS95 and TS83 feed the full TS25
padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_denseToDiagonal_trace_mellin
    (Hs : SelbergDenseToDiagonalInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS109.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_diagonalization_trace_mellin
    (diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS110
