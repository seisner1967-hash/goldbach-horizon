import Mathlib.Tactic
import TS.Goldbach.Strong.TS108.SelbergQuadraticFormExpansionLedger

namespace TS109
namespace Goldbach

/-!
# TS109 - Selberg Quadratic Diagonalization Ledger

TS108 defines the finite dense Selberg quadratic form

`sum_a sum_b w a * w b * K(a,b)`.

This sprint opens the next layer: the diagonalization interface. It defines a
finite diagonal change of variables and the corresponding diagonal square sum.
The actual Selberg diagonal identity, the square-sum majorant, the Selberg
sieve theorem, Brun-Titchmarsh, and prime-count estimates remain explicitly
packaged as relative obligations.
-/

/-- Finite support used by the diagonal side of the Selberg form. -/
def selbergDiagonalSupport
    (level : Nat) :
    Finset Nat :=
  TS108.Goldbach.selbergQuadraticSupport level

/--
Canonical finite transformed weight used to prepare diagonalization.

This is only the finite divisor-filtered change-of-variables slot. TS109 does
not prove that this choice diagonalizes the TS108 dense quadratic form.
-/
def selbergDiagonalTransformedWeight
    (level : Nat)
    (weight : Nat -> Rat)
    (d : Nat) :
    Rat :=
  Finset.sum (selbergDiagonalSupport level) fun m =>
    if Dvd.dvd d m then weight m else 0

/-- Default coefficient slot for the diagonal square sum. -/
def selbergUnitDiagonalCoefficient
    (_d : Nat) :
    Rat :=
  1

/-- One term of a diagonal Selberg square sum. -/
def selbergDiagonalSquareTerm
    (diagonalCoefficient : Nat -> Rat)
    (transformedWeight : Nat -> Rat)
    (d : Nat) :
    Rat :=
  diagonalCoefficient d * transformedWeight d ^ (2 : Nat)

/-- The diagonal Selberg square sum over the finite diagonal support. -/
def selbergDiagonalSquareSum
    (level : Nat)
    (diagonalCoefficient transformedWeight : Nat -> Rat) :
    Rat :=
  Finset.sum (selbergDiagonalSupport level) fun d =>
    selbergDiagonalSquareTerm diagonalCoefficient transformedWeight d

/-- The transformed weight is its defining divisor-filtered finite sum. -/
theorem selbergDiagonalTransformedWeight_expansion
    (level : Nat)
    (weight : Nat -> Rat)
    (d : Nat) :
    selbergDiagonalTransformedWeight level weight d =
      Finset.sum (selbergDiagonalSupport level) (fun m =>
        if Dvd.dvd d m then weight m else 0) :=
  rfl

/-- The diagonal square sum is its defining finite sum. -/
theorem selbergDiagonalSquareSum_expansion
    (level : Nat)
    (diagonalCoefficient transformedWeight : Nat -> Rat) :
    selbergDiagonalSquareSum level diagonalCoefficient transformedWeight =
      Finset.sum (selbergDiagonalSupport level) (fun d =>
        selbergDiagonalSquareTerm diagonalCoefficient transformedWeight d) :=
  rfl

/--
Finite change of variables expected before Selberg diagonalization.

The fields are deliberately structural: the actual proof that this change of
variables converts the TS108 dense double sum into a diagonal square sum is the
next hard arithmetic obligation.
-/
structure SelbergDiagonalChangeOfVariables
    (level : Nat)
    (weight : Nat -> Rat) where
  transformedWeight :
    Nat -> Rat

  transformed_weight_eq :
    forall d : Nat,
      transformedWeight d =
        selbergDiagonalTransformedWeight level weight d

  diagonalCoefficient :
    Nat -> Rat

  support :
    Finset Nat

  support_eq_diagonalSupport :
    support = selbergDiagonalSupport level

  support_control_ready :
    True

  divisor_convolution_rewrite_ready :
    True

  triangular_change_ready :
    True

/-- Canonical finite diagonal change-of-variables package. -/
def selbergDiagonalChangeOfVariables
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergDiagonalChangeOfVariables level weight where
  transformedWeight := selbergDiagonalTransformedWeight level weight
  transformed_weight_eq := by
    intro d
    rfl
  diagonalCoefficient := selbergUnitDiagonalCoefficient
  support := selbergDiagonalSupport level
  support_eq_diagonalSupport := rfl
  support_control_ready := True.intro
  divisor_convolution_rewrite_ready := True.intro
  triangular_change_ready := True.intro

/--
Diagonalization ledger for the TS108 finite quadratic form.

This packages the dense TS108 expansion, a finite diagonal change of variables,
and the diagonal square sum. The identity between the dense and diagonal sides
is intentionally recorded as a readiness marker, not proved here.
-/
structure SelbergQuadraticDiagonalization
    (level : Nat)
    (weight : Nat -> Rat) where
  expansion :
    TS108.Goldbach.SelbergQuadraticFormExpansion level weight

  changeOfVariables :
    SelbergDiagonalChangeOfVariables level weight

  diagonalSupport :
    Finset Nat

  diagonal_support_eq :
    diagonalSupport = selbergDiagonalSupport level

  denseValue :
    Rat

  dense_value_eq :
    denseValue = TS108.Goldbach.selbergQuadraticForm level weight

  diagonalValue :
    Rat

  diagonal_value_eq :
    diagonalValue =
      selbergDiagonalSquareSum
        level
        changeOfVariables.diagonalCoefficient
        changeOfVariables.transformedWeight

  diagonal_square_sum_expansion :
    diagonalValue =
      Finset.sum (selbergDiagonalSupport level) (fun d =>
        selbergDiagonalSquareTerm
          changeOfVariables.diagonalCoefficient
          changeOfVariables.transformedWeight
          d)

  dense_to_diagonal_identity_ready :
    True

  mobius_rewrite_ready :
    True

  square_sum_majorant_ready :
    True

  selberg_optimization_input_ready :
    True

/-- Concrete TS109 diagonalization ledger for each finite level and weight. -/
def selbergQuadraticDiagonalization
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergQuadraticDiagonalization level weight where
  expansion := TS108.Goldbach.selbergQuadraticFormExpansion level weight
  changeOfVariables := selbergDiagonalChangeOfVariables level weight
  diagonalSupport := selbergDiagonalSupport level
  diagonal_support_eq := rfl
  denseValue := TS108.Goldbach.selbergQuadraticForm level weight
  dense_value_eq := rfl
  diagonalValue :=
    selbergDiagonalSquareSum
      level
      (selbergDiagonalChangeOfVariables level weight).diagonalCoefficient
      (selbergDiagonalChangeOfVariables level weight).transformedWeight
  diagonal_value_eq := rfl
  diagonal_square_sum_expansion :=
    selbergDiagonalSquareSum_expansion
      level
      (selbergDiagonalChangeOfVariables level weight).diagonalCoefficient
      (selbergDiagonalChangeOfVariables level weight).transformedWeight
  dense_to_diagonal_identity_ready := True.intro
  mobius_rewrite_ready := True.intro
  square_sum_majorant_ready := True.intro
  selberg_optimization_input_ready := True.intro

/-- Target proposition for the finite diagonalization ledger. -/
def SelbergQuadraticDiagonalizationTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergQuadraticDiagonalization level weight)

/-- The diagonalization ledger is populated for every finite level and weight. -/
theorem selbergQuadraticDiagonalizationTarget :
    SelbergQuadraticDiagonalizationTarget := by
  intro level weight
  exact Nonempty.intro (selbergQuadraticDiagonalization level weight)

/--
Relative infrastructure using a diagonalization package to feed TS108.

The TS30 majorant, sieve, and budget fields remain the hard Selberg and
Brun-Titchmarsh obligations.
-/
structure SelbergQuadraticDiagonalizationInfrastructure where
  expansionInfrastructure :
    TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructure

  diagonalization :
    SelbergQuadraticDiagonalization
      expansionInfrastructure.quadraticLedger.level
      expansionInfrastructure.quadraticLedger.weight

  dense_value_agrees_with_expansion :
    diagonalization.denseValue =
      TS108.Goldbach.selbergQuadraticForm
        expansionInfrastructure.quadraticLedger.level
        expansionInfrastructure.quadraticLedger.weight

  diagonal_identity_from_expansion_ready :
    True

  square_sum_majorant_from_diagonal_ready :
    True

  majorant_from_diagonal_ready :
    True

  sieve_from_diagonal_ready :
    True

  budget_from_diagonal_ready :
    True

/-- Target proposition for the relative TS109 infrastructure. -/
def SelbergQuadraticDiagonalizationInfrastructureTarget : Prop :=
  Nonempty SelbergQuadraticDiagonalizationInfrastructure

/--
Diagonalization infrastructure supplies the TS108 quadratic-form expansion
infrastructure.
-/
def quadraticFormExpansionInfrastructure_of_diagonalizationInfrastructure
    (H : SelbergQuadraticDiagonalizationInfrastructure) :
    TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructure :=
  H.expansionInfrastructure

/--
Diagonalization infrastructure target supplies the TS108 quadratic-form
expansion infrastructure target.
-/
theorem quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
    (H : SelbergQuadraticDiagonalizationInfrastructureTarget) :
    TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (quadraticFormExpansionInfrastructure_of_diagonalizationInfrastructure
            h)

/--
Diagonalization infrastructure supplies the TS107 kernel-extraction
infrastructure target through TS108.
-/
theorem selbergKernelExtractionInfrastructureTarget_of_diagonalizationInfrastructureTarget
    (H : SelbergQuadraticDiagonalizationInfrastructureTarget) :
    TS107.Goldbach.SelbergKernelExtractionInfrastructureTarget :=
  TS108.Goldbach.selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
    (quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
      H)

/--
Diagonalization infrastructure supplies the TS103 Mobius-inversion
infrastructure target through TS108.
-/
theorem mobiusInversionInfrastructureTarget_of_diagonalizationInfrastructureTarget
    (H : SelbergQuadraticDiagonalizationInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS108.Goldbach.mobiusInversionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
    (quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
      H)

/--
Diagonalization infrastructure plus TS95 and TS83 supply the TS98 final root
input package.
-/
theorem finalHorizonInputsTarget_of_diagonalization_trace_mellin
    (Hs : SelbergQuadraticDiagonalizationInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS108.Goldbach.finalHorizonInputsTarget_of_quadraticExpansion_trace_mellin
    (quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Diagonalization infrastructure plus TS95 and TS83 feed the TS84 padded final API
route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_diagonalization_trace_mellin
    (Hs : SelbergQuadraticDiagonalizationInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS108.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_quadraticExpansion_trace_mellin
    (quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Diagonalization infrastructure plus TS95 and TS83 feed the full TS25
padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_diagonalization_trace_mellin
    (Hs : SelbergQuadraticDiagonalizationInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS108.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_quadraticExpansion_trace_mellin
    (quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS109
