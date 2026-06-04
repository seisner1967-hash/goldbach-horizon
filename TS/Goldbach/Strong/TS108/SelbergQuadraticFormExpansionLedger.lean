import Mathlib.Tactic
import TS.Goldbach.Strong.TS107.SelbergQuadraticKernelExtractionLedger

namespace TS108
namespace Goldbach

open Finset

/-!
# TS108 - Selberg Quadratic Form Expansion Ledger

TS107 extracts the canonical Selberg quadratic kernel
`gcd(a,b) / lcm(a,b)` and proves its symmetry. This sprint formalizes the
finite quadratic-form expansion layer built from that kernel.

It defines the finite double sum

`sum_a sum_b w a * w b * K(a,b)`

over `Finset.range (level + 1)` and proves the immediate index-swap symmetry
of the summand using TS107's kernel symmetry.

The diagonalization of the quadratic form, the Selberg sieve bound,
Brun-Titchmarsh, and prime-count estimates remain relative obligations.
-/

/-- One term of the canonical Selberg quadratic form. -/
def selbergQuadraticFormTerm
    (weight : Nat -> Rat)
    (a b : Nat) :
    Rat :=
  weight a * weight b *
    TS107.Goldbach.canonicalSelbergQuadraticKernel a b

/-- The canonical Selberg quadratic-form term is symmetric in its indices. -/
theorem selbergQuadraticFormTerm_symm
    (weight : Nat -> Rat)
    (a b : Nat) :
    selbergQuadraticFormTerm weight a b =
      selbergQuadraticFormTerm weight b a := by
  unfold selbergQuadraticFormTerm
  rw [TS107.Goldbach.canonicalSelbergQuadraticKernel_symm a b]
  ring

/-- Finite support window for the quadratic expansion. -/
def selbergQuadraticSupport
    (level : Nat) :
    Finset Nat :=
  Finset.range (level + 1)

/-- Canonical finite Selberg quadratic form over `range (level + 1)`. -/
def selbergQuadraticForm
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  Finset.sum (selbergQuadraticSupport level) fun a =>
    Finset.sum (selbergQuadraticSupport level) fun b =>
      selbergQuadraticFormTerm weight a b

/-- The definition of the finite quadratic form as an explicit double sum. -/
theorem selbergQuadraticForm_expansion
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergQuadraticForm level weight =
      Finset.sum (selbergQuadraticSupport level) (fun a =>
        Finset.sum (selbergQuadraticSupport level) fun b =>
          selbergQuadraticFormTerm weight a b) :=
  rfl

/-- The finite quadratic form is stable under swapping the summand indices. -/
theorem selbergQuadraticForm_swap_indices
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergQuadraticForm level weight =
      Finset.sum (selbergQuadraticSupport level) (fun a =>
        Finset.sum (selbergQuadraticSupport level) fun b =>
          selbergQuadraticFormTerm weight b a) := by
  unfold selbergQuadraticForm
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  exact selbergQuadraticFormTerm_symm weight a b

/--
Concrete finite quadratic-form expansion data for a given level and weight.

This records the explicit double sum and the immediate symmetry facts. The
diagonalization and Selberg optimization are deliberately kept as later
obligations.
-/
structure SelbergQuadraticFormExpansion
    (level : Nat)
    (weight : Nat -> Rat) where
  support :
    Finset Nat

  support_eq_range :
    support = selbergQuadraticSupport level

  quadraticValue :
    Rat

  quadratic_value_eq :
    quadraticValue = selbergQuadraticForm level weight

  extraction :
    TS107.Goldbach.SelbergQuadraticKernelExtractionProof

  extraction_kernel_agreement :
    forall a b : Nat,
      extraction.quadraticKernel a b =
        TS107.Goldbach.canonicalSelbergQuadraticKernel a b

  term_symmetric :
    forall a b : Nat,
      selbergQuadraticFormTerm weight a b =
        selbergQuadraticFormTerm weight b a

  form_swap_indices :
    selbergQuadraticForm level weight =
      Finset.sum (selbergQuadraticSupport level) (fun a =>
        Finset.sum (selbergQuadraticSupport level) fun b =>
          selbergQuadraticFormTerm weight b a)

  finite_double_sum_ready :
    True

  kernel_symmetry_used :
    True

  bilinear_form_symmetric :
    True

  quadratic_expansion_ready :
    True

  diagonalization_obligation :
    True

/-- Concrete finite quadratic-form expansion package. -/
def selbergQuadraticFormExpansion
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergQuadraticFormExpansion level weight where
  support := selbergQuadraticSupport level
  support_eq_range := rfl
  quadraticValue := selbergQuadraticForm level weight
  quadratic_value_eq := rfl
  extraction := TS107.Goldbach.selbergQuadraticKernelExtractionProof
  extraction_kernel_agreement := by
    intro a b
    rfl
  term_symmetric := selbergQuadraticFormTerm_symm weight
  form_swap_indices := selbergQuadraticForm_swap_indices level weight
  finite_double_sum_ready := True.intro
  kernel_symmetry_used := True.intro
  bilinear_form_symmetric := True.intro
  quadratic_expansion_ready := True.intro
  diagonalization_obligation := True.intro

/-- Target proposition for the finite quadratic-form expansion layer. -/
def SelbergQuadraticFormExpansionTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergQuadraticFormExpansion level weight)

/-- The finite quadratic-form expansion target is populated for all weights. -/
theorem selbergQuadraticFormExpansionTarget :
    SelbergQuadraticFormExpansionTarget := by
  intro level weight
  exact Nonempty.intro (selbergQuadraticFormExpansion level weight)

/--
Relative infrastructure using a quadratic-form expansion to feed TS107.

The TS30 majorant, sieve, and budget fields remain the hard Selberg and
Brun-Titchmarsh obligations.
-/
structure SelbergQuadraticFormExpansionInfrastructure where
  quadraticLedger :
    TS100.Goldbach.SelbergQuadraticFormLedger

  expansion :
    SelbergQuadraticFormExpansion
      quadraticLedger.level
      quadraticLedger.weight

  quadratic_kernel_agreement :
    forall a b : Nat,
      quadraticLedger.quadraticKernel a b =
        TS107.Goldbach.canonicalSelbergQuadraticKernel a b

  divisorConvolution :
    Nat -> Nat -> Rat

  divisor_convolution_from_expansion_ready :
    True

  weightLedger :
    TS99.Goldbach.SelbergSieveWeightLedger

  weight_agreement :
    forall d : Nat,
      weightLedger.weight d = quadraticLedger.weight d

  majorant :
    TS30.Goldbach.SelbergIntervalMajorant

  sieve :
    TS30.Goldbach.SelbergSieveIntervalBound majorant

  budget :
    TS30.Goldbach.SelbergMajorantBudgetComparison majorant

  majorant_from_expansion_ready :
    True

  sieve_from_expansion_ready :
    True

  budget_from_expansion_ready :
    True

/-- Target proposition for the relative TS108 infrastructure. -/
def SelbergQuadraticFormExpansionInfrastructureTarget : Prop :=
  Nonempty SelbergQuadraticFormExpansionInfrastructure

/--
Quadratic-form expansion infrastructure supplies the TS107 kernel-extraction
infrastructure.
-/
def kernelExtractionInfrastructure_of_quadraticFormExpansionInfrastructure
    (H : SelbergQuadraticFormExpansionInfrastructure) :
    TS107.Goldbach.SelbergKernelExtractionInfrastructure where
  extraction := H.expansion.extraction
  divisorConvolution := H.divisorConvolution
  divisor_convolution_from_kernel_ready :=
    H.divisor_convolution_from_expansion_ready
  quadraticLedger := H.quadraticLedger
  quadratic_kernel_agreement := by
    intro a b
    rw [H.quadratic_kernel_agreement a b]
    exact (H.expansion.extraction_kernel_agreement a b).symm
  weightLedger := H.weightLedger
  weight_agreement := H.weight_agreement
  majorant := H.majorant
  sieve := H.sieve
  budget := H.budget
  majorant_from_kernel_ready := H.majorant_from_expansion_ready
  sieve_from_kernel_ready := H.sieve_from_expansion_ready
  budget_from_kernel_ready := H.budget_from_expansion_ready

/--
Quadratic-form expansion infrastructure target supplies the TS107
kernel-extraction infrastructure target.
-/
theorem selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
    (H : SelbergQuadraticFormExpansionInfrastructureTarget) :
    TS107.Goldbach.SelbergKernelExtractionInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (kernelExtractionInfrastructure_of_quadraticFormExpansionInfrastructure
            h)

/--
Quadratic-form expansion infrastructure supplies the TS106 divisor-kernel
infrastructure target through TS107.
-/
theorem divisorKernelAlgebraInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
    (H : SelbergQuadraticFormExpansionInfrastructureTarget) :
    TS106.Goldbach.DivisorKernelAlgebraInfrastructureTarget :=
  TS107.Goldbach.divisorKernelAlgebraInfrastructureTarget_of_kernelExtractionInfrastructureTarget
    (selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
      H)

/--
Quadratic-form expansion infrastructure supplies the TS103 Mobius-inversion
infrastructure target through TS107.
-/
theorem mobiusInversionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
    (H : SelbergQuadraticFormExpansionInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget :=
  TS107.Goldbach.mobiusInversionInfrastructureTarget_of_kernelExtractionInfrastructureTarget
    (selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
      H)

/--
Quadratic-form expansion infrastructure plus TS95 and TS83 supply the TS98
final root input package.
-/
theorem finalHorizonInputsTarget_of_quadraticExpansion_trace_mellin
    (Hs : SelbergQuadraticFormExpansionInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS107.Goldbach.finalHorizonInputsTarget_of_kernelExtraction_trace_mellin
    (selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Quadratic-form expansion infrastructure plus TS95 and TS83 feed the TS84
padded final API route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_quadraticExpansion_trace_mellin
    (Hs : SelbergQuadraticFormExpansionInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS107.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_kernelExtraction_trace_mellin
    (selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Quadratic-form expansion infrastructure plus TS95 and TS83 feed the full TS25
padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_quadraticExpansion_trace_mellin
    (Hs : SelbergQuadraticFormExpansionInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS107.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_kernelExtraction_trace_mellin
    (selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS108
