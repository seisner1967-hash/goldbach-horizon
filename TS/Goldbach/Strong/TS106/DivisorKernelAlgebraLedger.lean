import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import TS.Goldbach.Strong.TS105.MobiusDeltaIdentityDischarge

namespace TS106
namespace Goldbach

/-!
# TS106 - Divisor Kernel Algebra Ledger

TS105 discharges the Mobius-delta identity. This sprint opens the next local
arithmetic layer: divisor convolution, gcd/lcm kernels, and the extraction of
the Selberg quadratic kernel.

It proves one elementary concrete identity for the canonical gcd/lcm kernels:
`gcd a b * lcm a b = a * b`, transported to rational-valued kernels.

The full Selberg divisor-kernel infrastructure remains relative: this sprint
does not prove Selberg's sieve, Brun-Titchmarsh, quadratic-form
diagonalization, or any prime-count estimate.
-/

/-- Canonical rational-valued gcd kernel. -/
def canonicalGcdKernel
    (a b : Nat) :
    Rat :=
  (Nat.gcd a b : Rat)

/-- Canonical rational-valued lcm kernel. -/
def canonicalLcmKernel
    (a b : Nat) :
    Rat :=
  (Nat.lcm a b : Rat)

/-- The canonical rational gcd/lcm kernels multiply to the product. -/
theorem canonicalGcdKernel_mul_lcmKernel
    (a b : Nat) :
    canonicalGcdKernel a b * canonicalLcmKernel a b =
      (a * b : Rat) := by
  unfold canonicalGcdKernel canonicalLcmKernel
  have h : Nat.gcd a b * Nat.lcm a b = a * b :=
    Nat.gcd_mul_lcm a b
  exact_mod_cast h

/--
Concrete divisor-convolution bridge.

This records that the concrete TS104 binding and the TS105 Mobius-delta
discharge provide the divisor-sum/convolution side of TS103.
-/
structure DivisorConvolutionBridge where
  delta :
    TS105.Goldbach.MobiusConcreteDeltaDischarge

  divisorAPI :
    TS103.Goldbach.DivisorSumConvolution

  divisor_sum_mobius_eq_delta :
    forall n : Nat,
      delta.binding.divisorSum delta.binding.mobiusFun n =
        delta.binding.delta n

  convolution_from_mathlib_ready :
    True

  convolution_associative_ready :
    True

/-- Concrete divisor-convolution bridge from TS104 and TS105. -/
def divisorConvolutionBridge :
    DivisorConvolutionBridge where
  delta := TS105.Goldbach.mobiusConcreteDeltaDischarge
  divisorAPI :=
    TS104.Goldbach.divisorSumConvolution_of_concreteBinding
      TS105.Goldbach.mobiusConcreteDeltaDischarge.binding
  divisor_sum_mobius_eq_delta :=
    TS105.Goldbach.mobiusConcreteDeltaDischarge.divisor_sum_mobius_eq_delta
  convolution_from_mathlib_ready := True.intro
  convolution_associative_ready := True.intro

/--
Gcd/lcm kernel algebra package.

The equality field is concrete and is proved below for the canonical kernels.
The remaining markers identify the later algebra required by Selberg's
quadratic-form diagonalization.
-/
structure GCDLCMKernelAlgebra where
  gcdKernel :
    Nat -> Nat -> Rat

  lcmKernel :
    Nat -> Nat -> Rat

  gcd_mul_lcm :
    forall a b : Nat,
      gcdKernel a b * lcmKernel a b = (a * b : Rat)

  gcd_lcm_kernel_ready :
    True

  divisor_square_kernel_ready :
    True

  diagonalization_kernel_ready :
    True

/-- Canonical gcd/lcm kernel algebra package. -/
def gcdLCMKernelAlgebra :
    GCDLCMKernelAlgebra where
  gcdKernel := canonicalGcdKernel
  lcmKernel := canonicalLcmKernel
  gcd_mul_lcm := canonicalGcdKernel_mul_lcmKernel
  gcd_lcm_kernel_ready := True.intro
  divisor_square_kernel_ready := True.intro
  diagonalization_kernel_ready := True.intro

/--
Selberg quadratic-kernel extraction ledger.

This names the bridge from divisor kernels to the finite quadratic kernel
expected by TS100.
-/
structure SelbergQuadraticKernelExtraction where
  quadraticKernel :
    Nat -> Nat -> Rat

  kernelAlgebra :
    GCDLCMKernelAlgebra

  quadratic_kernel_from_gcd_lcm_ready :
    True

  nonnegative_quadratic_form_ready :
    True

  diagonalization_ready :
    True

  divisor_square_majorant_ready :
    True

/--
Divisor-kernel algebra infrastructure sufficient to recover TS103's full
Mobius inversion infrastructure.

The TS30 majorant, sieve, and budget fields remain the hard Selberg and
Brun-Titchmarsh obligations.
-/
structure DivisorKernelAlgebraInfrastructure where
  convolution :
    DivisorConvolutionBridge

  kernel :
    GCDLCMKernelAlgebra

  extraction :
    SelbergQuadraticKernelExtraction

  level :
    Nat

  divisorWeight :
    Nat -> Rat

  support_bound :
    forall d : Nat,
      ((divisorWeight d = 0) -> False) ->
        d <= level

  weight_one :
    divisorWeight 1 = 1

  divisorConvolution :
    Nat -> Nat -> Rat

  divisor_convolution_from_kernel_ready :
    True

  quadraticLedger :
    TS100.Goldbach.SelbergQuadraticFormLedger

  quadratic_weight_agreement :
    forall d : Nat,
      quadraticLedger.weight d = divisorWeight d

  quadratic_kernel_from_divisor_kernel_ready :
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

  majorant_from_divisor_kernel_ready :
    True

  sieve_from_divisor_kernel_ready :
    True

  budget_from_divisor_kernel_ready :
    True

/-- Target proposition for the divisor-convolution bridge. -/
def DivisorConvolutionBridgeTarget : Prop :=
  Nonempty DivisorConvolutionBridge

/-- Target proposition for gcd/lcm kernel algebra. -/
def GCDLCMKernelAlgebraTarget : Prop :=
  Nonempty GCDLCMKernelAlgebra

/-- Target proposition for Selberg quadratic-kernel extraction. -/
def SelbergQuadraticKernelExtractionTarget : Prop :=
  Nonempty SelbergQuadraticKernelExtraction

/-- Target proposition for full divisor-kernel algebra infrastructure. -/
def DivisorKernelAlgebraInfrastructureTarget : Prop :=
  Nonempty DivisorKernelAlgebraInfrastructure

/-- The divisor-convolution bridge is populated by TS104 and TS105. -/
theorem divisorConvolutionBridgeTarget :
    DivisorConvolutionBridgeTarget :=
  Nonempty.intro divisorConvolutionBridge

/-- The canonical gcd/lcm kernel algebra is populated. -/
theorem gcdLCMKernelAlgebraTarget :
    GCDLCMKernelAlgebraTarget :=
  Nonempty.intro gcdLCMKernelAlgebra

/-- A divisor-kernel algebra infrastructure supplies a TS103 Mobius ledger. -/
def mobiusInversionLedger_of_divisorKernelAlgebraInfrastructure
    (H : DivisorKernelAlgebraInfrastructure) :
    TS103.Goldbach.MobiusInversionLedger where
  level := H.level
  divisorWeight := H.divisorWeight
  support_bound := H.support_bound
  weight_one := H.weight_one
  divisorAPI := H.convolution.divisorAPI
  mobius :=
    TS105.Goldbach.mobiusDeltaIdentity_of_concreteDeltaDischarge
      H.convolution.delta
  divisorConvolution := H.divisorConvolution
  gcdKernel := H.kernel.gcdKernel
  lcmKernel := H.kernel.lcmKernel
  divisor_convolution_from_mobius_ready :=
    H.divisor_convolution_from_kernel_ready
  gcd_lcm_kernel_from_mobius_ready := H.kernel.gcd_lcm_kernel_ready
  quadratic_kernel_extraction_ready :=
    H.extraction.quadratic_kernel_from_gcd_lcm_ready

/--
A divisor-kernel algebra infrastructure supplies the full TS103 Mobius
inversion infrastructure.
-/
def mobiusInversionInfrastructure_of_divisorKernelAlgebraInfrastructure
    (H : DivisorKernelAlgebraInfrastructure) :
    TS103.Goldbach.MobiusInversionInfrastructure where
  mobius := mobiusInversionLedger_of_divisorKernelAlgebraInfrastructure H
  quadraticLedger := H.quadraticLedger
  quadratic_weight_agreement := H.quadratic_weight_agreement
  quadratic_kernel_from_mobius_ready :=
    H.quadratic_kernel_from_divisor_kernel_ready
  weightLedger := H.weightLedger
  weight_agreement := H.weight_agreement
  majorant := H.majorant
  sieve := H.sieve
  budget := H.budget
  majorant_from_mobius_ready := H.majorant_from_divisor_kernel_ready
  sieve_from_mobius_ready := H.sieve_from_divisor_kernel_ready
  budget_from_mobius_ready := H.budget_from_divisor_kernel_ready

/--
A divisor-kernel algebra infrastructure target supplies the TS103 Mobius
inversion infrastructure target.
-/
theorem mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
    (H : DivisorKernelAlgebraInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (mobiusInversionInfrastructure_of_divisorKernelAlgebraInfrastructure
            h)

/--
Divisor-kernel algebra infrastructure supplies the TS101 divisor-algebra
infrastructure target through TS103.
-/
theorem selbergDivisorAlgebraInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
    (H : DivisorKernelAlgebraInfrastructureTarget) :
    TS101.Goldbach.SelbergDivisorAlgebraInfrastructureTarget :=
  TS103.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_mobiusInversionInfrastructureTarget
    (mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
      H)

/--
Divisor-kernel algebra infrastructure plus TS95 and TS83 supply the TS98 final
root input package.
-/
theorem finalHorizonInputsTarget_of_divisorKernel_trace_mellin
    (Hs : DivisorKernelAlgebraInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS103.Goldbach.finalHorizonInputsTarget_of_mobius_trace_mellin
    (mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Divisor-kernel algebra infrastructure plus TS95 and TS83 feed the TS84 padded
final API route.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_divisorKernel_trace_mellin
    (Hs : DivisorKernelAlgebraInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS103.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobius_trace_mellin
    (mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Divisor-kernel algebra infrastructure plus TS95 and TS83 feed the full TS25
padded-scale infrastructure.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_divisorKernel_trace_mellin
    (Hs : DivisorKernelAlgebraInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS103.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobius_trace_mellin
    (mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS106
