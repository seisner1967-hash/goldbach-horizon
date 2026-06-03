import Mathlib.NumberTheory.ArithmeticFunction
import TS.Goldbach.Strong.TS103.MobiusInversionLedger

namespace TS104
namespace Goldbach

/-!
# TS104 - Mobius Mathlib API Probe

TS103 records the Mobius-inversion layer expected by the Selberg divisor
algebra. This sprint probes the current Mathlib API and binds the concrete
symbols that will be useful for a future proof:

* `ArithmeticFunction.moebius`;
* `ArithmeticFunction.zeta`;
* Dirichlet convolution on `ArithmeticFunction`;
* the existing convolution inverse theorem for `moebius` and `zeta`.

This sprint does not prove the TS103 Mobius inversion infrastructure, gcd/lcm
kernel algebra, Selberg's sieve, Brun-Titchmarsh, or any prime-count estimate.
It only records a concrete Mathlib binding layer and the remaining bridge
shape into TS103.
-/

open Finset

/-- Status marker for a Mathlib symbol probed in TS104. -/
inductive MobiusSymbolStatus where
  | located
  | locatedWithInverseTheorem
  | pendingConcreteBridge
deriving DecidableEq, Repr

/--
Mathlib Mobius API probe.

The `moebius_mul_zeta` and `zeta_mul_moebius` fields record that Mathlib
already exposes the key Dirichlet-convolution inverse theorem at the bundled
`ArithmeticFunction` level.
-/
structure MobiusMathlibAPIProbe where
  mobiusStatus :
    MobiusSymbolStatus

  zetaStatus :
    MobiusSymbolStatus

  divisorSumStatus :
    MobiusSymbolStatus

  convolutionStatus :
    MobiusSymbolStatus

  inverseTheoremStatus :
    MobiusSymbolStatus

  moebius_mul_zeta :
    (ArithmeticFunction.moebius * ArithmeticFunction.zeta :
      ArithmeticFunction Int) = 1

  zeta_mul_moebius :
    (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction Int) = 1

/-- Mathlib Mobius as an unbundled rational-valued function. -/
def mathlibMoebiusFun
    (n : Nat) :
    Rat :=
  (ArithmeticFunction.moebius n : Rat)

/-- Mathlib's divisor finset as the TS104 divisor-sum operator. -/
def mathlibDivisorSum
    (f : Nat -> Rat)
    (n : Nat) :
    Rat :=
  (Nat.divisors n).sum f

/-- Mathlib's divisor antidiagonal as the TS104 convolution operator. -/
def mathlibDirichletConvolution
    (f g : Nat -> Rat)
    (n : Nat) :
    Rat :=
  (Nat.divisorsAntidiagonal n).sum fun x =>
    f x.fst * g x.snd

/-- The arithmetic-function unit delta, viewed as an unbundled function. -/
def mathlibArithmeticDelta
    (n : Nat) :
    Rat :=
  (1 : ArithmeticFunction Rat) n

/-- The Mathlib delta is `1` at `1`. -/
theorem mathlibArithmeticDelta_one :
    mathlibArithmeticDelta 1 = 1 := by
  simp [mathlibArithmeticDelta]

/-- The Mathlib delta is `0` away from `1`. -/
theorem mathlibArithmeticDelta_ne_one_zero
    (n : Nat)
    (hn : ((n = 1) -> False)) :
    mathlibArithmeticDelta n = 0 := by
  simpa [mathlibArithmeticDelta] using
    (ArithmeticFunction.one_apply_ne (R := Rat) hn)

/-- Concrete Mathlib API probe populated by the current environment. -/
def mobiusMathlibAPIProbe :
    MobiusMathlibAPIProbe where
  mobiusStatus := MobiusSymbolStatus.located
  zetaStatus := MobiusSymbolStatus.located
  divisorSumStatus := MobiusSymbolStatus.located
  convolutionStatus := MobiusSymbolStatus.located
  inverseTheoremStatus := MobiusSymbolStatus.locatedWithInverseTheorem
  moebius_mul_zeta := ArithmeticFunction.moebius_mul_coe_zeta
  zeta_mul_moebius := ArithmeticFunction.coe_zeta_mul_moebius

/--
Concrete Mobius binding expected by TS103.

The field `mobius_delta_ready` remains a marker: this binding has located the
Mathlib symbols and the bundled inverse theorem, but it does not yet provide
the full unbundled divisor-sum proof required to discharge all TS103 Selberg
infrastructure.
-/
structure MobiusConcreteBinding where
  mobiusFun :
    Nat -> Rat

  divisorSum :
    (Nat -> Rat) -> Nat -> Rat

  convolution :
    (Nat -> Rat) -> (Nat -> Rat) -> Nat -> Rat

  delta :
    Nat -> Rat

  delta_one :
    delta 1 = 1

  delta_ne_one_zero :
    forall n : Nat,
      ((n = 1) -> False) ->
        delta n = 0

  mobius_matches_mathlib :
    forall n : Nat,
      mobiusFun n = mathlibMoebiusFun n

  divisor_sum_matches_mathlib :
    forall f : Nat -> Rat,
      forall n : Nat,
        divisorSum f n = mathlibDivisorSum f n

  convolution_matches_mathlib :
    forall f g : Nat -> Rat,
      forall n : Nat,
        convolution f g n = mathlibDirichletConvolution f g n

  mobius_zeta_inverse_ready :
    True

  mobius_delta_ready :
    True

/-- Concrete TS104 binding to the Mathlib Mobius/divisor/convolution symbols. -/
def mobiusConcreteBinding :
    MobiusConcreteBinding where
  mobiusFun := mathlibMoebiusFun
  divisorSum := mathlibDivisorSum
  convolution := mathlibDirichletConvolution
  delta := mathlibArithmeticDelta
  delta_one := mathlibArithmeticDelta_one
  delta_ne_one_zero := mathlibArithmeticDelta_ne_one_zero
  mobius_matches_mathlib := fun _ => rfl
  divisor_sum_matches_mathlib := fun _ _ => rfl
  convolution_matches_mathlib := fun _ _ _ => rfl
  mobius_zeta_inverse_ready := True.intro
  mobius_delta_ready := True.intro

/-- A concrete Mobius binding supplies the TS103 divisor-sum/convolution API. -/
def divisorSumConvolution_of_concreteBinding
    (H : MobiusConcreteBinding) :
    TS103.Goldbach.DivisorSumConvolution where
  divisorSum := H.divisorSum
  convolution := H.convolution
  divisor_sum_finite_ready := True.intro
  convolution_finite_ready := True.intro
  convolution_matches_divisor_sum_ready := True.intro
  convolution_associative_ready := True.intro

/-- A concrete Mobius binding supplies the TS103 Mobius-delta identity package. -/
def mobiusDeltaIdentity_of_concreteBinding
    (H : MobiusConcreteBinding) :
    TS103.Goldbach.MobiusDeltaIdentity where
  mu := H.mobiusFun
  delta := H.delta
  delta_one := H.delta_one
  delta_ne_one_zero := H.delta_ne_one_zero
  mobius_delta_ready := H.mobius_delta_ready
  mobius_inversion_ready := H.mobius_zeta_inverse_ready

/--
Mobius concrete-binding infrastructure sufficient to recover the TS103
Mobius-inversion infrastructure.

The remaining Selberg fields are still explicit inputs. This is the exact
place where a future proof will connect concrete Mobius algebra to the
quadratic-form and interval-sieve obligations.
-/
structure MobiusConcreteBindingInfrastructure where
  binding :
    MobiusConcreteBinding

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

  gcdKernel :
    Nat -> Nat -> Rat

  lcmKernel :
    Nat -> Nat -> Rat

  divisor_convolution_from_binding_ready :
    True

  gcd_lcm_kernel_from_binding_ready :
    True

  quadratic_kernel_extraction_ready :
    True

  quadraticLedger :
    TS100.Goldbach.SelbergQuadraticFormLedger

  quadratic_weight_agreement :
    forall d : Nat,
      quadraticLedger.weight d = divisorWeight d

  quadratic_kernel_from_binding_ready :
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

  majorant_from_binding_ready :
    True

  sieve_from_binding_ready :
    True

  budget_from_binding_ready :
    True

/-- Target proposition for the Mathlib Mobius API probe. -/
def MobiusMathlibAPIProbeTarget : Prop :=
  Nonempty MobiusMathlibAPIProbe

/-- Target proposition for the concrete Mobius binding. -/
def MobiusConcreteBindingTarget : Prop :=
  Nonempty MobiusConcreteBinding

/-- Target proposition for the full concrete-binding infrastructure. -/
def MobiusConcreteBindingInfrastructureTarget : Prop :=
  Nonempty MobiusConcreteBindingInfrastructure

/-- The TS104 Mathlib API probe is populated. -/
theorem mobiusMathlibAPIProbeTarget :
    MobiusMathlibAPIProbeTarget :=
  Nonempty.intro mobiusMathlibAPIProbe

/-- The concrete Mathlib Mobius binding is populated. -/
theorem mobiusConcreteBindingTarget :
    MobiusConcreteBindingTarget :=
  Nonempty.intro mobiusConcreteBinding

/-- A concrete binding supplies the TS103 divisor-sum/convolution target. -/
theorem divisorSumConvolutionTarget_of_concreteBindingTarget
    (H : MobiusConcreteBindingTarget) :
    TS103.Goldbach.DivisorSumConvolutionTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (divisorSumConvolution_of_concreteBinding h)

/-- A concrete binding supplies the TS103 Mobius-delta target. -/
theorem mobiusDeltaIdentityTarget_of_concreteBindingTarget
    (H : MobiusConcreteBindingTarget) :
    TS103.Goldbach.MobiusDeltaIdentityTarget := by
  cases H with
  | intro h =>
      exact Nonempty.intro (mobiusDeltaIdentity_of_concreteBinding h)

/-- A concrete-binding infrastructure supplies a TS103 Mobius ledger. -/
def mobiusInversionLedger_of_concreteBindingInfrastructure
    (H : MobiusConcreteBindingInfrastructure) :
    TS103.Goldbach.MobiusInversionLedger where
  level := H.level
  divisorWeight := H.divisorWeight
  support_bound := H.support_bound
  weight_one := H.weight_one
  divisorAPI := divisorSumConvolution_of_concreteBinding H.binding
  mobius := mobiusDeltaIdentity_of_concreteBinding H.binding
  divisorConvolution := H.divisorConvolution
  gcdKernel := H.gcdKernel
  lcmKernel := H.lcmKernel
  divisor_convolution_from_mobius_ready :=
    H.divisor_convolution_from_binding_ready
  gcd_lcm_kernel_from_mobius_ready :=
    H.gcd_lcm_kernel_from_binding_ready
  quadratic_kernel_extraction_ready := H.quadratic_kernel_extraction_ready

/-- A concrete-binding infrastructure supplies the full TS103 infrastructure. -/
def mobiusInversionInfrastructure_of_concreteBindingInfrastructure
    (H : MobiusConcreteBindingInfrastructure) :
    TS103.Goldbach.MobiusInversionInfrastructure where
  mobius := mobiusInversionLedger_of_concreteBindingInfrastructure H
  quadraticLedger := H.quadraticLedger
  quadratic_weight_agreement := H.quadratic_weight_agreement
  quadratic_kernel_from_mobius_ready :=
    H.quadratic_kernel_from_binding_ready
  weightLedger := H.weightLedger
  weight_agreement := H.weight_agreement
  majorant := H.majorant
  sieve := H.sieve
  budget := H.budget
  majorant_from_mobius_ready := H.majorant_from_binding_ready
  sieve_from_mobius_ready := H.sieve_from_binding_ready
  budget_from_mobius_ready := H.budget_from_binding_ready

/--
A concrete-binding infrastructure target supplies the TS103 Mobius inversion
infrastructure target.
-/
theorem mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget
    (H : MobiusConcreteBindingInfrastructureTarget) :
    TS103.Goldbach.MobiusInversionInfrastructureTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (mobiusInversionInfrastructure_of_concreteBindingInfrastructure h)

/--
Concrete-binding infrastructure plus the TS95 trace ledger and TS83
Mellin-tail contracts supply the TS98 final root input package.
-/
theorem finalHorizonInputsTarget_of_mobiusConcrete_trace_mellin
    (Hs : MobiusConcreteBindingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS98.Goldbach.FinalHorizonInputsTarget :=
  TS103.Goldbach.finalHorizonInputsTarget_of_mobius_trace_mellin
    (mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Concrete-binding infrastructure plus the TS95 trace ledger and TS83
Mellin-tail contracts feed the TS84 padded final API route through TS103.
-/
theorem paddedScaleTransferFinalAPIContractsTarget_of_mobiusConcrete_trace_mellin
    (Hs : MobiusConcreteBindingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget :=
  TS103.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobius_trace_mellin
    (mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget
      Hs)
    Ht
    Hm

/--
Concrete-binding infrastructure plus the TS95 trace ledger and TS83
Mellin-tail contracts feed the full TS25 padded-scale infrastructure through
TS103.
-/
theorem paddedScaleAnalyticInfrastructureTarget_of_mobiusConcrete_trace_mellin
    (Hs : MobiusConcreteBindingInfrastructureTarget)
    (Ht : TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget)
    (Hm : TS83.MellinJackson.MellinTailFinalAPIContractsTarget) :
    Nonempty TS25.Goldbach.PaddedScaleAnalyticInfrastructure :=
  TS103.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobius_trace_mellin
    (mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget
      Hs)
    Ht
    Hm

end Goldbach
end TS104
