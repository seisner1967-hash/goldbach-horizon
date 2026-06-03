import Mathlib.NumberTheory.ArithmeticFunction
import TS.Goldbach.Strong.TS104.MobiusMathlibAPIProbe

namespace TS105
namespace Goldbach

/-!
# TS105 - Mobius Delta Identity Discharge

TS104 located Mathlib's bundled Mobius API. This sprint discharges the first
concrete arithmetic bridge below TS103: the finite divisor sum of Mathlib's
Mobius function is the arithmetic delta function.

The proof uses Mathlib's bundled convolution inverse theorem
`ArithmeticFunction.coe_moebius_mul_coe_zeta` and rewrites the product with
`ArithmeticFunction.coe_mul_zeta_apply`.

This sprint does not prove the gcd/lcm kernel algebra, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.
-/

open Finset

/-- The Mathlib Mobius divisor sum is the arithmetic-function delta. -/
theorem mathlibMoebiusDivisorSum_eq_delta
    (n : Nat) :
    TS104.Goldbach.mathlibDivisorSum
        TS104.Goldbach.mathlibMoebiusFun n =
      TS104.Goldbach.mathlibArithmeticDelta n := by
  unfold TS104.Goldbach.mathlibDivisorSum
  unfold TS104.Goldbach.mathlibMoebiusFun
  unfold TS104.Goldbach.mathlibArithmeticDelta
  have h :=
    congrArg
      (fun F : ArithmeticFunction Rat => F n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := Rat))
  change
    (ArithmeticFunction.moebius * ArithmeticFunction.zeta :
      ArithmeticFunction Rat) n =
      (1 : ArithmeticFunction Rat) n at h
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa using h

/-- The Mathlib arithmetic delta is the explicit `if n = 1 then 1 else 0`. -/
theorem mathlibArithmeticDelta_eq_ite
    (n : Nat) :
    TS104.Goldbach.mathlibArithmeticDelta n =
      if n = 1 then 1 else 0 := by
  simpa [TS104.Goldbach.mathlibArithmeticDelta] using
    (ArithmeticFunction.one_apply (R := Rat) (x := n))

/-- The Mobius divisor-sum identity in explicit delta form. -/
theorem mathlibMoebiusDivisorSum_eq_ite
    (n : Nat) :
    TS104.Goldbach.mathlibDivisorSum
        TS104.Goldbach.mathlibMoebiusFun n =
      if n = 1 then 1 else 0 := by
  rw [mathlibMoebiusDivisorSum_eq_delta]
  exact mathlibArithmeticDelta_eq_ite n

/-- The concrete TS104 binding satisfies the Mobius-delta divisor-sum identity. -/
theorem mobiusConcreteBinding_divisorSum_mobius_eq_delta
    (n : Nat) :
    TS104.Goldbach.mobiusConcreteBinding.divisorSum
        TS104.Goldbach.mobiusConcreteBinding.mobiusFun n =
      TS104.Goldbach.mobiusConcreteBinding.delta n := by
  simpa [TS104.Goldbach.mobiusConcreteBinding] using
    mathlibMoebiusDivisorSum_eq_delta n

/--
Strengthened concrete discharge for the TS104 binding.

Unlike the TS103 marker fields, this structure stores the actual divisor-sum
identity proved from Mathlib's convolution theorem.
-/
structure MobiusConcreteDeltaDischarge where
  binding :
    TS104.Goldbach.MobiusConcreteBinding

  divisor_sum_mobius_eq_delta :
    forall n : Nat,
      binding.divisorSum binding.mobiusFun n = binding.delta n

/-- Concrete Mobius-delta discharge using Mathlib's bundled inverse theorem. -/
def mobiusConcreteDeltaDischarge :
    MobiusConcreteDeltaDischarge where
  binding := TS104.Goldbach.mobiusConcreteBinding
  divisor_sum_mobius_eq_delta :=
    mobiusConcreteBinding_divisorSum_mobius_eq_delta

/-- A concrete Mobius-delta discharge supplies the TS103 Mobius-delta package. -/
def mobiusDeltaIdentity_of_concreteDeltaDischarge
    (H : MobiusConcreteDeltaDischarge) :
    TS103.Goldbach.MobiusDeltaIdentity where
  mu := H.binding.mobiusFun
  delta := H.binding.delta
  delta_one := H.binding.delta_one
  delta_ne_one_zero := H.binding.delta_ne_one_zero
  mobius_delta_ready := True.intro
  mobius_inversion_ready := H.binding.mobius_zeta_inverse_ready

/-- Target proposition for the concrete Mobius-delta discharge. -/
def MobiusConcreteDeltaDischargeTarget : Prop :=
  Nonempty MobiusConcreteDeltaDischarge

/-- The concrete Mobius-delta discharge is populated. -/
theorem mobiusConcreteDeltaDischargeTarget :
    MobiusConcreteDeltaDischargeTarget :=
  Nonempty.intro mobiusConcreteDeltaDischarge

/-- The TS105 discharge supplies the TS103 Mobius-delta target. -/
theorem mobiusDeltaIdentityTarget_of_concreteDeltaDischargeTarget
    (H : MobiusConcreteDeltaDischargeTarget) :
    TS103.Goldbach.MobiusDeltaIdentityTarget := by
  cases H with
  | intro h =>
      exact
        Nonempty.intro
          (mobiusDeltaIdentity_of_concreteDeltaDischarge h)

/-- TS105 discharges the TS103 Mobius-delta target through Mathlib. -/
theorem mobiusDeltaIdentityTarget :
    TS103.Goldbach.MobiusDeltaIdentityTarget :=
  mobiusDeltaIdentityTarget_of_concreteDeltaDischargeTarget
    mobiusConcreteDeltaDischargeTarget

/--
The TS105 concrete discharge also recovers the TS104 concrete-binding target.
-/
theorem mobiusConcreteBindingTarget :
    TS104.Goldbach.MobiusConcreteBindingTarget :=
  Nonempty.intro mobiusConcreteDeltaDischarge.binding

end Goldbach
end TS105
