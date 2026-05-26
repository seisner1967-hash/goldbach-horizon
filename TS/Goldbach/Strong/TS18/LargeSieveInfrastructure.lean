import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import TS.Goldbach.Strong.TS18.DirichletCharacterBridge

namespace TS18
namespace Goldbach

/--
Local large-sieve infrastructure for TS18.

The selected modulus packages the averaging step, while `sieve_bound` packages
the large-sieve estimate and the final elementary normalization to
`C * x^2 / Q^2`.
-/
structure LargeSieveInfrastructure where
  C : Real
  C_pos : 0 < C
  C_le_one : C <= 1
  selectedModulus : Nat -> Nat -> Nat
  sieve_bound :
    forall (D : DirichletCharacterBridge) (x Q : Nat),
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      D.characterSecondMoment x Q (selectedModulus x Q) +
          D.characterBridgeError x Q (selectedModulus x Q) <=
        C * ((x : Real)^2 / ((Q : Real)^2))

end Goldbach
end TS18
