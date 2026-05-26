import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.DirichletCharacter.Basic
import TS.Goldbach.Strong.TS15.ShortIntervalSecondMoment

namespace TS18
namespace Goldbach

/--
Local Dirichlet-character bridge.

This is the formal place for the orthogonality and discrete Parseval step:
it bounds the short-interval energy by a character-side second moment plus the
bridge error.
-/
structure DirichletCharacterBridge where
  /--
  Character-side second moment for the modulus selected by the analytic
  argument.
  -/
  characterSecondMoment : Nat -> Nat -> Nat -> Real

  /--
  Bridge error between the short-interval prime energy and the character
  second moment.
  -/
  characterBridgeError : Nat -> Nat -> Nat -> Real

  energy_bound :
    forall (x Q q : Nat),
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      TS15.Goldbach.shortPrimeEnergy x Q <=
        characterSecondMoment x Q q + characterBridgeError x Q q

end Goldbach
end TS18
