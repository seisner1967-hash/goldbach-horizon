import Mathlib.Tactic
import TS.Goldbach.Strong.TS18.DirichletCharacterBridge
import TS.Goldbach.Strong.TS22.EnergyScale

namespace TS22
namespace Goldbach

/--
Scale-aware large-sieve infrastructure.

This is the TS22 version of the TS18 large-sieve obligation: instead of forcing
the character-side bound into the rigid `x^2 / Q^2` scale, it targets an
arbitrary explicit `ShortIntervalScale`.
-/
structure ScaledLargeSieveInfrastructure (S : ShortIntervalScale) where
  K : Real
  K_pos : 0 < K
  selectedModulus : Nat -> Nat -> Nat
  sieve_bound :
    forall (D : TS18.Goldbach.DirichletCharacterBridge) (x Q : Nat),
      TS15.Goldbach.LargeX x ->
      Q = Nat.log 2 x * Nat.log 2 x ->
      D.characterSecondMoment x Q (selectedModulus x Q) +
          D.characterBridgeError x Q (selectedModulus x Q) <=
        K * S.scale x Q

/--
A Dirichlet-character bridge plus a scale-aware large-sieve estimate gives a
scaled short-interval second-moment estimate.
-/
noncomputable def secondMomentScaleFromScaledLargeSieve
    {S : ShortIntervalScale}
    (D : TS18.Goldbach.DirichletCharacterBridge)
    (L : ScaledLargeSieveInfrastructure S) :
    ShortIntervalPrimeSecondMomentScale S where
  K := L.K
  K_pos := L.K_pos
  bound := by
    intro x Q hx hQ
    have hD :
        TS15.Goldbach.shortPrimeEnergy x Q <=
          D.characterSecondMoment x Q (L.selectedModulus x Q) +
            D.characterBridgeError x Q (L.selectedModulus x Q) :=
      D.energy_bound x Q (L.selectedModulus x Q) hx hQ
    have hL :
        D.characterSecondMoment x Q (L.selectedModulus x Q) +
            D.characterBridgeError x Q (L.selectedModulus x Q) <=
          L.K * S.scale x Q :=
      L.sieve_bound D x Q hx hQ
    exact le_trans hD hL

/-- Final scaled large-sieve discharge. -/
theorem Problem_E1Scale_from_scaledLargeSieve
    {S : ShortIntervalScale}
    (D : TS18.Goldbach.DirichletCharacterBridge)
    (L : ScaledLargeSieveInfrastructure S) :
    Problem_E1Scale S L.K :=
  Problem_E1Scale_from_second_moment_scale
    (secondMomentScaleFromScaledLargeSieve D L)

end Goldbach
end TS22
