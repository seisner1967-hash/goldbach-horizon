import Mathlib.Tactic
import TS.Goldbach.Strong.TS34.MellinFourierMeasureTransport

namespace TS35
namespace MellinJackson

open MeasureTheory Filter Set

/-!
# TS35 - Mellin-Fourier AEEqFun Transport

This sprint crosses the almost-everywhere quotient layer, but deliberately
stops before the `Lp` quotient and the `L²` isometry.

It combines the TS34 measure-transport contract with a local strong
measurability contract, converts the result into the already compiled TS17
`AEEqFun` transport package, and re-exports the descended operators and their
inverse laws.
-/

/--
Strong-measurability infrastructure for the Mellin/Fourier representative
operators.

The future concrete proof should come from measurability of composition by
`exp`/`log` and multiplication by continuous weights.
-/
structure MellinFourierMeasurabilityTransport where
  tsigma_aestronglyMeasurable :
    forall {sigma : Real} (W : Real -> Complex),
      AEStronglyMeasurable W (TS17.MellinJackson.muWeighted sigma) ->
        AEStronglyMeasurable
          (TS17.MellinJackson.TsigmaFun sigma W)
          (volume : Measure Real)

  inv_aestronglyMeasurable :
    forall {sigma : Real} (V : Real -> Complex),
      AEStronglyMeasurable V (volume : Measure Real) ->
        AEStronglyMeasurable
          (TS17.MellinJackson.TsigmaInvFun sigma V)
          (TS17.MellinJackson.muWeighted sigma)

/--
Complete AEEq transport package: TS34 measure transport plus the local strong
measurability facts needed to create `AEEqFun` representatives.
-/
structure MellinFourierAEEqTransport where
  measure :
    TS34.MellinJackson.MellinFourierMeasureTransport
  measurability :
    MellinFourierMeasurabilityTransport

/--
Convert the TS35 two-layer package into the fixed-`sigma` TS17 transport
package.

TS17 already contains the quotient-level `AEEqFun` construction. TS35 only
feeds it the TS34 congruence lemmas and the new measurability contract.
-/
def toTS17AEEqTransport
    {sigma : Real} (H : MellinFourierAEEqTransport) :
    TS17.MellinJackson.MellinFourierAEEqTransport sigma where
  tsigma_aestronglyMeasurable := by
    intro W hW
    exact H.measurability.tsigma_aestronglyMeasurable W hW
  tsigma_congr := by
    intro W Z hWZ
    exact TS34.MellinJackson.tsigmaFun_congr_of_measureTransport
      H.measure hWZ
  inv_aestronglyMeasurable := by
    intro V hV
    exact H.measurability.inv_aestronglyMeasurable V hV
  inv_congr := by
    intro V U hVU
    exact TS34.MellinJackson.tsigmaInvFun_congr_of_measureTransport
      H.measure hVU

/-- Descent of `TsigmaFun` to almost-everywhere equivalence classes. -/
noncomputable def TsigmaAEEqFun
    {sigma : Real} (H : MellinFourierAEEqTransport) :
    AEEqFun Real Complex (TS17.MellinJackson.muWeighted sigma) ->
      AEEqFun Real Complex (volume : Measure Real) :=
  TS17.MellinJackson.TsigmaAEEqFun
    (toTS17AEEqTransport (sigma := sigma) H)

/-- Descent of `TsigmaInvFun` to almost-everywhere equivalence classes. -/
noncomputable def TsigmaInvAEEqFun
    {sigma : Real} (H : MellinFourierAEEqTransport) :
    AEEqFun Real Complex (volume : Measure Real) ->
      AEEqFun Real Complex (TS17.MellinJackson.muWeighted sigma) :=
  TS17.MellinJackson.TsigmaInvAEEqFun
    (toTS17AEEqTransport (sigma := sigma) H)

/-- The descended inverse is a left inverse on `AEEqFun`. -/
theorem TsigmaInvAEEqFun_left
    {sigma : Real} (H : MellinFourierAEEqTransport)
    (F : AEEqFun Real Complex (TS17.MellinJackson.muWeighted sigma)) :
    TsigmaInvAEEqFun (sigma := sigma) H
      (TsigmaAEEqFun (sigma := sigma) H F) = F :=
  TS17.MellinJackson.TsigmaInvAEEqFun_left
    (toTS17AEEqTransport (sigma := sigma) H) F

/-- The descended inverse is a right inverse on `AEEqFun`. -/
theorem TsigmaInvAEEqFun_right
    {sigma : Real} (H : MellinFourierAEEqTransport)
    (F : AEEqFun Real Complex (volume : Measure Real)) :
    TsigmaAEEqFun (sigma := sigma) H
      (TsigmaInvAEEqFun (sigma := sigma) H F) = F :=
  TS17.MellinJackson.TsigmaInvAEEqFun_right
    (toTS17AEEqTransport (sigma := sigma) H) F

end MellinJackson
end TS35
