import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS35.MellinFourierAEEqTransport

namespace TS36
namespace MellinJackson

open MeasureTheory Filter

/-!
# TS36 - Mellin-Fourier L2 Isometry Roadmap

This sprint records the exact `Lp`-level inputs still needed after TS35.

TS34 handles measure transport. TS35 descends the representative operators to
`AEEqFun`. TS36 deliberately stops before constructing the final
`LinearIsometryEquiv`; it packages the remaining `Memℒp`, norm, and linearity
facts needed to lift the TS35 quotient transport to `Lp`.
-/

/--
Local infrastructure needed to lift the TS35 `AEEqFun` transport to `L²`.

The fields are the precise obligations that a future concrete proof must
discharge using the TS17 integral identity and the current Mathlib `Lp` API.
-/
structure MellinFourierLpIsometryInfrastructure where
  memℒp_Tsigma :
    forall {sigma : Real} (W : Real -> Complex),
      Memℒp W 2 (TS17.MellinJackson.muWeighted sigma) ->
        Memℒp (TS17.MellinJackson.TsigmaFun sigma W)
          2 (volume : Measure Real)

  memℒp_TsigmaInv :
    forall {sigma : Real} (V : Real -> Complex),
      Memℒp V 2 (volume : Measure Real) ->
        Memℒp (TS17.MellinJackson.TsigmaInvFun sigma V)
          2 (TS17.MellinJackson.muWeighted sigma)

  snorm_Tsigma :
    forall {sigma : Real} (W : Real -> Complex),
      Memℒp W 2 (TS17.MellinJackson.muWeighted sigma) ->
        snorm (TS17.MellinJackson.TsigmaFun sigma W)
          2 (volume : Measure Real) =
        snorm W 2 (TS17.MellinJackson.muWeighted sigma)

  snorm_TsigmaInv :
    forall {sigma : Real} (V : Real -> Complex),
      Memℒp V 2 (volume : Measure Real) ->
        snorm (TS17.MellinJackson.TsigmaInvFun sigma V)
          2 (TS17.MellinJackson.muWeighted sigma) =
        snorm V 2 (volume : Measure Real)

  tsigma_add_ae :
    forall {sigma : Real} (W Z : Real -> Complex),
      TS17.MellinJackson.TsigmaFun sigma (fun x => W x + Z x)
        =ᵐ[(volume : Measure Real)]
          fun u =>
            TS17.MellinJackson.TsigmaFun sigma W u +
              TS17.MellinJackson.TsigmaFun sigma Z u

  tsigma_smul_ae :
    forall {sigma : Real} (c : Complex) (W : Real -> Complex),
      TS17.MellinJackson.TsigmaFun sigma (fun x => c * W x)
        =ᵐ[(volume : Measure Real)]
          fun u => c * TS17.MellinJackson.TsigmaFun sigma W u

  tsigmaInv_add_ae :
    forall {sigma : Real} (V U : Real -> Complex),
      TS17.MellinJackson.TsigmaInvFun sigma (fun u => V u + U u)
        =ᵐ[TS17.MellinJackson.muWeighted sigma]
          fun x =>
            TS17.MellinJackson.TsigmaInvFun sigma V x +
              TS17.MellinJackson.TsigmaInvFun sigma U x

  tsigmaInv_smul_ae :
    forall {sigma : Real} (c : Complex) (V : Real -> Complex),
      TS17.MellinJackson.TsigmaInvFun sigma (fun u => c * V u)
        =ᵐ[TS17.MellinJackson.muWeighted sigma]
          fun x => c * TS17.MellinJackson.TsigmaInvFun sigma V x

/--
Roadmap package for the Mellin-Fourier `L²` isometry.

This is the handoff point between TS35 and the future concrete `Lp` proof:
`ae_transport` supplies quotient transport, while `lp_infrastructure` records
the norm and linearity facts needed by the Banach/Hilbert-space layer.
-/
structure MellinFourierLpIsometryRoadmap where
  ae_transport :
    TS35.MellinJackson.MellinFourierAEEqTransport
  lp_infrastructure :
    MellinFourierLpIsometryInfrastructure

/-- The final target type for a fixed Mellin line parameter `sigma`. -/
def MellinFourierLpIsometryTarget (sigma : Real) : Prop :=
  Nonempty
    (Lp Complex 2 (TS17.MellinJackson.muWeighted sigma) ≃ₗᵢ[Complex]
      Lp Complex 2 (volume : Measure Real))

/--
The roadmap exposes the TS35 `AEEqFun` transport package unchanged.

This small theorem is intentionally modest: the actual `Lp` isometry is still a
future construction, but its lower quotient layer is already available.
-/
theorem ae_transport_of_roadmap
    (H : MellinFourierLpIsometryRoadmap) :
    TS35.MellinJackson.MellinFourierAEEqTransport :=
  H.ae_transport

end MellinJackson
end TS36
