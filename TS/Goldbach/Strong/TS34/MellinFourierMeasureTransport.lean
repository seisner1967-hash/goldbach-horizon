import Mathlib.Tactic
import TS.Goldbach.Strong.TS17.MellinFourierNormBridge

namespace TS34
namespace MellinJackson

open MeasureTheory Filter Set

/-!
# TS34 - Mellin-Fourier Measure Transport

This sprint isolates the measure-transport facts needed before constructing a
concrete Mellin/Fourier `L²` isometry. It deliberately stops before the `Lp`
quotient layer.
-/

/--
Measure-transport infrastructure needed for the concrete Mellin/Fourier bridge.

The fields are the local almost-everywhere transport facts required to move
statements between the weighted Mellin measure, Lebesgue measure restricted to
the positive half-line, and Lebesgue measure under `exp`/`log`.
-/
structure MellinFourierMeasureTransport where
  ae_volume_Ioi_of_ae_muWeighted :
    forall {sigma : Real} {P : Real -> Prop},
      (∀ᵐ x ∂(TS17.MellinJackson.muWeighted sigma), P x) ->
      ∀ᵐ x ∂((volume : Measure Real).restrict (Ioi (0 : Real))), P x

  ae_muWeighted_of_ae_volume_Ioi :
    forall {sigma : Real} {P : Real -> Prop},
      (∀ᵐ x ∂((volume : Measure Real).restrict (Ioi (0 : Real))), P x) ->
      ∀ᵐ x ∂(TS17.MellinJackson.muWeighted sigma), P x

  ae_volume_comp_exp_of_ae_volume_Ioi :
    forall {P : Real -> Prop},
      (∀ᵐ x ∂((volume : Measure Real).restrict (Ioi (0 : Real))), P x) ->
      ∀ᵐ u ∂(volume : Measure Real), P (Real.exp u)

  ae_volume_Ioi_comp_log_of_ae_volume :
    forall {P : Real -> Prop},
      (∀ᵐ u ∂(volume : Measure Real), P u) ->
      ∀ᵐ x ∂((volume : Measure Real).restrict (Ioi (0 : Real))), P (Real.log x)

/--
The measure transport package gives congruence of `TsigmaFun` under a.e.
equality on the weighted Mellin side.
-/
theorem tsigmaFun_congr_of_measureTransport
    (H : MellinFourierMeasureTransport)
    {sigma : Real} {W Z : Real -> Complex}
    (hWZ : W =ᵐ[TS17.MellinJackson.muWeighted sigma] Z) :
    TS17.MellinJackson.TsigmaFun sigma W
      =ᵐ[(volume : Measure Real)]
        TS17.MellinJackson.TsigmaFun sigma Z := by
  have hIoi :
      ∀ᵐ x ∂((volume : Measure Real).restrict (Ioi (0 : Real))), W x = Z x :=
    H.ae_volume_Ioi_of_ae_muWeighted (P := fun x => W x = Z x) hWZ
  have hexp :
      ∀ᵐ u ∂(volume : Measure Real), W (Real.exp u) = Z (Real.exp u) :=
    H.ae_volume_comp_exp_of_ae_volume_Ioi (P := fun x => W x = Z x) hIoi
  filter_upwards [hexp] with u hu
  simp [TS17.MellinJackson.TsigmaFun, hu]

/--
The measure transport package gives congruence of `TsigmaInvFun` under a.e.
equality on the Lebesgue side.
-/
theorem tsigmaInvFun_congr_of_measureTransport
    (H : MellinFourierMeasureTransport)
    {sigma : Real} {V U : Real -> Complex}
    (hVU : V =ᵐ[(volume : Measure Real)] U) :
    TS17.MellinJackson.TsigmaInvFun sigma V
      =ᵐ[TS17.MellinJackson.muWeighted sigma]
        TS17.MellinJackson.TsigmaInvFun sigma U := by
  have hlogIoi :
      ∀ᵐ x ∂((volume : Measure Real).restrict (Ioi (0 : Real))),
        V (Real.log x) = U (Real.log x) :=
    H.ae_volume_Ioi_comp_log_of_ae_volume (P := fun u => V u = U u) hVU
  have hlogMu :
      ∀ᵐ x ∂(TS17.MellinJackson.muWeighted sigma),
        V (Real.log x) = U (Real.log x) :=
    H.ae_muWeighted_of_ae_volume_Ioi
      (P := fun x => V (Real.log x) = U (Real.log x)) hlogIoi
  filter_upwards [hlogMu] with x hx
  by_cases hpos : 0 < x
  · simp [TS17.MellinJackson.TsigmaInvFun, hpos, hx]
  · simp [TS17.MellinJackson.TsigmaInvFun, hpos]

end MellinJackson
end TS34
