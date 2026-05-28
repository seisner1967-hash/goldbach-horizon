import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS37.MellinFourierLpNormInputs

namespace TS38
namespace MellinJackson

open MeasureTheory Filter

/-!
# TS38 - Mellin-Fourier Lp Linearity Inputs

This sprint isolates the almost-everywhere linearity side of the future
Mellin-Fourier `L²` isometry.

Together with TS37, it gives the two orthogonal projections of the TS36
`Lp` roadmap: norm preservation and algebraic compatibility.
-/

/--
Linearity inputs for the Mellin-Fourier representative operators.

The fields are exactly the a.e. equalities needed before lifting additivity and
scalar compatibility to the future `Lp`-level linear isometry.
-/
structure MellinFourierLpLinearityInputs where
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
Combine TS37 norm inputs and TS38 linearity inputs into the full TS36
`Lp`-isometry infrastructure.
-/
def lpInfrastructureOfNormAndLinearity
    (N : TS37.MellinJackson.MellinFourierLpNormInputs)
    (L : MellinFourierLpLinearityInputs) :
    TS36.MellinJackson.MellinFourierLpIsometryInfrastructure where
  memℒp_Tsigma := N.memℒp_Tsigma
  memℒp_TsigmaInv := N.memℒp_TsigmaInv
  snorm_Tsigma := N.snorm_Tsigma
  snorm_TsigmaInv := N.snorm_TsigmaInv
  tsigma_add_ae := L.tsigma_add_ae
  tsigma_smul_ae := L.tsigma_smul_ae
  tsigmaInv_add_ae := L.tsigmaInv_add_ae
  tsigmaInv_smul_ae := L.tsigmaInv_smul_ae

/--
Extract the linearity-side package from a full TS36 roadmap.

This shows that TS38 is exactly the linearity projection of the TS36
infrastructure.
-/
def linearityInputsOfRoadmap
    (H : TS36.MellinJackson.MellinFourierLpIsometryRoadmap) :
    MellinFourierLpLinearityInputs where
  tsigma_add_ae := H.lp_infrastructure.tsigma_add_ae
  tsigma_smul_ae := H.lp_infrastructure.tsigma_smul_ae
  tsigmaInv_add_ae := H.lp_infrastructure.tsigmaInv_add_ae
  tsigmaInv_smul_ae := H.lp_infrastructure.tsigmaInv_smul_ae

/-- Standalone target for the linearity side. -/
def MellinFourierLpLinearityInputsTarget : Prop :=
  Nonempty MellinFourierLpLinearityInputs

/-- A full TS36 roadmap provides the TS38 linearity inputs. -/
theorem linearityTarget_of_roadmap
    (H : TS36.MellinJackson.MellinFourierLpIsometryRoadmap) :
    MellinFourierLpLinearityInputsTarget :=
  ⟨linearityInputsOfRoadmap H⟩

end MellinJackson
end TS38
