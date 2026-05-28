import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS36.MellinFourierLpIsometryRoadmap

namespace TS37
namespace MellinJackson

open MeasureTheory

/-!
# TS37 - Mellin-Fourier Lp Norm Inputs

This sprint isolates the norm side of the future Mellin-Fourier `L²`
isometry.

TS36 records the full `Lp` roadmap. TS37 separates the two norm tasks that
should be proved before touching quotient linearity or the final
`LinearIsometryEquiv`: preservation of `Memℒp` and preservation of `snorm` in
both directions.
-/

/--
Concrete norm-side inputs for the future Mellin-Fourier `L²` isometry.

Linearity and the final `LinearIsometryEquiv` remain outside this sprint.
-/
structure MellinFourierLpNormInputs where
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

/--
Extract the norm-side package from a full TS36 roadmap.

This shows that TS37 is exactly the norm projection of the TS36 infrastructure,
not a parallel or competing interface.
-/
def normInputsOfRoadmap
    (H : TS36.MellinJackson.MellinFourierLpIsometryRoadmap) :
    MellinFourierLpNormInputs where
  memℒp_Tsigma := H.lp_infrastructure.memℒp_Tsigma
  memℒp_TsigmaInv := H.lp_infrastructure.memℒp_TsigmaInv
  snorm_Tsigma := H.lp_infrastructure.snorm_Tsigma
  snorm_TsigmaInv := H.lp_infrastructure.snorm_TsigmaInv

/--
The standalone target saying that the norm side of the Mellin-Fourier `L²`
bridge has been supplied.
-/
def MellinFourierLpNormInputsTarget : Prop :=
  Nonempty MellinFourierLpNormInputs

/--
Once the full TS36 roadmap is supplied, the TS37 norm-input target is
automatically satisfied.
-/
theorem normInputsTarget_of_roadmap
    (H : TS36.MellinJackson.MellinFourierLpIsometryRoadmap) :
    MellinFourierLpNormInputsTarget :=
  ⟨normInputsOfRoadmap H⟩

end MellinJackson
end TS37
