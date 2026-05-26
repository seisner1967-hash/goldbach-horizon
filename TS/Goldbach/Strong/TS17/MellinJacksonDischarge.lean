import Mathlib.Data.Real.Basic
import TS.Goldbach.Strong.TS15.MellinJacksonFourier
import TS.Goldbach.Strong.TS17.MellinJacksonInfrastructure
import TS.Goldbach.Strong.TS17.FourierTailBound

namespace TS17
namespace MellinJackson

/--
TS17 discharge of the TS15 Mellin-Jackson projection interface.

The proof is relative to two local analytic infrastructure records:
* `MellinFourierNormBridge`, for the logarithmic Mellin/Fourier norm bridge;
* `FourierTailInfrastructure`, for the Plancherel/Fourier tail estimate.
-/
theorem mellin_jackson_projection_bound
    (B : MellinFourierNormBridge)
    (I : FourierTailInfrastructure) :
    TS15.MellinJackson.MellinJacksonProjectionBound := by
  refine ⟨?_⟩
  intro b k T hT

  have htail :
      TS15.MellinJackson.mellinTailNorm T b =
        fourierTailNorm T (logPullback b) :=
    B.tail_bridge b T

  have htheta :
      TS15.MellinJackson.mellinNorm
          (TS15.MellinJackson.thetaIter k b)
        =
        derivativeL2Norm k (logPullback b) :=
    B.theta_bridge b k

  rw [htail, htheta]
  exact fourier_tail_bound I (logPullback b) k T hT

end MellinJackson
end TS17
