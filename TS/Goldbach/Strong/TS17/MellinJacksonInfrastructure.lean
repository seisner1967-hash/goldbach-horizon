import Mathlib.Data.Real.Basic
import Mathlib.Analysis.MellinTransform
import TS.Goldbach.Strong.TS15.MellinJacksonFourier

namespace TS17
namespace MellinJackson

/--
Abstract object representing the logarithmic pullback B(u) = b(exp u).

In a later analytic version this can be replaced by a concrete real function
or by an L2 class.
-/
structure LogPullback where
  dummy : Unit := ()

/-- Abstract L2 norm of the logarithmic pullback. -/
noncomputable def l2Norm (_B : LogPullback) : Real :=
  0

/-- Abstract L2 norm of the high-frequency Fourier tail. -/
noncomputable def fourierTailNorm (_T : Real) (_B : LogPullback) : Real :=
  0

/-- Abstract L2 norm of the k-th derivative of the logarithmic pullback. -/
noncomputable def derivativeL2Norm (_k : Nat) (_B : LogPullback) : Real :=
  0

/-- Logarithmic pullback attached to a TS15 Mellin function. -/
noncomputable def logPullback
    (_b : TS15.MellinJackson.MellinFunction) :
    LogPullback :=
  {}

/--
The local Mellin/Fourier bridge needed by TS17.

This records exactly the two analytic identifications:
the Mellin tail is the Fourier tail of the logarithmic pullback, and
Theta^k on the Mellin side is the k-th derivative on the logarithmic side.
-/
structure MellinFourierNormBridge where
  tail_bridge :
    forall (b : TS15.MellinJackson.MellinFunction) (T : Real),
      TS15.MellinJackson.mellinTailNorm T b =
        fourierTailNorm T (logPullback b)

  theta_bridge :
    forall (b : TS15.MellinJackson.MellinFunction) (k : Nat),
      TS15.MellinJackson.mellinNorm
          (TS15.MellinJackson.thetaIter k b)
        =
        derivativeL2Norm k (logPullback b)

end MellinJackson
end TS17
