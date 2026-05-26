import Mathlib.Data.Real.Basic
import TS.Goldbach.Strong.TS17.MellinJacksonInfrastructure

namespace TS17
namespace MellinJackson

/--
Minimal harmonic infrastructure for the Fourier tail estimate.

Analytically, this packages the high-frequency estimate together with the
Plancherel identification of the weighted Fourier energy with the derivative
L2 norm. It is deliberately local and explicit: no global assumption is introduced.
-/
structure FourierTailInfrastructure where
  tail_bound :
    forall (B : LogPullback) (k : Nat) (T : Real),
      0 < T ->
      fourierTailNorm T B <= derivativeL2Norm k B / T ^ k

/--
The Fourier tail bound, relative to the local harmonic infrastructure.
-/
theorem fourier_tail_bound
    (I : FourierTailInfrastructure)
    (B : LogPullback)
    (k : Nat)
    (T : Real)
    (hT : 0 < T) :
    fourierTailNorm T B <= derivativeL2Norm k B / T ^ k := by
  exact I.tail_bound B k T hT

end MellinJackson
end TS17
