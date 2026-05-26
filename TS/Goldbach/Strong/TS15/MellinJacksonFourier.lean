import Mathlib.Data.Real.Basic

namespace TS15
namespace MellinJackson

structure MellinFunction where
  dummy : Unit := ()

noncomputable def mellinNorm (_b : MellinFunction) : Real :=
  0

noncomputable def mellinTailNorm (_T : Real) (_b : MellinFunction) : Real :=
  0

noncomputable def thetaIter (_k : Nat) (b : MellinFunction) : MellinFunction :=
  b

/--
TS15 Mellin-Jackson bound:

  ||b - b_T||_M <= ||Theta^k b||_M / T^k.
-/
structure MellinJacksonProjectionBound where
  bound :
    forall (b : MellinFunction) (k : Nat) (T : Real),
      0 < T ->
      mellinTailNorm T b <=
        mellinNorm (thetaIter k b) / (T ^ k)

end MellinJackson
end TS15
