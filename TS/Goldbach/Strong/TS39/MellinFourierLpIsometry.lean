import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS36.MellinFourierLpIsometryRoadmap

namespace TS39
namespace MellinJackson

open MeasureTheory Filter

/-!
# TS39 - Mellin-Fourier Lp Isometry

This sprint defines the final mathematical specification for the
Mellin-Fourier `L²` isometry.

It does not construct the `LinearIsometryEquiv`. Instead, it records the exact
target: an isometric linear equivalence whose forward and inverse maps agree
almost everywhere with the pointwise representative operators from TS17.
-/

/--
Final specification of the Mellin-Fourier `L²` isometry.

The a.e. behaviour fields are part of the contract. They prevent an unrelated
abstract isometry between the same Banach spaces from satisfying the
Mellin-Fourier bridge obligation.
-/
structure MellinFourierLpIsometry (sigma : Real) where
  /-- The Banach/Hilbert-space isometric linear equivalence. -/
  iso :
    Lp Complex 2 (TS17.MellinJackson.muWeighted sigma) ≃ₗᵢ[Complex]
      Lp Complex 2 (volume : Measure Real)

  /-- The forward map agrees a.e. with the pointwise logarithmic transport. -/
  iso_apply_ae :
    forall (W : Lp Complex 2 (TS17.MellinJackson.muWeighted sigma)),
      ((iso W : Lp Complex 2 (volume : Measure Real)) : Real -> Complex)
        =ᵐ[(volume : Measure Real)]
          TS17.MellinJackson.TsigmaFun sigma
            (((W : Lp Complex 2 (TS17.MellinJackson.muWeighted sigma)) :
              Real -> Complex))

  /-- The inverse map agrees a.e. with the pointwise inverse transport. -/
  iso_symm_apply_ae :
    forall (V : Lp Complex 2 (volume : Measure Real)),
      ((iso.symm V :
          Lp Complex 2 (TS17.MellinJackson.muWeighted sigma)) :
            Real -> Complex)
        =ᵐ[TS17.MellinJackson.muWeighted sigma]
          TS17.MellinJackson.TsigmaInvFun sigma
            (((V : Lp Complex 2 (volume : Measure Real)) : Real -> Complex))

/-- Final fixed-`sigma` target for the Mellin-Fourier norm bridge. -/
def MellinFourierLpIsometryTarget (sigma : Real) : Prop :=
  Nonempty (MellinFourierLpIsometry sigma)

/--
Any final isometry specification provides the weaker TS36 target: existence of
some `LinearIsometryEquiv` between the two `L²` spaces.
-/
theorem weakTarget_of_isometryTarget
    {sigma : Real}
    (H : MellinFourierLpIsometryTarget sigma) :
    TS36.MellinJackson.MellinFourierLpIsometryTarget sigma := by
  rcases H with ⟨Hiso⟩
  exact ⟨Hiso.iso⟩

end MellinJackson
end TS39
