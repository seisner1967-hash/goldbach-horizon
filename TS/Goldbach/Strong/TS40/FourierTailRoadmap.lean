import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
import TS.Goldbach.Strong.TS39.MellinFourierLpIsometry

namespace TS40
namespace MellinJackson

open MeasureTheory
open scoped ENNReal

/-!
# TS40 - Fourier Tail Roadmap

This sprint records the Fourier-tail infrastructure needed by the TS17
Mellin-Jackson layer.

It is a roadmap-level contract. It does not prove Plancherel, the Fourier
derivative rule, Sobolev decay, or the final high-frequency estimate. Those
remain explicit local analytic obligations.
-/

/--
Fourier-tail analytic infrastructure.

The Fourier transform and Sobolev derivative are kept abstract so that the
future concrete sprint can first inspect Mathlib's Fourier normalization and
its `2π` conventions.
-/
structure FourierTailInfrastructure where
  /-- Abstract Fourier transform on representatives. -/
  fourierTransform :
    (Real -> Complex) -> (Real -> Complex)

  /-- Abstract `k`-th derivative/Sobolev representative. -/
  sobolevDerivative :
    Nat -> (Real -> Complex) -> (Real -> Complex)

  /--
  Plancherel-type `snorm` control for the chosen Fourier transform.

  The exact normalization is deferred to the concrete Mathlib Fourier API
  sprint.
  -/
  plancherel_snorm :
    forall (F : Real -> Complex),
      snorm (fourierTransform F) 2 (volume : Measure Real) =
        snorm F 2 (volume : Measure Real)

  /--
  Roadmap-level Fourier derivative control.

  A future concrete version should replace this marker with the precise
  multiplier statement, including the sign and any `2π` constants required by
  Mathlib's Fourier convention.
  -/
  fourier_derivative_control :
    forall (F : Real -> Complex) (k : Nat), True

  /--
  High-frequency tail bound.

  The Fourier mass outside `[-T, T]` is controlled by a Sobolev norm divided by
  a power of `T`.
  -/
  high_frequency_tail_bound :
    forall (F : Real -> Complex) (T : Real) (k : Nat),
      0 < T ->
        snorm
          (fun xi : Real =>
            if T < |xi| then fourierTransform F xi else 0)
          2
          (volume : Measure Real)
        <=
        ENNReal.ofReal (1 / T ^ k) *
          snorm (sobolevDerivative k F) 2 (volume : Measure Real)

/-- Roadmap target for the Fourier-tail side of TS17. -/
def FourierTailTarget : Prop :=
  Nonempty FourierTailInfrastructure

/-- Any supplied infrastructure trivially discharges the roadmap target. -/
theorem FourierTailTarget.of_infrastructure
    (H : FourierTailInfrastructure) :
    FourierTailTarget :=
  ⟨H⟩

end MellinJackson
end TS40
