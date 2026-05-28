import Mathlib.Tactic
import TS.Goldbach.Strong.TS40.FourierTailRoadmap

namespace TS41
namespace MellinJackson

/-!
# TS41 - Fourier API Probe

This sprint records the normalization slots needed before the TS40
Fourier-tail roadmap is instantiated with concrete Mathlib Fourier objects.

It deliberately does not prove Plancherel, the Fourier derivative rule, or the
high-frequency tail estimate.
-/

/--
Fourier API normalization ledger.

The transform and Sobolev derivative remain abstract until a later sprint
checks Mathlib's concrete Fourier API and its normalization conventions. The
two positive constants reserve the places where Plancherel and derivative
multiplier normalizations will be recorded.
-/
structure FourierAPINormalizationLedger where
  /-- The Fourier transform selected from the Mathlib API. -/
  fourierTransform :
    (Real -> Complex) -> (Real -> Complex)

  /-- The chosen representative for the `k`-th Sobolev derivative. -/
  sobolevDerivative :
    Nat -> (Real -> Complex) -> (Real -> Complex)

  /--
  Positive normalization constant for the Plancherel side.

  A concrete future instance should set this according to Mathlib's Fourier
  convention.
  -/
  plancherelConstant :
    Real
  plancherelConstant_pos :
    0 < plancherelConstant

  /--
  Positive normalization constant for the derivative multiplier side.

  This absorbs the sign and any `2 * pi` factors appearing in the concrete
  Fourier derivative theorem.
  -/
  derivativeMultiplierConstant :
    Real
  derivativeMultiplierConstant_pos :
    0 < derivativeMultiplierConstant

/--
TS41 target: a Fourier API normalization package exists.

This is weaker than the TS40 Fourier-tail target; it only records the API and
normalization choices that a later concrete proof will use.
-/
def FourierAPINormalizationTarget : Prop :=
  Nonempty FourierAPINormalizationLedger

/-- Any supplied normalization ledger discharges the TS41 target. -/
theorem FourierAPINormalizationTarget.of_ledger
    (H : FourierAPINormalizationLedger) :
    FourierAPINormalizationTarget :=
  Nonempty.intro H

end MellinJackson
end TS41
