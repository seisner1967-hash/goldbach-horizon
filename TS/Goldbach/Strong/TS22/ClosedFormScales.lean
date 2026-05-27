import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import TS.Goldbach.Strong.TS22.EnergyScale

namespace TS22
namespace Goldbach

/--
Closed-form Brun-Titchmarsh scale suggested by the local estimate
`B ~ 4h / log Q`, with `h = intervalScale x Q`.

The denominator is kept as a real division, so no integer remainder bookkeeping
is introduced at the scale layer.
-/
noncomputable def brunTitchmarshClosedFormScaleValue (x Q : Nat) : Real :=
  ((x + 1 : Nat) : Real) *
    (((4 : Real) * (TS15.Goldbach.intervalScale x Q : Real)) /
      Real.log (Q : Real)) ^ 2

theorem brunTitchmarshClosedFormScaleValue_nonneg (x Q : Nat) :
    0 <= brunTitchmarshClosedFormScaleValue x Q := by
  unfold brunTitchmarshClosedFormScaleValue
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (x + 1)) (sq_nonneg _)

/--
The closed-form Brun-Titchmarsh normalization as a `ShortIntervalScale`.
-/
noncomputable def brunTitchmarshClosedFormScale : ShortIntervalScale where
  scale := brunTitchmarshClosedFormScaleValue
  scale_nonneg := brunTitchmarshClosedFormScaleValue_nonneg

end Goldbach
end TS22
