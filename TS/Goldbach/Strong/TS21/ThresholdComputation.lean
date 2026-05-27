import Mathlib.Tactic
import TS.Goldbach.Strong.TS21.BrunTitchmarshShortInterval

namespace TS21
namespace Goldbach

/--
Default TS21 admissible constant for the short-interval budget.

In a later threshold file this value is the one to compare against the
asymptotic cutoff computation. TS21 keeps it explicit and transportable.
-/
noncomputable def KAllowedTS21 : Real :=
  20

theorem KAllowedTS21_pos :
    0 < KAllowedTS21 := by
  norm_num [KAllowedTS21]

theorem BTShortIntervalConstant_le_KAllowedTS21 :
    BTShortIntervalConstant <= KAllowedTS21 := by
  norm_num [BTShortIntervalConstant, KAllowedTS21]

/--
The Brun-Titchmarsh constant is admissible for the default TS21 budget.
-/
theorem Problem_E1K_allowed_from_BrunTitchmarsh
    (BT : BrunTitchmarshShortInterval) :
    Problem_E1K KAllowedTS21 :=
  Problem_E1K_mono
    BTShortIntervalConstant_le_KAllowedTS21
    (Problem_E1K_from_BrunTitchmarsh BT)

end Goldbach
end TS21
