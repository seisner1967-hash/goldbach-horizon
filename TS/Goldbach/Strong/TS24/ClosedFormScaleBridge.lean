import Mathlib.Tactic
import TS.Goldbach.Strong.TS22.BrunTitchmarshIntervalBridge
import TS.Goldbach.Strong.TS22.ClosedFormScales

namespace TS24
namespace Goldbach

/--
The real kernel underlying the integer ceiling budget from TS22.

It is separated out so that the only rounding loss is the standard
`ceil a <= a + 1` estimate.
-/
noncomputable def brunTitchmarshCeilKernel (x Q : Nat) : Real :=
  ((4 : Real) * (TS15.Goldbach.intervalScale x Q : Real)) /
    Real.log ((Q : Real) + 1)

theorem brunTitchmarshCeilKernel_nonneg (x Q : Nat) :
    0 <= brunTitchmarshCeilKernel x Q := by
  unfold brunTitchmarshCeilKernel
  have hnum :
      0 <= (4 : Real) * (TS15.Goldbach.intervalScale x Q : Real) := by
    exact mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _)
  have hQ : (1 : Real) <= (Q : Real) + 1 := by
    have hQ0 : (0 : Real) <= (Q : Real) := by exact_mod_cast Nat.zero_le Q
    linarith
  have hden : 0 <= Real.log ((Q : Real) + 1) :=
    Real.log_nonneg hQ
  exact div_nonneg hnum hden

/-- The TS22 ceiling budget is bounded by its real kernel plus one. -/
theorem brunTitchmarshCeilBudget_le_kernel_add_one (x Q : Nat) :
    (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Real) <=
      brunTitchmarshCeilKernel x Q + 1 := by
  unfold TS22.Goldbach.brunTitchmarshCeilBudget
  change
    ((Nat.ceil (brunTitchmarshCeilKernel x Q) : Nat) : Real) <=
      brunTitchmarshCeilKernel x Q + 1
  exact (Nat.ceil_lt_add_one (brunTitchmarshCeilKernel_nonneg x Q)).le

/--
Closed-form scale with the unavoidable `+1` ceiling cushion.

This is the scale that can be proved to dominate the exact integer
ceiling-budget scale without any analytic input beyond the local
Brun-Titchmarsh interval theorem itself.
-/
noncomputable def brunTitchmarshPaddedClosedFormScaleValue
    (x Q : Nat) : Real :=
  ((x + 1 : Nat) : Real) *
    (brunTitchmarshCeilKernel x Q + 1) ^ 2

theorem brunTitchmarshPaddedClosedFormScaleValue_nonneg
    (x Q : Nat) :
    0 <= brunTitchmarshPaddedClosedFormScaleValue x Q := by
  unfold brunTitchmarshPaddedClosedFormScaleValue
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (x + 1)) (sq_nonneg _)

/--
The padded closed-form Brun-Titchmarsh normalization as a `ShortIntervalScale`.
-/
noncomputable def brunTitchmarshPaddedClosedFormScale :
    TS22.Goldbach.ShortIntervalScale where
  scale := brunTitchmarshPaddedClosedFormScaleValue
  scale_nonneg := brunTitchmarshPaddedClosedFormScaleValue_nonneg

/--
The exact TS22 ceiling-budget scale is dominated by the padded closed-form
scale.
-/
theorem localWindowBudgetScale_le_paddedClosedFormScale
    (BT : TS22.Goldbach.BrunTitchmarshNatIntervalBound) :
    TS22.Goldbach.BrunTitchmarshScaleBridge
      (TS22.Goldbach.localWindowBudgetOfNatIntervalBound BT)
      brunTitchmarshPaddedClosedFormScale := by
  refine ⟨?_⟩
  intro x Q
  simp only
    [TS22.Goldbach.localWindowBudgetScale,
     TS22.Goldbach.localWindowBudgetOfNatIntervalBound,
     TS21.Goldbach.localCountEnergyScale,
     brunTitchmarshPaddedClosedFormScale,
     brunTitchmarshPaddedClosedFormScaleValue]
  have hceil :
      (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Real) <=
        brunTitchmarshCeilKernel x Q + 1 :=
    brunTitchmarshCeilBudget_le_kernel_add_one x Q
  have hceil_nonneg :
      0 <= (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Real) := by
    exact_mod_cast Nat.zero_le (TS22.Goldbach.brunTitchmarshCeilBudget x Q)
  have hkernel_nonneg :
      0 <= brunTitchmarshCeilKernel x Q + 1 := by
    have h := brunTitchmarshCeilKernel_nonneg x Q
    linarith
  have hsquare :
      (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Real) ^ 2 <=
        (brunTitchmarshCeilKernel x Q + 1) ^ 2 := by
    nlinarith
  have hmul :
      ((x + 1 : Nat) : Real) *
          (TS22.Goldbach.brunTitchmarshCeilBudget x Q : Real) ^ 2 <=
        ((x + 1 : Nat) : Real) *
          (brunTitchmarshCeilKernel x Q + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left
      hsquare
      (by exact_mod_cast Nat.zero_le (x + 1))
  simpa [Nat.cast_mul, Nat.cast_pow] using hmul

/--
An interval-count Brun-Titchmarsh theorem yields the scaled pair-count target
at the padded closed-form scale.
-/
theorem Problem_E1Scale_from_natIntervalBound_paddedClosedForm
    (BT : TS22.Goldbach.BrunTitchmarshNatIntervalBound) :
    TS22.Goldbach.Problem_E1Scale
      brunTitchmarshPaddedClosedFormScale
      1 :=
  TS22.Goldbach.Problem_E1Scale_from_localWindowBudget_bridge
    (TS22.Goldbach.localWindowBudgetOfNatIntervalBound BT)
    brunTitchmarshPaddedClosedFormScale
    (localWindowBudgetScale_le_paddedClosedFormScale BT)

end Goldbach
end TS24
