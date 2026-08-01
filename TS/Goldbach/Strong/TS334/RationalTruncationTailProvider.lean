import Mathlib.Tactic
import TS.Goldbach.Strong.TS314.FiniteQuadraticSpectralMomentGoodScale
import TS.Goldbach.Strong.TS332.ShiftedInfiniteZeroTailProvider

namespace TS334
namespace Goldbach

noncomputable section

/-!
# TS334: rational truncation-tail provider

This module packages rational outer bounds for the explicit TS314 normalized
spectral tail envelope.  It uses only the public TS314 formula and certified
rational bounds on its two analytic factors.  No zero data or downstream
trace-budget assembly is introduced.
-/

/-! ## Abstract rational provider -/

/-- A rational upper bound for the normalized TS314 truncation tail. -/
structure RationalTruncationTailBound (T : Nat) where
  majorant : Rat
  majorant_nonnegative : 0 <= majorant
  envelope_le :
    TS314.Goldbach.normalizedSpectralTailEnvelope T <= (majorant : Real)

/-- A rational logarithm bound yields a rational bound for the TS292
logarithmic tail rate. -/
theorem logarithmicTailRate_le_of_rationalLogBound
    (T : Nat)
    (hT : 1 <= T)
    (logBound : Rat)
    (hLog : Real.log ((T : Real) + 2) <= (logBound : Real)) :
    TS292.Goldbach.logarithmicTailRate T <=
      (((logBound + 1) / (T : Rat) : Rat) : Real) := by
  have hTNonnegative : (0 : Real) <= (T : Real) := by positivity
  unfold TS292.Goldbach.logarithmicTailRate
  calc
    (Real.log ((T : Real) + 2) + 1) / (T : Real) <=
        ((logBound : Real) + 1) / (T : Real) :=
      div_le_div_of_nonneg_right (by linarith) hTNonnegative
    _ = (((logBound + 1) / (T : Rat) : Rat) : Real) := by
      norm_cast

/-- Rational bounds for the two factors in the public TS314 formula combine
to a rational bound for the normalized envelope. -/
theorem normalizedSpectralTailEnvelope_le_of_rationalBounds
    (T : Nat)
    (constantBound rateBound : Rat)
    (hConstant :
      TS292.Goldbach.infiniteZeroResidualTailConstant <=
        (constantBound : Real))
    (hRate :
      TS292.Goldbach.logarithmicTailRate T <= (rateBound : Real)) :
    TS314.Goldbach.normalizedSpectralTailEnvelope T <=
      ((2 * constantBound * rateBound : Rat) : Real) := by
  have hConstantNonnegative :=
    TS292.Goldbach.infiniteZeroResidualTailConstant_nonnegative
  have hRateNonnegative :
      0 <= TS292.Goldbach.logarithmicTailRate T := by
    unfold TS292.Goldbach.logarithmicTailRate
    exact div_nonneg
      (add_nonneg
        (Real.log_nonneg (by
          have hTNonnegative : (0 : Real) <= (T : Real) := by positivity
          linarith))
        (by norm_num))
      (by positivity)
  have hConstantBoundNonnegative : 0 <= (constantBound : Real) :=
    hConstantNonnegative.trans hConstant
  have hProduct :
      TS292.Goldbach.infiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate T <=
        (constantBound : Real) * (rateBound : Real) :=
    mul_le_mul hConstant hRate hRateNonnegative hConstantBoundNonnegative
  unfold TS314.Goldbach.normalizedSpectralTailEnvelope
  calc
    2 * TS292.Goldbach.infiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate T =
        2 * (TS292.Goldbach.infiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate T) := by ring
    _ <= 2 * ((constantBound : Real) * (rateBound : Real)) :=
      mul_le_mul_of_nonneg_left hProduct (by norm_num)
    _ = ((2 * constantBound * rateBound : Rat) : Real) := by
      norm_cast
      ring

/-- Constructor for a reusable rational truncation-tail certificate. -/
noncomputable def RationalTruncationTailBound.ofRationalBounds
    (T : Nat)
    (constantBound rateBound : Rat)
    (hConstantBoundNonnegative : 0 <= constantBound)
    (hRateBoundNonnegative : 0 <= rateBound)
    (hConstant :
      TS292.Goldbach.infiniteZeroResidualTailConstant <=
        (constantBound : Real))
    (hRate :
      TS292.Goldbach.logarithmicTailRate T <= (rateBound : Real)) :
    RationalTruncationTailBound T where
  majorant := 2 * constantBound * rateBound
  majorant_nonnegative :=
    mul_nonneg
      (mul_nonneg (by norm_num) hConstantBoundNonnegative)
      hRateBoundNonnegative
  envelope_le := normalizedSpectralTailEnvelope_le_of_rationalBounds
    T constantBound rateBound hConstant hRate

/-! ## Certified factors at the reference height -/

/-- Rational outer bound for the historical TS292 residual constant used by
the public TS314 envelope. -/
theorem infiniteZeroResidualTailConstant_le_forty_one_five_twenty_div_nineteen :
    TS292.Goldbach.infiniteZeroResidualTailConstant <=
      (((41520 : Rat) / 19 : Rat) : Real) := by
  unfold TS292.Goldbach.infiniteZeroResidualTailConstant
    TS290.Goldbach.xiGlobalLogLinearConstant
  have hDyadic :=
    TS332.Goldbach.xiDyadicLogLinearConstant_le_six_ninety_two_div_nineteen
  norm_cast at hDyadic
  norm_cast
  nlinarith

/-- Exact rational rate bound at `T = 1132490`. -/
theorem logarithmicTailRate_referenceHeight_le :
    TS292.Goldbach.logarithmicTailRate 1132490 <=
      (((15 : Rat) / 1132490 : Rat) : Real) := by
  have hLog :
      Real.log ((1132490 : Real) + 2) <= ((14 : Rat) : Real) := by
    norm_num only [Rat.cast_ofNat]
    exact le_of_lt TS332.Goldbach.log_height_plus_two_lt_fourteen
  calc
    TS292.Goldbach.logarithmicTailRate 1132490 <=
        ((((14 : Rat) + 1) / 1132490 : Rat) : Real) :=
      logarithmicTailRate_le_of_rationalLogBound
        1132490 (by norm_num) 14 hLog
    _ = (((15 : Rat) / 1132490 : Rat) : Real) := by norm_num

/-! ## Exact reference-height specialization -/

/-- Compact rational truncation-tail majorant at the reference height. -/
def referenceTruncationTailMajorant : Rat :=
  124560 / 2151731

theorem referenceTruncationTailMajorant_nonnegative :
    0 <= referenceTruncationTailMajorant := by
  norm_num [referenceTruncationTailMajorant]

/-- The public TS314 normalized tail at `T = 1132490` is bounded by the
compact rational provider. -/
theorem normalizedSpectralTailEnvelope_referenceHeight_le :
    TS314.Goldbach.normalizedSpectralTailEnvelope 1132490 <=
      (referenceTruncationTailMajorant : Real) := by
  calc
    TS314.Goldbach.normalizedSpectralTailEnvelope 1132490 <=
        ((2 * ((41520 : Rat) / 19) *
          ((15 : Rat) / 1132490) : Rat) : Real) :=
      normalizedSpectralTailEnvelope_le_of_rationalBounds
        1132490 ((41520 : Rat) / 19) ((15 : Rat) / 1132490)
        infiniteZeroResidualTailConstant_le_forty_one_five_twenty_div_nineteen
        logarithmicTailRate_referenceHeight_le
    _ = (referenceTruncationTailMajorant : Real) := by
      norm_num [referenceTruncationTailMajorant]

/-- Reusable packaged provider at the reference height. -/
noncomputable def referenceTruncationTailBound :
    RationalTruncationTailBound 1132490 where
  majorant := referenceTruncationTailMajorant
  majorant_nonnegative := referenceTruncationTailMajorant_nonnegative
  envelope_le := normalizedSpectralTailEnvelope_referenceHeight_le

end

end Goldbach
end TS334
