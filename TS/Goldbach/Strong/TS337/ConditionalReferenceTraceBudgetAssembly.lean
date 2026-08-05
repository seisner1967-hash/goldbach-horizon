import Mathlib.Tactic
import TS.Goldbach.Strong.TS93.ZetaZeroFamilyLedger
import TS.Goldbach.Strong.TS322.FiniteCoreEffectiveTail
import TS.Goldbach.Strong.TS330.ConditionalTraceBudgetAssembly
import TS.Goldbach.Strong.TS333.AbstractShiftedSpectralMassAssembly
import TS.Goldbach.Strong.TS334.RationalTruncationTailProvider
import TS.Goldbach.Strong.TS335.RationalExceptionalResidueProvider
import TS.Goldbach.Strong.TS336.RationalFixedLeftBoundaryProvider

namespace TS337
namespace Goldbach

noncomputable section

/-!
# TS337: conditional reference trace-budget assembly

This module instantiates the rational shell of the TS330 trace-budget template
at the reference height and dyadic scale.  The finite linear and quadratic
coefficient caps remain explicit premises, and the zero-family ledger is
supplied by the caller.  No finite-core proof, zero payload, completion of the
full certificate, downstream adapter, or arithmetic consequence is constructed
here.
-/

/-! ## Reference parameters -/

def referenceHeight : Nat := 1132490

def referenceTruncationHeight : Nat := 1132490

def referenceDyadicScale : Nat := 4529960

def referenceCore : Rat := 1 / 7500

def referenceFiniteLinearCap : Rat := 1 / 20

def referenceFiniteQuadraticCap : Rat := 1 / 10000

def referenceResidualTailCap : Rat := 31140 / 2151731

def referenceQMoment : Rat := 11 / 25

def referenceTraceBudget : Rat := 1 / 2

/-! ## Closed rational majorants -/

def referenceTailMajorant : Rat :=
  2 * (referenceFiniteLinearCap + referenceResidualTailCap) *
    referenceResidualTailCap

def referenceDiagonalMajorant : Rat :=
  4 * (referenceFiniteQuadraticCap + referenceResidualTailCap ^ 2)

def referenceTruncationTailMajorant : Rat :=
  124560 / 2151731

def referenceExceptionalMajorant : Rat :=
  (2 / (referenceDyadicScale : Rat)) *
    (3 + 9 / (referenceDyadicScale : Rat))

def referenceLeftMajorant : Rat :=
  2880 / ((referenceDyadicScale : Rat) ^ 2)

/-! ## Exact arithmetic margins -/

theorem referenceSpectralMargin_eq :
    (referenceQMoment : Real) ^ 2 -
        ((referenceDiagonalMajorant : Real) +
          96 * ((referenceCore : Real) + (referenceTailMajorant : Real))) =
      (((4835295498811 : Rat) / 11574865740902500 : Rat) : Real) := by
  norm_num [referenceQMoment, referenceDiagonalMajorant,
    referenceFiniteQuadraticCap, referenceResidualTailCap, referenceCore,
    referenceTailMajorant, referenceFiniteLinearCap]

theorem referenceSpectralMargin_pos :
    0 <
      (referenceQMoment : Real) ^ 2 -
        ((referenceDiagonalMajorant : Real) +
          96 * ((referenceCore : Real) + (referenceTailMajorant : Real))) := by
  rw [referenceSpectralMargin_eq]
  norm_num

theorem referenceTotalBudgetMargin_eq :
    (referenceTraceBudget : Real) -
        ((referenceQMoment : Real) +
          (referenceTruncationTailMajorant : Real) +
          (referenceExceptionalMajorant : Real) +
          (referenceLeftMajorant : Real)) =
      (((411411845661 : Rat) / 194945107215200 : Rat) : Real) := by
  norm_num [referenceTraceBudget, referenceQMoment,
    referenceTruncationTailMajorant, referenceExceptionalMajorant,
    referenceLeftMajorant, referenceDyadicScale]

theorem referenceTotalBudgetMargin_pos :
    0 <
      (referenceTraceBudget : Real) -
        ((referenceQMoment : Real) +
          (referenceTruncationTailMajorant : Real) +
          (referenceExceptionalMajorant : Real) +
          (referenceLeftMajorant : Real)) := by
  rw [referenceTotalBudgetMargin_eq]
  norm_num

/-! ## Normalized dyadic providers -/

private theorem canonicalTraceNormalizationFactor_le_reference
    (x : Nat)
    (hxWindow :
      Membership.mem
        (TS314.Goldbach.dyadicWindow referenceDyadicScale) x) :
    TS313.Goldbach.canonicalTraceNormalizationFactor x <=
      2 / (referenceDyadicScale : Real) := by
  have hxLower : referenceDyadicScale <= x :=
    (TS314.Goldbach.mem_dyadicWindow_iff.mp hxWindow).1
  have hScalePos : 0 < (referenceDyadicScale : Real) := by
    norm_num [referenceDyadicScale]
  have hxLowerReal : (referenceDyadicScale : Real) <= (x : Real) := by
    exact_mod_cast hxLower
  have hInv : (1 : Real) / (x : Real) <=
      1 / (referenceDyadicScale : Real) :=
    one_div_le_one_div_of_le hScalePos hxLowerReal
  unfold TS313.Goldbach.canonicalTraceNormalizationFactor
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 2)

private theorem fixedLeftUniformBound_le_1440_div
    (x : Nat)
    (hx : 1 <= x) :
    TS305.Goldbach.fixedLeftUniformBound
        x TS307.Goldbach.fixedLeftLogDerivativeBoundData <=
      1440 / (x : Real) := by
  calc
    TS305.Goldbach.fixedLeftUniformBound
          x TS307.Goldbach.fixedLeftLogDerivativeBoundData <=
        1440 * TS305.Goldbach.fixedLeftScale x := by
      unfold TS305.Goldbach.fixedLeftUniformBound
      have hScale := TS305.Goldbach.fixedLeftScale_nonnegative x
      have hMass := TS305.Goldbach.fixedLeftLogKernelMass_nonnegative
      have hConstant :=
        TS307.Goldbach.fixedLeftLogDerivativeBoundData.constant_nonnegative
      calc
        2 * TS307.Goldbach.fixedLeftLogDerivativeBoundData.constant *
              TS305.Goldbach.fixedLeftScale x *
            TS305.Goldbach.fixedLeftLogKernelMass <=
            2 * 18 * TS305.Goldbach.fixedLeftScale x * 40 := by
          gcongr
          · exact TS336.Goldbach.fixedLeftLogDerivativeConstant_le_eighteen
          · exact TS336.Goldbach.fixedLeftLogKernelMass_le_forty
        _ = 1440 * TS305.Goldbach.fixedLeftScale x := by ring
    _ <= 1440 * (1 / (x : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (TS336.Goldbach.fixedLeftScale_le_inv x hx) (by norm_num)
    _ = 1440 / (x : Real) := by ring

private theorem normalizedExceptionalContribution_le_reference
    (x : Nat)
    (hxWindow :
      Membership.mem
        (TS314.Goldbach.dyadicWindow referenceDyadicScale) x) :
    TS313.Goldbach.canonicalTraceNormalizationFactor x *
        TS306.Goldbach.concreteExceptionalResidueBound x <=
      (referenceExceptionalMajorant : Real) := by
  have hScalePos : 0 < referenceDyadicScale := by
    norm_num [referenceDyadicScale]
  have hFactor := canonicalTraceNormalizationFactor_le_reference x hxWindow
  have hResidue :=
    TS335.Goldbach.concreteExceptionalResidueBound_le_three_add_nine_div_on_dyadicWindow
      referenceDyadicScale x hScalePos hxWindow
  calc
    TS313.Goldbach.canonicalTraceNormalizationFactor x *
          TS306.Goldbach.concreteExceptionalResidueBound x <=
        (2 / (referenceDyadicScale : Real)) *
          (3 + 9 / (referenceDyadicScale : Real)) := by
      exact mul_le_mul hFactor hResidue
        (TS306.Goldbach.concreteExceptionalResidueBound_nonnegative x)
        (by positivity)
    _ = (referenceExceptionalMajorant : Real) := by
      norm_num [referenceExceptionalMajorant, referenceDyadicScale]

private theorem normalizedFixedLeftContribution_le_reference
    (x : Nat)
    (hxWindow :
      Membership.mem
        (TS314.Goldbach.dyadicWindow referenceDyadicScale) x) :
    TS313.Goldbach.canonicalTraceNormalizationFactor x *
        (TS305.Goldbach.fixedLeftUniformBound
            x TS307.Goldbach.fixedLeftLogDerivativeBoundData /
          (2 * Real.pi)) <=
      (referenceLeftMajorant : Real) := by
  have hScalePos : 0 < referenceDyadicScale := by
    norm_num [referenceDyadicScale]
  have hxOne := TS314.Goldbach.one_le_of_mem_dyadicWindow hScalePos hxWindow
  have hxLower : referenceDyadicScale <= x :=
    (TS314.Goldbach.mem_dyadicWindow_iff.mp hxWindow).1
  have hxLowerReal : (referenceDyadicScale : Real) <= (x : Real) := by
    exact_mod_cast hxLower
  have hScaleRealPos : 0 < (referenceDyadicScale : Real) := by
    exact_mod_cast hScalePos
  have hInv : (1 : Real) / (x : Real) <=
      1 / (referenceDyadicScale : Real) :=
    one_div_le_one_div_of_le hScaleRealPos hxLowerReal
  have hUniformNonnegative :=
    TS305.Goldbach.fixedLeftUniformBound_nonnegative
      x TS307.Goldbach.fixedLeftLogDerivativeBoundData
  have hDivNonnegative :
      0 <=
        TS305.Goldbach.fixedLeftUniformBound
            x TS307.Goldbach.fixedLeftLogDerivativeBoundData /
          (2 * Real.pi) := by
    positivity
  have hPi : (1 : Real) <= 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hDiv :
      TS305.Goldbach.fixedLeftUniformBound
            x TS307.Goldbach.fixedLeftLogDerivativeBoundData /
          (2 * Real.pi) <=
        1440 / (referenceDyadicScale : Real) := by
    calc
      TS305.Goldbach.fixedLeftUniformBound
              x TS307.Goldbach.fixedLeftLogDerivativeBoundData /
            (2 * Real.pi) <=
          TS305.Goldbach.fixedLeftUniformBound
            x TS307.Goldbach.fixedLeftLogDerivativeBoundData :=
        div_le_self hUniformNonnegative hPi
      _ <= 1440 / (x : Real) := fixedLeftUniformBound_le_1440_div x hxOne
      _ <= 1440 / (referenceDyadicScale : Real) := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 1440)
  have hFactor := canonicalTraceNormalizationFactor_le_reference x hxWindow
  calc
    TS313.Goldbach.canonicalTraceNormalizationFactor x *
          (TS305.Goldbach.fixedLeftUniformBound
              x TS307.Goldbach.fixedLeftLogDerivativeBoundData /
            (2 * Real.pi)) <=
        (2 / (referenceDyadicScale : Real)) *
          (1440 / (referenceDyadicScale : Real)) := by
      exact mul_le_mul hFactor hDiv hDivNonnegative (by positivity)
    _ = (referenceLeftMajorant : Real) := by
      norm_num [referenceLeftMajorant, referenceDyadicScale]

/-! ## Conditional reference template -/

/--
The TS330 reference template, conditional on the two finite spectral caps and
on an externally supplied zero-family ledger.  This definition deliberately
stops at the template boundary.
-/
noncomputable def referenceTraceBudgetTemplate
    (zeroFamily : TS93.Goldbach.ZetaZeroFamilyLedger)
    (hL :
      TS322.Goldbach.finiteLinearCoefficientMass 1132490 <=
        (((1 : Rat) / 20 : Rat) : Real))
    (hQ :
      TS333.Goldbach.finiteQuadraticCoefficientMass 1132490 <=
        (((1 : Rat) / 10000 : Rat) : Real)) :
    TS330.Goldbach.RationalTraceBudgetTemplate
      1132490 ((1 : Rat) / 7500) where
  truncationHeight := referenceTruncationHeight
  dyadicScale := referenceDyadicScale
  core_le_height := by norm_num [referenceTruncationHeight]
  height_pos := by norm_num [referenceTruncationHeight]
  scale_pos := by norm_num [referenceDyadicScale]
  height_scale_compatible := by
    norm_num [referenceTruncationHeight, referenceDyadicScale]
  tailMajorant := referenceTailMajorant
  diagonalMajorant := referenceDiagonalMajorant
  qMoment := referenceQMoment
  truncationTailMajorant := referenceTruncationTailMajorant
  exceptionalMajorant := referenceExceptionalMajorant
  leftMajorant := referenceLeftMajorant
  traceBudget := referenceTraceBudget
  coreMajorant_nonnegative := by norm_num
  tailMajorant_nonnegative := by
    norm_num [referenceTailMajorant, referenceFiniteLinearCap,
      referenceResidualTailCap]
  diagonalMajorant_nonnegative := by
    norm_num [referenceDiagonalMajorant, referenceFiniteQuadraticCap,
      referenceResidualTailCap]
  qMoment_nonnegative := by norm_num [referenceQMoment]
  truncationTailMajorant_nonnegative := by
    norm_num [referenceTruncationTailMajorant]
  exceptionalMajorant_nonnegative := by
    norm_num [referenceExceptionalMajorant, referenceDyadicScale]
  leftMajorant_nonnegative := by
    norm_num [referenceLeftMajorant, referenceDyadicScale]
  tail_bound := by
    simpa [referenceTailMajorant, referenceFiniteLinearCap,
      referenceResidualTailCap] using
      TS333.Goldbach.effectiveWeightedTailError_referenceHeight_le_of_rationalFiniteCap
        hL
  diagonal_bound := by
    simpa [referenceDiagonalMajorant, referenceFiniteQuadraticCap,
      referenceResidualTailCap] using
      TS333.Goldbach.diagonalSpectralMass_referenceHeight_le_of_rationalFiniteCap
        hQ
  moment_allocation := by
    have hMargin := referenceSpectralMargin_pos
    change
      (referenceDiagonalMajorant : Real) +
          96 * ((((1 : Rat) / 7500 : Rat) : Real) +
            (referenceTailMajorant : Real)) <=
        (referenceQMoment : Real) ^ 2
    simpa [referenceCore] using le_of_lt (sub_pos.mp hMargin)
  truncation_tail_bound := by
    simpa [referenceTruncationHeight, referenceTruncationTailMajorant,
      TS334.Goldbach.referenceTruncationTailMajorant] using
      TS334.Goldbach.normalizedSpectralTailEnvelope_referenceHeight_le
  zeroFamily := zeroFamily
  exceptional_window_bound := by
    intro x hxWindow
    exact normalizedExceptionalContribution_le_reference x hxWindow
  left_window_bound := by
    intro x hxWindow
    exact normalizedFixedLeftContribution_le_reference x hxWindow
  traceBudget_pos := by norm_num [referenceTraceBudget]
  traceBudget_le_half := by norm_num [referenceTraceBudget]
  components_le_budget := by
    norm_num [referenceQMoment, referenceTruncationTailMajorant,
      referenceExceptionalMajorant, referenceLeftMajorant,
      referenceTraceBudget, referenceDyadicScale]

end

end Goldbach
end TS337
