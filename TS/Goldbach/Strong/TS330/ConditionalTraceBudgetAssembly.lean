import Mathlib.Tactic
import TS.Goldbach.Strong.TS323.CertifiedRationalTraceBudget
import TS.Goldbach.Strong.TS328.ExecutableGroupedZeroPayload
import TS.Goldbach.Strong.TS329.PositiveCountSaturation

namespace TS330
namespace Goldbach

noncomputable section

/-!
# TS330: conditional trace-budget assembly

This module fills the exact finite-core field of the TS323 rational trace
certificate from the positive-count route established by TS329.  All remaining
rational and analytic budget fields stay explicit in a template.  No empirical
payload, positive count certificate, half-budget instance, TS181 consequence,
or Goldbach statement is inhabited here.
-/

/-! ## TS323 template without the finite-core proof -/

/--
All fields of `CertifiedRationalTraceBudgetData` except the core height, core
majorant, and proof of the core bound.  Those three values are fixed by the
parameters and supplied by TS328 during completion.
-/
structure RationalTraceBudgetTemplate (H : Nat) (core : Rat) where
  truncationHeight : Nat
  dyadicScale : Nat

  core_le_height : H <= truncationHeight
  height_pos : 1 <= truncationHeight
  scale_pos : 0 < dyadicScale
  height_scale_compatible : 4 * truncationHeight <= dyadicScale

  tailMajorant : Rat
  diagonalMajorant : Rat
  qMoment : Rat
  truncationTailMajorant : Rat
  exceptionalMajorant : Rat
  leftMajorant : Rat
  traceBudget : Rat

  coreMajorant_nonnegative : 0 <= core
  tailMajorant_nonnegative : 0 <= tailMajorant
  diagonalMajorant_nonnegative : 0 <= diagonalMajorant
  qMoment_nonnegative : 0 <= qMoment
  truncationTailMajorant_nonnegative : 0 <= truncationTailMajorant
  exceptionalMajorant_nonnegative : 0 <= exceptionalMajorant
  leftMajorant_nonnegative : 0 <= leftMajorant

  tail_bound :
    TS322.Goldbach.effectiveWeightedTailError H <=
      (tailMajorant : Real)
  diagonal_bound :
    4 * TS316.Goldbach.globalQuadraticSpectralMass <=
      (diagonalMajorant : Real)
  moment_allocation :
    (diagonalMajorant : Real) +
        96 * ((core : Real) + (tailMajorant : Real)) <=
      (qMoment : Real) ^ 2
  truncation_tail_bound :
    TS314.Goldbach.normalizedSpectralTailEnvelope truncationHeight <=
      (truncationTailMajorant : Real)

  zeroFamily : TS93.Goldbach.ZetaZeroFamilyLedger

  exceptional_window_bound :
    forall x,
      Membership.mem (TS314.Goldbach.dyadicWindow dyadicScale) x ->
        TS313.Goldbach.canonicalTraceNormalizationFactor x *
            TS306.Goldbach.concreteExceptionalResidueBound x <=
          (exceptionalMajorant : Real)
  left_window_bound :
    forall x,
      Membership.mem (TS314.Goldbach.dyadicWindow dyadicScale) x ->
        TS313.Goldbach.canonicalTraceNormalizationFactor x *
            (TS305.Goldbach.fixedLeftUniformBound x
                TS307.Goldbach.fixedLeftLogDerivativeBoundData /
              (2 * Real.pi)) <=
          (leftMajorant : Real)

  traceBudget_pos : 0 < traceBudget
  traceBudget_le_half : traceBudget <= 1 / 2
  components_le_budget :
    qMoment + truncationTailMajorant +
        exceptionalMajorant + leftMajorant <= traceBudget

namespace RationalTraceBudgetTemplate

/-- Complete the real TS323 certificate with the independently derived core bound. -/
def complete
    {H : Nat} {core : Rat}
    (T : RationalTraceBudgetTemplate H core)
    (hCore :
      TS322.Goldbach.finiteWeightedLocalCore H <= (core : Real)) :
    TS323.Goldbach.CertifiedRationalTraceBudgetData where
  coreHeight := H
  truncationHeight := T.truncationHeight
  dyadicScale := T.dyadicScale
  core_le_height := T.core_le_height
  height_pos := T.height_pos
  scale_pos := T.scale_pos
  height_scale_compatible := T.height_scale_compatible
  coreMajorant := core
  tailMajorant := T.tailMajorant
  diagonalMajorant := T.diagonalMajorant
  qMoment := T.qMoment
  truncationTailMajorant := T.truncationTailMajorant
  exceptionalMajorant := T.exceptionalMajorant
  leftMajorant := T.leftMajorant
  traceBudget := T.traceBudget
  coreMajorant_nonnegative := T.coreMajorant_nonnegative
  tailMajorant_nonnegative := T.tailMajorant_nonnegative
  diagonalMajorant_nonnegative := T.diagonalMajorant_nonnegative
  qMoment_nonnegative := T.qMoment_nonnegative
  truncationTailMajorant_nonnegative :=
    T.truncationTailMajorant_nonnegative
  exceptionalMajorant_nonnegative := T.exceptionalMajorant_nonnegative
  leftMajorant_nonnegative := T.leftMajorant_nonnegative
  core_bound := hCore
  tail_bound := T.tail_bound
  diagonal_bound := T.diagonal_bound
  moment_allocation := T.moment_allocation
  truncation_tail_bound := T.truncation_tail_bound
  zeroFamily := T.zeroFamily
  exceptional_window_bound := T.exceptional_window_bound
  left_window_bound := T.left_window_bound
  traceBudget_pos := T.traceBudget_pos
  traceBudget_le_half := T.traceBudget_le_half
  components_le_budget := T.components_le_budget

end RationalTraceBudgetTemplate

/-! ## Executable claim and semantic routing -/

/-- The TS325 claim for the symmetric payload and declared rational core bound. -/
def symmetricBudgetClaim
    (upper : TS324.Goldbach.ZeroCoverPayload) (core : Rat) :
    TS325.Goldbach.PayloadBudgetClaim where
  data := TS328.Goldbach.symmetricPayload upper
  declaredMajorant := core

/-- A successful grouped budget check contains the grouped structural check. -/
theorem groupedPayloadCheck_of_budgetCheck
    {claim : TS325.Goldbach.PayloadBudgetClaim}
    (hBudget : TS328.Goldbach.checkGroupedPayloadBudget claim = true) :
    TS328.Goldbach.checkGroupedPayload claim.data = true := by
  have hReflected :=
    (TS328.Goldbach.checkGroupedPayloadBudget_iff claim).mp hBudget
  exact (TS328.Goldbach.checkGroupedPayload_iff claim.data).mpr
    (And.intro hReflected.1.1 hReflected.2)

/-! ## Conditional TS323 and TS181 assembly -/

/--
Positive count saturation plus the executable symmetric budget check fill the
only omitted field of the TS323 template.
-/
noncomputable def certifiedRationalTraceBudgetData_of_positive
    {H : Nat} {upper : TS324.Goldbach.ZeroCoverPayload} {core : Rat}
    (T : RationalTraceBudgetTemplate H core)
    (hNoZero : TS327.Goldbach.NoZeroOrdinateInTruncation H)
    (hPositive : TS329.Goldbach.PositiveImaginaryPayload upper)
    (P : TS329.Goldbach.CertifiedPositiveCountSaturation H upper)
    (hBudget : TS328.Goldbach.checkGroupedPayloadBudget
      (symmetricBudgetClaim upper core) = true) :
    TS323.Goldbach.CertifiedRationalTraceBudgetData := by
  have hGrouped :
      TS328.Goldbach.checkGroupedPayload
        (TS328.Goldbach.symmetricPayload upper) = true := by
    simpa [symmetricBudgetClaim] using
      groupedPayloadCheck_of_budgetCheck hBudget
  have hCover :
      TS324.Goldbach.CertifiedTruncatedZeroCover H
        (TS328.Goldbach.symmetricPayload upper) :=
    TS329.Goldbach.certifiedTruncatedZeroCover_of_positive
      hNoZero hPositive P hGrouped
  have hCore :
      TS322.Goldbach.finiteWeightedLocalCore H <= (core : Real) := by
    simpa [symmetricBudgetClaim] using
      TS328.Goldbach.finiteWeightedLocalCore_le_of_grouped_check
        hBudget hCover
  exact T.complete hCore

/-- Route the completed TS323 certificate through its existing TS181 adapter. -/
noncomputable def ts181TraceBudgetAdapterData_of_positive
    {H : Nat} {upper : TS324.Goldbach.ZeroCoverPayload} {core : Rat}
    (T : RationalTraceBudgetTemplate H core)
    (hNoZero : TS327.Goldbach.NoZeroOrdinateInTruncation H)
    (hPositive : TS329.Goldbach.PositiveImaginaryPayload upper)
    (P : TS329.Goldbach.CertifiedPositiveCountSaturation H upper)
    (hBudget : TS328.Goldbach.checkGroupedPayloadBudget
      (symmetricBudgetClaim upper core) = true) :
    TS312.Goldbach.TS181TraceBudgetAdapterData := by
  exact
    (certifiedRationalTraceBudgetData_of_positive
      T hNoZero hPositive P hBudget).toTS181TraceBudgetAdapterData

end

end Goldbach
end TS330
