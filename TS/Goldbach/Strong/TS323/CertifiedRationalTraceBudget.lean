import Mathlib.Tactic
import TS.Goldbach.Strong.TS313.NormalizedTraceBudgetRationalPackagingBridge
import TS.Goldbach.Strong.TS320.UniformDiscreteKusminLandauBound
import TS.Goldbach.Strong.TS322.FiniteCoreEffectiveTail

namespace TS323
namespace Goldbach

noncomputable section

/-!
# TS323: certified rational trace-budget packaging

This module converts certified rational upper bounds for the exact TS322
finite core and effective tail into the TS313 normalized rational budget
interface.  It closes only the conditional routing: no concrete numerical
certificate, half-budget inhabitant, OTSA result, or Goldbach result is
constructed here.
-/

/-! ## Complete conditional certificate -/

/--
All rational certificates needed to pass from the TS322 real pair envelope
to the TS313 normalized half-budget at one good scale.

The exceptional and fixed-left bounds are uniform over the whole dyadic
window because TS314 selects the final arithmetic scale existentially.
-/
structure CertifiedRationalTraceBudgetData where
  coreHeight : Nat
  truncationHeight : Nat
  dyadicScale : Nat

  core_le_height : coreHeight <= truncationHeight
  height_pos : 1 <= truncationHeight
  scale_pos : 0 < dyadicScale
  height_scale_compatible : 4 * truncationHeight <= dyadicScale

  coreMajorant : Rat
  tailMajorant : Rat
  diagonalMajorant : Rat
  qMoment : Rat
  truncationTailMajorant : Rat
  exceptionalMajorant : Rat
  leftMajorant : Rat
  traceBudget : Rat

  coreMajorant_nonnegative : 0 <= coreMajorant
  tailMajorant_nonnegative : 0 <= tailMajorant
  diagonalMajorant_nonnegative : 0 <= diagonalMajorant
  qMoment_nonnegative : 0 <= qMoment
  truncationTailMajorant_nonnegative : 0 <= truncationTailMajorant
  exceptionalMajorant_nonnegative : 0 <= exceptionalMajorant
  leftMajorant_nonnegative : 0 <= leftMajorant

  core_bound :
    TS322.Goldbach.finiteWeightedLocalCore coreHeight <=
      (coreMajorant : Real)
  tail_bound :
    TS322.Goldbach.effectiveWeightedTailError coreHeight <=
      (tailMajorant : Real)
  diagonal_bound :
    4 * TS316.Goldbach.globalQuadraticSpectralMass <=
      (diagonalMajorant : Real)

  moment_allocation :
    (diagonalMajorant : Real) +
        96 * ((coreMajorant : Real) + (tailMajorant : Real)) <=
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

namespace CertifiedRationalTraceBudgetData

theorem pairMajorant_nonnegative
    (D : CertifiedRationalTraceBudgetData) :
    0 <= (D.coreMajorant : Real) + (D.tailMajorant : Real) := by
  exact add_nonneg (by exact_mod_cast D.coreMajorant_nonnegative)
    (by exact_mod_cast D.tailMajorant_nonnegative)

/-- TS322 plus the two rational component certificates bound the pair mass. -/
theorem weightedClosePairEnvelopeBound
    (D : CertifiedRationalTraceBudgetData) :
    TS317.Goldbach.WeightedClosePairEnvelopeBoundStatement
      D.truncationHeight
      ((D.coreMajorant : Real) + (D.tailMajorant : Real)) := by
  refine And.intro D.pairMajorant_nonnegative ?_
  exact
    (TS322.Goldbach.weightedClosePairEnvelope_le_core_add_effectiveTail
      D.truncationHeight D.coreHeight D.core_le_height).trans
        (add_le_add D.core_bound D.tail_bound)

/-- The exact TS316 diagonal bound is weakened only to its certified rational bound. -/
theorem diagonalZeroCorrelationBound
    (D : CertifiedRationalTraceBudgetData) :
    TS315.Goldbach.DiagonalZeroCorrelationBoundStatement
      D.dyadicScale D.truncationHeight (D.diagonalMajorant : Real) := by
  unfold TS315.Goldbach.DiagonalZeroCorrelationBoundStatement
  exact
    (TS316.Goldbach.diagonalZeroCorrelationBound
      D.dyadicScale D.truncationHeight D.scale_pos).trans D.diagonal_bound

/-- The absolute TS320 constant `96` converts the pair certificate to TS315. -/
theorem weightedOffDiagonalCorrelationBound
    (D : CertifiedRationalTraceBudgetData) :
    TS315.Goldbach.WeightedZeroOrdinatePairCorrelationWindowBoundStatement
      D.dyadicScale D.truncationHeight
      (96 * ((D.coreMajorant : Real) + (D.tailMajorant : Real))) := by
  exact TS317.Goldbach.weightedZeroOrdinatePairCorrelationWindowBound_of_reduction
    D.dyadicScale D.truncationHeight 96
      ((D.coreMajorant : Real) + (D.tailMajorant : Real))
      (TS320.Goldbach.uniformWeightedKusminLandauKernelBound
        D.dyadicScale D.truncationHeight D.scale_pos
          D.height_scale_compatible)
      D.weightedClosePairEnvelopeBound

/-- The rational square certificate closes the exact TS314 moment statement. -/
theorem finiteQuadraticSpectralMomentBound
    (D : CertifiedRationalTraceBudgetData) :
    TS314.Goldbach.FiniteQuadraticSpectralMomentBoundStatement
      D.dyadicScale D.truncationHeight (D.qMoment : Real) := by
  exact TS315.Goldbach.finiteQuadraticSpectralMoment_le_of_pair_bounds
    D.dyadicScale D.truncationHeight
      (D.diagonalMajorant : Real)
      (96 * ((D.coreMajorant : Real) + (D.tailMajorant : Real)))
      (D.qMoment : Real)
      D.diagonalZeroCorrelationBound
      D.weightedOffDiagonalCorrelationBound
      D.moment_allocation

/-- TS314 selects a natural scale and adds the certified truncation tail. -/
theorem exists_good_scale_spectral_bound
    (D : CertifiedRationalTraceBudgetData) :
    exists x,
      Membership.mem (TS314.Goldbach.dyadicWindow D.dyadicScale) x /\
        TS313.Goldbach.NormalizedSpectralTraceBoundStatement
          x
          (TS313.Goldbach.canonicalTraceNormalizationFactor x)
          (D.qMoment + D.truncationTailMajorant) := by
  exact TS314.Goldbach.exists_good_scale_normalizedSpectralTraceBound
    D.dyadicScale D.truncationHeight D.scale_pos D.height_pos
      D.qMoment D.truncationTailMajorant D.qMoment_nonnegative
      D.finiteQuadraticSpectralMomentBound D.truncation_tail_bound

/--
The complete certificate produces TS313 data at the scale selected by TS314.
-/
theorem exists_normalizedTraceBudget
    (D : CertifiedRationalTraceBudgetData) :
    exists N : TS313.Goldbach.NormalizedTraceBudgetData,
      Membership.mem (TS314.Goldbach.dyadicWindow D.dyadicScale) N.scale := by
  let hGood := D.exists_good_scale_spectral_bound
  let x := Classical.choose hGood
  have hxSpec := Classical.choose_spec hGood
  have hxWindow := hxSpec.1
  have hxSpectral := hxSpec.2
  have hxOne : 1 <= x :=
    TS314.Goldbach.one_le_of_mem_dyadicWindow D.scale_pos hxWindow
  have hxPos : 0 < x := by omega
  let N : TS313.Goldbach.NormalizedTraceBudgetData := {
    scale := x
    scale_pos := hxPos
    normalizationFactor :=
      TS313.Goldbach.canonicalTraceNormalizationFactor x
    normalizationFactor_nonnegative :=
      (TS313.Goldbach.canonicalTraceNormalizationFactor_positive x hxPos).le
    normalization_spec := rfl
    zeroFamily := D.zeroFamily
    spectralMajorant := D.qMoment + D.truncationTailMajorant
    exceptionalMajorant := D.exceptionalMajorant
    leftMajorant := D.leftMajorant
    spectralMajorant_nonnegative :=
      add_nonneg D.qMoment_nonnegative D.truncationTailMajorant_nonnegative
    exceptionalMajorant_nonnegative := D.exceptionalMajorant_nonnegative
    leftMajorant_nonnegative := D.leftMajorant_nonnegative
    spectral_bound_valid := hxSpectral
    exceptional_bound_valid := D.exceptional_window_bound x hxWindow
    left_bound_valid := D.left_window_bound x hxWindow
    traceBudget := D.traceBudget
    traceBudget_pos := D.traceBudget_pos
    traceBudget_le_half := D.traceBudget_le_half
    components_le_budget := D.components_le_budget
  }
  exact Exists.intro N hxWindow

/-- A canonical chosen TS313 package for downstream definitions. -/
noncomputable def normalizedTraceBudgetData
    (D : CertifiedRationalTraceBudgetData) :
    TS313.Goldbach.NormalizedTraceBudgetData :=
  Classical.choose D.exists_normalizedTraceBudget

theorem normalizedTraceBudgetData_scale_mem
    (D : CertifiedRationalTraceBudgetData) :
    Membership.mem (TS314.Goldbach.dyadicWindow D.dyadicScale)
      D.normalizedTraceBudgetData.scale :=
  Classical.choose_spec D.exists_normalizedTraceBudget

/-- Final conditional routing into the exact TS181 adapter boundary. -/
noncomputable def toTS181TraceBudgetAdapterData
    (D : CertifiedRationalTraceBudgetData) :
    TS312.Goldbach.TS181TraceBudgetAdapterData :=
  TS313.Goldbach.ts181TraceBudgetAdapterData_of_normalizedBudget
    D.normalizedTraceBudgetData

end CertifiedRationalTraceBudgetData

/-! ## Fail-closed ledger -/

structure TS323Ledger where
  rational_core_certificate_interface_defined : True
  rational_tail_certificate_interface_defined : True
  rational_diagonal_certificate_interface_defined : True
  uniform_residual_certificate_interfaces_defined : True
  ts322_pair_bound_routed : True
  ts320_constant_96_routed : True
  ts316_diagonal_bound_routed : True
  ts315_moment_bound_routed : True
  ts314_good_scale_selection_routed : True
  ts313_normalized_budget_constructed_conditionally : True
  ts181_adapter_constructed_conditionally : True
  concrete_certificate_not_constructed : True
  unconditional_half_budget_not_claimed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts323Ledger : TS323Ledger where
  rational_core_certificate_interface_defined := True.intro
  rational_tail_certificate_interface_defined := True.intro
  rational_diagonal_certificate_interface_defined := True.intro
  uniform_residual_certificate_interfaces_defined := True.intro
  ts322_pair_bound_routed := True.intro
  ts320_constant_96_routed := True.intro
  ts316_diagonal_bound_routed := True.intro
  ts315_moment_bound_routed := True.intro
  ts314_good_scale_selection_routed := True.intro
  ts313_normalized_budget_constructed_conditionally := True.intro
  ts181_adapter_constructed_conditionally := True.intro
  concrete_certificate_not_constructed := True.intro
  unconditional_half_budget_not_claimed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end
end Goldbach
end TS323
