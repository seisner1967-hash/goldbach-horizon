import Mathlib.Tactic
import TS.Goldbach.Strong.TS312.PostWall2EffectiveFormulaContractDischarge

namespace TS313
namespace Goldbach

noncomputable section

/-!
# Normalized trace budget and rational packaging bridge

TS311 supplies a complex explicit identity at arithmetic scale `x`, while
TS181 consumes nonnegative rational trace entries bounded by a rational budget
at most one half.  This module records the missing normalization and proves the
pure packaging implication.  It does not prove the pointwise spectral bound,
the future Gallagher variance statement, or an inhabitant of the normalized
budget data.
-/

/-! ## Canonical normalization -/

/-- The normalization sending the Perron main term `x / 2` to one. -/
noncomputable def canonicalTraceNormalizationFactor
    (x : Nat) : Real :=
  2 / (x : Real)

theorem canonicalTraceNormalizationFactor_nonnegative
    (x : Nat) :
    0 <= canonicalTraceNormalizationFactor x := by
  unfold canonicalTraceNormalizationFactor
  positivity

theorem canonicalTraceNormalizationFactor_positive
    (x : Nat)
    (hx : 0 < x) :
    0 < canonicalTraceNormalizationFactor x := by
  unfold canonicalTraceNormalizationFactor
  positivity

/-- The canonical factor sends the TS204 Perron main term `x / 2` to one. -/
theorem canonicalTraceNormalizationFactor_mul_mainTerm_eq_one
    (x : Nat)
    (hx : 0 < x) :
    canonicalTraceNormalizationFactor x *
        TS293.Goldbach.triangleSplinePerronMainTerm x = 1 := by
  rw [TS312.Goldbach.postWall2MainTermIdentification x]
  unfold canonicalTraceNormalizationFactor
  have hxR : Not ((x : Real) = 0) := by
    exact_mod_cast Nat.ne_of_gt hx
  field_simp

/-- Real normalized size of the infinite nontrivial-zero contribution. -/
noncomputable def normalizedSpectralTrace
    (x : Nat)
    (normalizationFactor : Real) : Real :=
  normalizationFactor *
    norm (TS292.Goldbach.infiniteZeroContribution x)

/-- Real normalized size of the two exceptional residues `0` and `-1`. -/
noncomputable def normalizedExceptionalResidual
    (x : Nat)
    (normalizationFactor : Real) : Real :=
  normalizationFactor *
    norm (TS311.Goldbach.infiniteExceptionalResidueContribution x)

/-- Real normalized size of the surviving fixed-left boundary integral. -/
noncomputable def normalizedFixedLeftResidual
    (x : Nat)
    (normalizationFactor : Real) : Real :=
  normalizationFactor *
    norm (TS293.Goldbach.normalizeContourIntegral
      (TS305.Goldbach.fixedLeftBoundaryLimit x))

/--
Pointwise normalized spectral output expected after a future Gallagher
variance argument and good-scale selection.
-/
def NormalizedSpectralTraceBoundStatement
    (x : Nat)
    (normalizationFactor : Real)
    (spectralMajorant : Rat) : Prop :=
  normalizedSpectralTrace x normalizationFactor <=
    (spectralMajorant : Real)

/-! ## Rich normalized budget data -/

/--
Certified real-to-rational data at one arithmetic scale.

The exceptional and fixed-left fields dominate the closed TS311 envelopes.
The spectral field is the pointwise output expected after a future Gallagher
variance argument.  The rational sum is already required to fit inside the
positive half-budget.
-/
structure NormalizedTraceBudgetData where
  scale : Nat
  scale_pos : 0 < scale

  normalizationFactor : Real
  normalizationFactor_nonnegative : 0 <= normalizationFactor
  normalization_spec :
    normalizationFactor = canonicalTraceNormalizationFactor scale

  zeroFamily : TS93.Goldbach.ZetaZeroFamilyLedger

  spectralMajorant : Rat
  exceptionalMajorant : Rat
  leftMajorant : Rat

  spectralMajorant_nonnegative : 0 <= spectralMajorant
  exceptionalMajorant_nonnegative : 0 <= exceptionalMajorant
  leftMajorant_nonnegative : 0 <= leftMajorant

  spectral_bound_valid :
    NormalizedSpectralTraceBoundStatement
      scale normalizationFactor spectralMajorant

  exceptional_bound_valid :
    normalizationFactor *
        TS306.Goldbach.concreteExceptionalResidueBound scale <=
      (exceptionalMajorant : Real)

  left_bound_valid :
    normalizationFactor *
        (TS305.Goldbach.fixedLeftUniformBound scale
          TS307.Goldbach.fixedLeftLogDerivativeBoundData /
            (2 * Real.pi)) <=
      (leftMajorant : Real)

  traceBudget : Rat
  traceBudget_pos : 0 < traceBudget
  traceBudget_le_half : traceBudget <= 1 / 2

  components_le_budget :
    spectralMajorant + exceptionalMajorant + leftMajorant <= traceBudget

namespace NormalizedTraceBudgetData

theorem normalizationFactor_positive
    (D : NormalizedTraceBudgetData) :
    0 < D.normalizationFactor := by
  rw [D.normalization_spec]
  exact canonicalTraceNormalizationFactor_positive D.scale D.scale_pos

theorem normalizes_main_term
    (D : NormalizedTraceBudgetData) :
    D.normalizationFactor *
        TS293.Goldbach.triangleSplinePerronMainTerm D.scale = 1 := by
  rw [D.normalization_spec]
  exact canonicalTraceNormalizationFactor_mul_mainTerm_eq_one
    D.scale D.scale_pos

theorem normalizedSpectralTrace_le_majorant
    (D : NormalizedTraceBudgetData) :
    normalizedSpectralTrace D.scale D.normalizationFactor <=
      (D.spectralMajorant : Real) :=
  D.spectral_bound_valid

theorem normalizedExceptionalResidual_le_majorant
    (D : NormalizedTraceBudgetData) :
    normalizedExceptionalResidual D.scale D.normalizationFactor <=
      (D.exceptionalMajorant : Real) := by
  unfold normalizedExceptionalResidual
  exact (mul_le_mul_of_nonneg_left
    (TS311.Goldbach.infiniteExceptionalResidueContribution_norm_le D.scale)
    D.normalizationFactor_nonnegative).trans D.exceptional_bound_valid

theorem normalizedFixedLeftResidual_le_majorant
    (D : NormalizedTraceBudgetData) :
    normalizedFixedLeftResidual D.scale D.normalizationFactor <=
      (D.leftMajorant : Real) := by
  unfold normalizedFixedLeftResidual
  exact (mul_le_mul_of_nonneg_left
    (TS311.Goldbach.normalizedFixedLeftBoundaryLimit_norm_le D.scale)
    D.normalizationFactor_nonnegative).trans D.left_bound_valid

/-- The two analytically distinct residual pieces fit the TS95 contour slot. -/
theorem normalizedContourResidual_le_majorant
    (D : NormalizedTraceBudgetData) :
    D.normalizationFactor *
        norm (TS311.Goldbach.infiniteContourResidualComplex D.scale) <=
      (D.exceptionalMajorant : Real) + (D.leftMajorant : Real) := by
  have hNorm :
      norm (TS311.Goldbach.infiniteContourResidualComplex D.scale) <=
        norm (TS311.Goldbach.infiniteExceptionalResidueContribution D.scale) +
          norm (TS293.Goldbach.normalizeContourIntegral
            (TS305.Goldbach.fixedLeftBoundaryLimit D.scale)) := by
    unfold TS311.Goldbach.infiniteContourResidualComplex
    exact norm_add_le _ _
  calc
    D.normalizationFactor *
        norm (TS311.Goldbach.infiniteContourResidualComplex D.scale) <=
      D.normalizationFactor *
        (norm (TS311.Goldbach.infiniteExceptionalResidueContribution D.scale) +
          norm (TS293.Goldbach.normalizeContourIntegral
            (TS305.Goldbach.fixedLeftBoundaryLimit D.scale))) :=
      mul_le_mul_of_nonneg_left hNorm D.normalizationFactor_nonnegative
    _ = normalizedExceptionalResidual D.scale D.normalizationFactor +
        normalizedFixedLeftResidual D.scale D.normalizationFactor := by
      unfold normalizedExceptionalResidual normalizedFixedLeftResidual
      ring
    _ <= (D.exceptionalMajorant : Real) + (D.leftMajorant : Real) :=
      add_le_add D.normalizedExceptionalResidual_le_majorant
        D.normalizedFixedLeftResidual_le_majorant

end NormalizedTraceBudgetData

/-! ## Rational TS95 packaging -/

/-- The normalized spectral majorant as the TS95 nontrivial-zero entry. -/
def normalizedZeroTraceContribution
    (D : NormalizedTraceBudgetData) :
    TS95.Goldbach.NontrivialZeroTraceContribution where
  value := D.spectralMajorant
  nonneg := D.spectralMajorant_nonnegative

/--
Canonical TS95 residual allocation.

The main pole at `1` is already the TS204 term `x / 2`, and the rectangle lies
to the right of the first trivial zero `-2`.  Hence both corresponding TS95
slots are zero.  Only the exceptional residues and fixed-left boundary enter
the contour slot.
-/
def normalizedResidualTerms
    (D : NormalizedTraceBudgetData) :
    TS95.Goldbach.ExplicitFormulaResidualTerms where
  poleTerm := 0
  trivialZeroTerm := 0
  contourError := D.exceptionalMajorant + D.leftMajorant
  pole_nonneg := by norm_num
  trivial_nonneg := by norm_num
  contour_nonneg := add_nonneg
    D.exceptionalMajorant_nonnegative D.leftMajorant_nonnegative

theorem normalizedResidualTerms_total
    (D : NormalizedTraceBudgetData) :
    TS95.Goldbach.ExplicitFormulaResidualTerms.total
        (normalizedResidualTerms D) =
      D.exceptionalMajorant + D.leftMajorant := by
  simp [normalizedResidualTerms,
    TS95.Goldbach.ExplicitFormulaResidualTerms.total]

/--
Pure rational packaging from a certified normalized budget into TS312's exact
TS181 adapter boundary.
-/
def ts181TraceBudgetAdapterData_of_normalizedBudget
    (D : NormalizedTraceBudgetData) :
    TS312.Goldbach.TS181TraceBudgetAdapterData where
  zeroFamily := D.zeroFamily
  zeroContribution := normalizedZeroTraceContribution D
  residuals := normalizedResidualTerms D
  traceBudget := D.traceBudget
  traceBudget_pos := D.traceBudget_pos
  traceBudget_le_half := D.traceBudget_le_half
  trace_budget_controls_formula := by
    simpa [normalizedZeroTraceContribution, normalizedResidualTerms,
      TS95.Goldbach.ExplicitFormulaResidualTerms.total, add_assoc] using
        D.components_le_budget

/-- Any certified normalized budget reaches the downstream TS95 target. -/
theorem explicitFormulaTraceBridgeTarget_of_normalizedBudget
    (D : NormalizedTraceBudgetData) :
    TS95.Goldbach.ExplicitFormulaTraceBridgeTarget :=
  TS312.Goldbach.explicitFormulaTraceBridgeTarget_of_adapter
    (ts181TraceBudgetAdapterData_of_normalizedBudget D)

/-! ## Fail-closed status -/

structure TS313Ledger where
  canonical_two_div_scale_normalization_defined : True
  normalization_scale_preserved : True
  spectral_and_residual_components_separated : True
  exceptional_and_left_real_bounds_routed : True
  rational_ts95_packaging_proved : True
  ts181_adapter_construction_proved : True
  main_pole_not_double_counted : True
  trivial_zero_slot_zero_for_fixed_rectangle : True
  normalized_spectral_trace_bound_not_proved : True
  gallagher_variance_statement_deferred_to_ts314 : True
  normalized_budget_data_not_constructed : True
  rh_not_assumed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts313Ledger : TS313Ledger where
  canonical_two_div_scale_normalization_defined := True.intro
  normalization_scale_preserved := True.intro
  spectral_and_residual_components_separated := True.intro
  exceptional_and_left_real_bounds_routed := True.intro
  rational_ts95_packaging_proved := True.intro
  ts181_adapter_construction_proved := True.intro
  main_pole_not_double_counted := True.intro
  trivial_zero_slot_zero_for_fixed_rectangle := True.intro
  normalized_spectral_trace_bound_not_proved := True.intro
  gallagher_variance_statement_deferred_to_ts314 := True.intro
  normalized_budget_data_not_constructed := True.intro
  rh_not_assumed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end


end Goldbach
end TS313
