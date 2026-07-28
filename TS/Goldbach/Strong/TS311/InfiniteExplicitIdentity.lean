import Mathlib.Tactic
import TS.Goldbach.Strong.TS310.ScalarMellinPerronInversion

/-!
# TS311 - Infinite Explicit Identity

This module passes the unconditional finite-height Perron identity of TS310 to
the infinite-height limit along the quantitative finite-grid contours of
TS299.  It introduces no new zero-density or complex-growth estimate: every
limit is routed from TS292, TS294, TS298, TS304, and TS307.

The exceptional residues and the fixed-left improper integral remain separate
in the canonical theorem.  An aggregated residual is provided only as a
downstream convenience interface.
-/

noncomputable section

namespace TS311
namespace Goldbach

open Complex Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Canonical finite-grid sequence -/

/-- The quantitative clean contour at natural cutoff `T + 1`. -/
noncomputable def canonicalInfiniteHeightContour
    (T : Nat) :
    TS294.Goldbach.QuantitativelyCleanPerronContourData (T + 1) :=
  TS299.Goldbach.finiteGridStrongPerronContourData (T + 1) (by omega)

/-- The exceptional inventory attached to the canonical finite-grid contour. -/
noncomputable def canonicalExceptionalInventory
    (x T : Nat)
    (hx : 0 < x) :
    TS293.Goldbach.PerronExceptionalResidueInventory x
      (canonicalInfiniteHeightContour T).toPerronRectangle :=
  (TS308.Goldbach.completePerronResidueCensus
    x (T + 1) hx (canonicalInfiniteHeightContour T)).exceptional.inventory

/-- The TS293 contour residual along the canonical finite-grid sequence. -/
noncomputable def canonicalContourResidualComplex
    (x T : Nat)
    (hx : 0 < x) : Complex :=
  TS293.Goldbach.triangleSplineContourResidualComplex x (T + 1)
    (canonicalInfiniteHeightContour T).toCleanPerronContourData
    (canonicalExceptionalInventory x T hx)

/-- Canonical fixed-left truncation. -/
noncomputable def canonicalLeftBoundary
    (x T : Nat) : Complex :=
  TS293.Goldbach.perronLeftForwardIntegral x
    (canonicalInfiniteHeightContour T).toPerronRectangle

/-- Canonical negative normalized non-right boundary contribution. -/
noncomputable def canonicalNegativeNonRightBoundary
    (x T : Nat) : Complex :=
  -TS293.Goldbach.normalizedNonRightBoundary x
    (canonicalInfiniteHeightContour T).toPerronRectangle

/-- Canonical right-line cutoff. -/
noncomputable def canonicalRightCutoff
    (x T : Nat) : Complex :=
  TS293.Goldbach.perronRightLineCutoffAdjustment x
    (canonicalInfiniteHeightContour T).toPerronRectangle

/-- Canonical adjustment from the natural cutoff to the selected real height. -/
noncomputable def canonicalSpectralAdjustment
    (x T : Nat) : Complex :=
  TS293.Goldbach.spectralHeightCutoffAdjustment x (T + 1)
    (canonicalInfiniteHeightContour T).tau

/-! ## Exact exceptional contribution -/

/-- Exact symbolic contribution of the exceptional poles `0` and `-1`. -/
noncomputable def infiniteExceptionalResidueContribution
    (x : Nat) : Complex :=
  -deriv riemannZeta 0 / riemannZeta 0 +
    (1 / (x : Complex)) *
      (deriv riemannZeta (-1) / riemannZeta (-1))

theorem canonicalExceptionalResidueContribution_eq
    (x T : Nat)
    (hx : 0 < x) :
    TS293.Goldbach.exceptionalResidueContribution
        (canonicalExceptionalInventory x T hx) =
      infiniteExceptionalResidueContribution x := by
  simpa [canonicalExceptionalInventory, canonicalInfiniteHeightContour,
    infiniteExceptionalResidueContribution,
    TS308.Goldbach.completePerronResidueCensus,
    TS306.Goldbach.mainTermSeparatedExceptionalInventory] using
    (TS306.Goldbach.concreteExceptionalResidueContribution_eq_inv
      x hx (canonicalInfiniteHeightContour T).toPerronRectangle)

/-! ## Component limits -/

/-- The selected finite-grid heights tend to infinity. -/
theorem canonicalFiniteGridTau_tendsto_atTop :
    Tendsto
      (fun T : Nat => (canonicalInfiniteHeightContour T).tau)
      atTop atTop := by
  have hBase :
      Tendsto (fun T : Nat => (((T + 1 : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall (fun T =>
      (TS299.Goldbach.finiteGridStrongTau_gt (T + 1)).le)) hBase

/-- The canonical left side converges to the absolutely convergent fixed-left
improper integral. -/
theorem canonicalLeftBoundary_tendsto
    (x : Nat)
    (hx : 0 < x) :
    Tendsto (canonicalLeftBoundary x) atTop
      (nhds (TS305.Goldbach.fixedLeftBoundaryLimit x)) := by
  have hBase :=
    (TS307.Goldbach.fixedLeftBoundaryTruncation_tendsto x hx).comp
      canonicalFiniteGridTau_tendsto_atTop
  apply hBase.congr'
  filter_upwards with T
  exact (TS305.Goldbach.perronLeftForwardIntegral_eq_fixedLeftBoundaryTruncation
    x (canonicalInfiniteHeightContour T).toPerronRectangle rfl).symm

/-- The complete canonical horizontal pair is already known to vanish. -/
theorem canonicalHorizontalPair_tendsto_zero
    (x : Nat) :
    Tendsto
      (fun T : Nat =>
        TS293.Goldbach.perronBottomIntegral x
            (canonicalInfiniteHeightContour T).toPerronRectangle -
          TS293.Goldbach.perronTopForwardIntegral x
            (canonicalInfiniteHeightContour T).toPerronRectangle)
      atTop (nhds 0) := by
  simpa [canonicalInfiniteHeightContour,
    TS304.Goldbach.finiteGridCanonicalBottomHorizontalIntegral,
    TS304.Goldbach.finiteGridCanonicalTopHorizontalIntegral] using
    TS304.Goldbach.finiteGridCanonicalHorizontalPair_tendsto_zero x

/-- After orientation and normalization, the non-right boundary converges with
the positive fixed-left sign. -/
theorem canonicalNegativeNonRightBoundary_tendsto
    (x : Nat)
    (hx : 0 < x) :
    Tendsto (canonicalNegativeNonRightBoundary x) atTop
      (nhds (TS293.Goldbach.normalizeContourIntegral
        (TS305.Goldbach.fixedLeftBoundaryLimit x))) := by
  have hRaw :=
    (canonicalHorizontalPair_tendsto_zero x).sub
      (canonicalLeftBoundary_tendsto x hx)
  have hNormalized := hRaw.div_const (((2 * Real.pi : Real) : Complex) * I)
  have hNeg := hNormalized.neg
  convert hNeg using 1
  all_goals
    simp [canonicalNegativeNonRightBoundary,
      canonicalInfiniteHeightContour,
      TS293.Goldbach.normalizedNonRightBoundary,
      TS293.Goldbach.perronNonRightBoundaryIntegral,
      TS293.Goldbach.normalizeContourIntegral]
    ring

/-- The elementary logarithmic TS292 tail rate tends to zero. -/
theorem logarithmicTailRate_tendsto_zero :
    Tendsto TS292.Goldbach.logarithmicTailRate atTop (nhds 0) := by
  have hShift :
      Tendsto (fun T : Nat => (T : Real) + 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hLogBase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hShift
  have hLog :
      Tendsto
        (fun T : Nat => Real.log ((T : Real) + 2) / (T : Real))
        atTop (nhds 0) := by
    apply hLogBase.congr'
    filter_upwards with T
    norm_num [Function.comp_def, pow_one]
  have hInv :
      Tendsto (fun T : Nat => 1 / (T : Real)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hSum := hLog.add hInv
  have hSum' :
      Tendsto
        (fun T : Nat =>
          Real.log ((T : Real) + 2) / (T : Real) + 1 / (T : Real))
        atTop (nhds 0) := by
    simpa using hSum
  apply hSum'.congr'
  filter_upwards with T
  simp [TS292.Goldbach.logarithmicTailRate, add_div]

/-- The closed TS294 spectral-adjustment envelope tends to zero along `T+1`. -/
theorem canonicalSpectralAdjustmentEnvelope_tendsto_zero
    (x : Nat) :
    Tendsto
      (fun T : Nat =>
        TS294.Goldbach.spectralHeightAdjustmentEnvelope x (T + 1))
      atTop (nhds 0) := by
  have hRate := logarithmicTailRate_tendsto_zero.comp
    (tendsto_add_atTop_nat 1)
  have hScaled := hRate.const_mul
    (max 1 (x : Real) *
      TS292.Goldbach.infiniteZeroResidualTailConstant)
  have hScaled' :
      Tendsto
        (fun T : Nat =>
          (max 1 (x : Real) *
            TS292.Goldbach.infiniteZeroResidualTailConstant) *
              TS292.Goldbach.logarithmicTailRate (T + 1))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hScaled
  apply hScaled'.congr'
  filter_upwards with T
  unfold TS294.Goldbach.spectralHeightAdjustmentEnvelope
  ring

/-- The natural-height to contour-height spectral correction vanishes. -/
theorem canonicalSpectralAdjustment_tendsto_zero
    (x : Nat) :
    Tendsto (canonicalSpectralAdjustment x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_
    (canonicalSpectralAdjustmentEnvelope_tendsto_zero x)
  next => exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  next => exact Filter.Eventually.of_forall (fun T => by
      exact TS294.Goldbach.quantitativeContour_spectralHeightCutoffAdjustment_norm_le
        x (T + 1) (by omega) (canonicalInfiniteHeightContour T))

/-- Elementary envelope for the canonical right cutoff. -/
noncomputable def canonicalRightCutoffEnvelope
    (x T : Nat) : Real :=
  TS298.Goldbach.rightLineCutoffConstant *
    TS298.Goldbach.rightLineScale x / ((T + 1 : Nat) : Real)

theorem canonicalRightCutoffEnvelope_tendsto_zero
    (x : Nat) :
    Tendsto (canonicalRightCutoffEnvelope x) atTop (nhds 0) := by
  have hInv := tendsto_one_div_atTop_nhds_zero_nat.comp
    (tendsto_add_atTop_nat 1)
  have hMul := hInv.const_mul
    (TS298.Goldbach.rightLineCutoffConstant *
      TS298.Goldbach.rightLineScale x)
  have hMul' :
      Tendsto
        (fun T : Nat =>
          (TS298.Goldbach.rightLineCutoffConstant *
            TS298.Goldbach.rightLineScale x) *
              (1 / (((T + 1 : Nat) : Real))))
        atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add] using hMul
  apply hMul'.congr'
  filter_upwards with T
  simp [canonicalRightCutoffEnvelope, div_eq_mul_inv, Nat.cast_add]

/-- The right-line cutoff vanishes along the canonical contours. -/
theorem canonicalRightCutoff_tendsto_zero
    (x : Nat) :
    Tendsto (canonicalRightCutoff x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_ (canonicalRightCutoffEnvelope_tendsto_zero x)
  next => exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  next => exact Filter.Eventually.of_forall (fun T => by
      have hFixed :=
        TS298.Goldbach.perronRightLineCutoffAdjustment_norm_le_fixed x
          (canonicalInfiniteHeightContour T).toPerronRectangle rfl
      have hNumerator :
          0 <= TS298.Goldbach.rightLineCutoffConstant *
            TS298.Goldbach.rightLineScale x :=
        mul_nonneg TS298.Goldbach.rightLineCutoffConstant_nonnegative
          (TS298.Goldbach.rightLineScale_nonnegative x)
      exact hFixed.trans (div_le_div_of_nonneg_left hNumerator
        (by positivity)
        (canonicalInfiniteHeightContour T).height_ge))

/-! ## Residual convergence -/

theorem canonicalContourResidualComplex_eq_components
    (x T : Nat)
    (hx : 0 < x) :
    canonicalContourResidualComplex x T hx =
      infiniteExceptionalResidueContribution x +
        canonicalNegativeNonRightBoundary x T +
          canonicalRightCutoff x T +
            canonicalSpectralAdjustment x T := by
  unfold canonicalContourResidualComplex canonicalNegativeNonRightBoundary
    canonicalRightCutoff canonicalSpectralAdjustment
    TS293.Goldbach.triangleSplineContourResidualComplex
  rw [canonicalExceptionalResidueContribution_eq x T hx]
  ring

/-- Aggregated facade for downstream modules. -/
noncomputable def infiniteContourResidualComplex
    (x : Nat) : Complex :=
  infiniteExceptionalResidueContribution x +
    TS293.Goldbach.normalizeContourIntegral
      (TS305.Goldbach.fixedLeftBoundaryLimit x)

theorem canonicalContourResidualComplex_tendsto
    (x : Nat)
    (hx : 0 < x) :
    Tendsto (fun T => canonicalContourResidualComplex x T hx) atTop
      (nhds (infiniteContourResidualComplex x)) := by
  have hExceptional :
      Tendsto
        (fun _ : Nat => infiniteExceptionalResidueContribution x)
        atTop (nhds (infiniteExceptionalResidueContribution x)) :=
    tendsto_const_nhds
  have hComponents :=
    ((hExceptional.add
      (canonicalNegativeNonRightBoundary_tendsto x hx)).add
        (canonicalRightCutoff_tendsto_zero x)).add
          (canonicalSpectralAdjustment_tendsto_zero x)
  have hComponents' :
      Tendsto
        (fun T : Nat =>
          infiniteExceptionalResidueContribution x +
            canonicalNegativeNonRightBoundary x T +
              canonicalRightCutoff x T +
                canonicalSpectralAdjustment x T)
        atTop (nhds (infiniteContourResidualComplex x)) := by
    simpa [infiniteContourResidualComplex] using hComponents
  apply hComponents'.congr'
  filter_upwards with T
  rw [canonicalContourResidualComplex_eq_components x T hx]

/-- The natural zero truncations at `T+1` retain the TS292 limit. -/
theorem canonicalTruncatedZeroContribution_tendsto
    (x : Nat) :
    Tendsto
      (fun T : Nat =>
        TS292.Goldbach.truncatedInfiniteZeroContribution x (T + 1))
      atTop (nhds (TS292.Goldbach.infiniteZeroContribution x)) :=
  (TS292.Goldbach.truncatedInfiniteZeroContribution_tendsto x).comp
    (tendsto_add_atTop_nat 1)

/-! ## Infinite explicit identities -/

/-- Canonical expanded complex explicit identity. -/
theorem infiniteExplicitIdentity_complex_expanded
    (x : Nat)
    (hx : 0 < x) :
    ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Real) : Complex) =
      (x : Complex) / 2 - TS292.Goldbach.infiniteZeroContribution x +
        infiniteExceptionalResidueContribution x +
          TS293.Goldbach.normalizeContourIntegral
            (TS305.Goldbach.fixedLeftBoundaryLimit x) := by
  let rhs : Nat -> Complex := fun T =>
    (x : Complex) / 2 -
      TS292.Goldbach.truncatedInfiniteZeroContribution x (T + 1) +
        canonicalContourResidualComplex x T hx
  have hRhs :
      Tendsto rhs atTop
        (nhds ((x : Complex) / 2 - TS292.Goldbach.infiniteZeroContribution x +
          infiniteContourResidualComplex x)) := by
    exact (tendsto_const_nhds.sub
      (canonicalTruncatedZeroContribution_tendsto x)).add
        (canonicalContourResidualComplex_tendsto x hx)
  have hEventually :
      Filter.EventuallyEq atTop
        (fun _ : Nat =>
          ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
            Real) : Complex)) rhs := by
    filter_upwards with T
    exact TS310.Goldbach.canonical_truncatedPerronExplicitIdentity_complex
      x (T + 1) hx (canonicalInfiniteHeightContour T)
  have hConstant :
      Tendsto rhs atTop
        (nhds ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
          Real) : Complex)) :=
    tendsto_const_nhds.congr' hEventually
  have hLimit := tendsto_nhds_unique hConstant hRhs
  calc
    ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Real) : Complex) =
        (x : Complex) / 2 - TS292.Goldbach.infiniteZeroContribution x +
          infiniteContourResidualComplex x := hLimit
    _ = (x : Complex) / 2 - TS292.Goldbach.infiniteZeroContribution x +
          infiniteExceptionalResidueContribution x +
            TS293.Goldbach.normalizeContourIntegral
              (TS305.Goldbach.fixedLeftBoundaryLimit x) := by
      unfold infiniteContourResidualComplex
      ring

/-- Canonical expanded real explicit identity. -/
theorem infiniteExplicitIdentity_real_expanded
    (x : Nat)
    (hx : 0 < x) :
    TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x =
      TS293.Goldbach.triangleSplinePerronMainTerm x -
        (TS292.Goldbach.infiniteZeroContribution x).re +
          (infiniteExceptionalResidueContribution x).re +
            (TS293.Goldbach.normalizeContourIntegral
              (TS305.Goldbach.fixedLeftBoundaryLimit x)).re := by
  have hRe := congrArg Complex.re
    (infiniteExplicitIdentity_complex_expanded x hx)
  simpa [TS293.Goldbach.triangleSplinePerronMainTerm] using hRe

/-- Real facade for the aggregated infinite residual. -/
noncomputable def infiniteContourResidualReal
    (x : Nat) : Real :=
  (infiniteContourResidualComplex x).re

/-- Compact complex explicit identity. -/
theorem infiniteExplicitIdentity_complex
    (x : Nat)
    (hx : 0 < x) :
    ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Real) : Complex) =
      (x : Complex) / 2 - TS292.Goldbach.infiniteZeroContribution x +
        infiniteContourResidualComplex x := by
  rw [infiniteExplicitIdentity_complex_expanded x hx]
  unfold infiniteContourResidualComplex
  ring

/-- Compact real explicit identity. -/
theorem infiniteExplicitIdentity_real
    (x : Nat)
    (hx : 0 < x) :
    TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x =
      TS293.Goldbach.triangleSplinePerronMainTerm x -
        (TS292.Goldbach.infiniteZeroContribution x).re +
          infiniteContourResidualReal x := by
  rw [infiniteExplicitIdentity_real_expanded x hx]
  unfold infiniteContourResidualReal infiniteContourResidualComplex
  simp
  ring

/-! ## Componentwise residual bound -/

/-- Height-independent bound retaining the exceptional and fixed-left origins. -/
noncomputable def infiniteContourResidualBound
    (x : Nat) : Real :=
  TS306.Goldbach.concreteExceptionalResidueBound x +
    TS305.Goldbach.fixedLeftUniformBound x
      TS307.Goldbach.fixedLeftLogDerivativeBoundData / (2 * Real.pi)

theorem infiniteExceptionalResidueContribution_norm_le
    (x : Nat) :
    norm (infiniteExceptionalResidueContribution x) <=
      TS306.Goldbach.concreteExceptionalResidueBound x := by
  unfold infiniteExceptionalResidueContribution
    TS306.Goldbach.concreteExceptionalResidueBound
  exact norm_add_le _ _

theorem normalizedFixedLeftBoundaryLimit_norm_le
    (x : Nat) :
    norm (TS293.Goldbach.normalizeContourIntegral
        (TS305.Goldbach.fixedLeftBoundaryLimit x)) <=
      TS305.Goldbach.fixedLeftUniformBound x
        TS307.Goldbach.fixedLeftLogDerivativeBoundData / (2 * Real.pi) := by
  unfold TS293.Goldbach.normalizeContourIntegral
  rw [norm_div]
  have hDen :
      norm ((((2 * Real.pi : Real) : Complex) * I)) = 2 * Real.pi := by
    rw [norm_mul, norm_I, mul_one]
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hDen]
  exact div_le_div_of_nonneg_right
    (TS307.Goldbach.fixedLeftBoundaryLimit_norm_le x) (by positivity)

theorem infiniteContourResidualComplex_norm_le
    (x : Nat) :
    norm (infiniteContourResidualComplex x) <=
      infiniteContourResidualBound x := by
  unfold infiniteContourResidualComplex infiniteContourResidualBound
  exact (norm_add_le _ _).trans (add_le_add
    (infiniteExceptionalResidueContribution_norm_le x)
    (normalizedFixedLeftBoundaryLimit_norm_le x))

/-! ## Fail-closed ledger -/

structure InfiniteExplicitIdentityLedger where
  infinite_height_limit_proved : True
  left_boundary_limit_composed : True
  spectral_tail_converged : True
  horizontal_cutoff_vanished : True
  right_cutoff_vanished : True
  exceptional_residue_limit_identified : True
  complex_developed_identity_proved : True
  real_developed_identity_proved : True
  aggregated_facade_defined : True
  aggregated_identity_proved : True
  componentwise_bound_proved : True
  zeta_logDerivative_zero_closed_form_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def infiniteExplicitIdentityLedger : InfiniteExplicitIdentityLedger where
  infinite_height_limit_proved := True.intro
  left_boundary_limit_composed := True.intro
  spectral_tail_converged := True.intro
  horizontal_cutoff_vanished := True.intro
  right_cutoff_vanished := True.intro
  exceptional_residue_limit_identified := True.intro
  complex_developed_identity_proved := True.intro
  real_developed_identity_proved := True.intro
  aggregated_facade_defined := True.intro
  aggregated_identity_proved := True.intro
  componentwise_bound_proved := True.intro
  zeta_logDerivative_zero_closed_form_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS311
