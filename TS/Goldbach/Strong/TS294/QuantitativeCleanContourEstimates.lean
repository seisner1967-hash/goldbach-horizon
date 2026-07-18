import Mathlib.Tactic
import TS.Goldbach.Strong.TS293.TruncatedPerronContourResidual

/-!
# TS294 - Quantitative Clean Contour Estimates

TS293 defines a concrete, non-tautological Perron contour residual.  This
module separates its four quantitative components.

The contour geometry is fixed at `Re(s) = 2` and `Re(s) = -3/2`.  A
quantitatively clean contour strengthens the TS293 nonvanishing data by
recording a positive separation from all nearby nontrivial zero heights.
This is the datum needed by a future local estimate for `zeta'/zeta`; mere
nonvanishing on a compact side is not an effective estimate.

The spectral height adjustment is discharged unconditionally from the TS292
finite-tail theorem.  Bounds for the exceptional residues, the three
non-right sides, and the right-line cutoff are represented by direct,
independently auditable evidence.  From these inputs the complete complex and
real residual bounds are proved.

This module does not prove quantitative clean-height existence, a
logarithmic-derivative estimate, completeness of an exceptional residue
inventory, Perron inversion, the meromorphic rectangle residue theorem, an
infinite explicit formula, Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS294
namespace Goldbach

open Complex Set
open scoped BigOperators

/-- Fixed left edge for the first effective Perron rectangle. -/
def fixedPerronLeft : Real := -3 / 2

/-- Fixed right edge, inside the absolutely convergent zeta half-plane. -/
def fixedPerronRight : Real := 2

theorem fixedPerronLeft_lt_neg_one :
    fixedPerronLeft < -1 := by
  norm_num [fixedPerronLeft]

theorem one_lt_fixedPerronRight :
    1 < fixedPerronRight := by
  norm_num [fixedPerronRight]

/-- The fixed rectangle before any zero-avoidance data are supplied. -/
def fixedPerronRectangle
    (tau : Real)
    (htau : 0 < tau) :
    TS293.Goldbach.PerronRectangle where
  left := fixedPerronLeft
  right := fixedPerronRight
  tau := tau
  left_lt_neg_one := fixedPerronLeft_lt_neg_one
  one_lt_right := one_lt_fixedPerronRight
  tau_pos := htau

/--
A clean contour together with a quantitative gap from every relevant
nontrivial zero height.

The separation is deliberately a field, rather than a hard-coded rate.  A
future density argument may provide a coarse `1 / (T log T)` gap without
changing any downstream contour estimate.
-/
structure QuantitativelyCleanPerronContourData
    (T : Nat)
    extends TS293.Goldbach.CleanPerronContourData T where
  left_eq_fixed : left = fixedPerronLeft
  right_eq_fixed : right = fixedPerronRight
  zeroSeparation : Real
  zeroSeparation_pos : 0 < zeroSeparation
  separated_from_nearby_zeros :
    forall rho : TS292.Goldbach.ConcreteNontrivialZero,
      _root_.abs rho.1.im <= (T : Real) + 2 ->
        zeroSeparation <=
          _root_.abs (tau - _root_.abs rho.1.im)

/-- Exact target for a quantitative clean-height construction. -/
def QuantitativeCleanPerronContourExistenceStatement : Prop :=
  forall T : Nat, 1 <= T ->
    Nonempty (QuantitativelyCleanPerronContourData T)

/-- Quantitative data forget to the clean data required by TS293. -/
def QuantitativelyCleanPerronContourData.clean
    {T : Nat}
    (D : QuantitativelyCleanPerronContourData T) :
    TS293.Goldbach.CleanPerronContourData T :=
  D.toCleanPerronContourData

/-- The fixed right edge is automatically zero-free. -/
theorem riemannZeta_ne_zero_on_fixedPerronRight
    (t : Real) :
    Not
      (riemannZeta
        ((fixedPerronRight : Complex) + (t : Complex) * I) = 0) := by
  exact TS293.Goldbach.riemannZeta_ne_zero_on_perron_right_line
    one_lt_fixedPerronRight

/-- The exact TS292 closed spectral-tail envelope. -/
noncomputable def spectralHeightAdjustmentEnvelope
    (x T : Nat) :
    Real :=
  max 1 (x : Real) *
    (TS292.Goldbach.infiniteZeroResidualTailConstant *
      TS292.Goldbach.logarithmicTailRate T)

/--
The zeros admitted by a real cutoff `tau` but not by the natural cutoff `T`,
reindexed as a finite subset of the TS292 tail subtype.
-/
noncomputable def realHeightTailIndexFinset
    (T : Nat)
    (tau : Real) :
    Finset
      {rho : TS292.Goldbach.ConcreteNontrivialZero //
        Not (Membership.mem
          (TS292.Goldbach.concreteZerosUpToHeightSubtype T) rho)} :=
  (TS293.Goldbach.concreteZerosUpToRealHeight tau \
      TS292.Goldbach.concreteZerosUpToHeightSubtype T).attach.map
    { toFun := fun rho =>
        Subtype.mk rho.1 (Finset.mem_sdiff.mp rho.2).2
      inj' := by
        intro rho sigma h
        apply Subtype.ext
        have hValue :
            rho.1 = sigma.1 :=
          congrArg
            (fun z :
              {w : TS292.Goldbach.ConcreteNontrivialZero //
                Not (Membership.mem
                  (TS292.Goldbach.concreteZerosUpToHeightSubtype T) w)} =>
              z.1)
            h
        exact hValue }

theorem realHeightTailIndexFinset_norm_sum
    (x T : Nat)
    (tau : Real) :
    Finset.sum (realHeightTailIndexFinset T tau)
        (fun rho =>
          norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho.1)) =
      Finset.sum
        (TS293.Goldbach.concreteZerosUpToRealHeight tau \
          TS292.Goldbach.concreteZerosUpToHeightSubtype T)
        (fun rho =>
          norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho)) := by
  classical
  unfold realHeightTailIndexFinset
  rw [Finset.sum_map]
  simpa using
    (Finset.sum_attach
      (TS293.Goldbach.concreteZerosUpToRealHeight tau \
        TS292.Goldbach.concreteZerosUpToHeightSubtype T)
      (fun rho =>
        norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho)))

/-- Natural-height zeros are contained in every later real-height cutoff. -/
theorem concreteZerosUpToHeightSubtype_subset_realHeight
    (T : Nat)
    (tau : Real)
    (hTau : (T : Real) <= tau) :
    TS292.Goldbach.concreteZerosUpToHeightSubtype T <=
      TS293.Goldbach.concreteZerosUpToRealHeight tau := by
  intro rho hRho
  apply (TS293.Goldbach.mem_concreteZerosUpToRealHeight_iff tau rho).mpr
  exact
    ((TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff T rho).mp hRho).trans
      hTau

/-- The exact spectral adjustment is the negative sum over the added shell. -/
theorem spectralHeightCutoffAdjustment_eq_neg_sdiff
    (x T : Nat)
    (tau : Real)
    (hTau : (T : Real) <= tau) :
    TS293.Goldbach.spectralHeightCutoffAdjustment x T tau =
      -Finset.sum
        (TS293.Goldbach.concreteZerosUpToRealHeight tau \
          TS292.Goldbach.concreteZerosUpToHeightSubtype T)
        (TS292.Goldbach.infiniteZeroSpectralTerm x) := by
  classical
  have hSubset :=
    concreteZerosUpToHeightSubtype_subset_realHeight T tau hTau
  unfold TS293.Goldbach.spectralHeightCutoffAdjustment
    TS293.Goldbach.realHeightZeroContribution
    TS292.Goldbach.truncatedInfiniteZeroContribution
  rw [<- Finset.sum_sdiff hSubset]
  ring

/--
The spectral `T -> tau` adjustment is bounded unconditionally by the TS292
tail beginning at `T`.
-/
theorem spectralHeightCutoffAdjustment_norm_le
    (x T : Nat)
    (tau : Real)
    (hT : 1 <= T)
    (hTau : (T : Real) <= tau) :
    norm (TS293.Goldbach.spectralHeightCutoffAdjustment x T tau) <=
      spectralHeightAdjustmentEnvelope x T := by
  rw [spectralHeightCutoffAdjustment_eq_neg_sdiff x T tau hTau,
    norm_neg]
  calc
    norm
        (Finset.sum
          (TS293.Goldbach.concreteZerosUpToRealHeight tau \
            TS292.Goldbach.concreteZerosUpToHeightSubtype T)
          (TS292.Goldbach.infiniteZeroSpectralTerm x)) <=
        Finset.sum
          (TS293.Goldbach.concreteZerosUpToRealHeight tau \
            TS292.Goldbach.concreteZerosUpToHeightSubtype T)
          (fun rho =>
            norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho)) :=
      norm_sum_le _ _
    _ =
        Finset.sum (realHeightTailIndexFinset T tau)
          (fun rho =>
            norm (TS292.Goldbach.infiniteZeroSpectralTerm x rho.1)) :=
      (realHeightTailIndexFinset_norm_sum x T tau).symm
    _ <= spectralHeightAdjustmentEnvelope x T := by
      exact TS292.Goldbach.finiteInfiniteZeroSpectralTail_norm_sum_le
        x T hT (realHeightTailIndexFinset T tau)

/-- The same unconditional estimate for every quantitative clean contour. -/
theorem quantitativeContour_spectralHeightCutoffAdjustment_norm_le
    (x T : Nat)
    (hT : 1 <= T)
    (D : QuantitativelyCleanPerronContourData T) :
    norm
        (TS293.Goldbach.spectralHeightCutoffAdjustment
          x T D.tau) <=
      spectralHeightAdjustmentEnvelope x T :=
  spectralHeightCutoffAdjustment_norm_le x T D.tau hT D.height_ge

/--
Direct estimates for the bottom, top, and left integrals before contour
normalization.
-/
structure PerronNonRightSideBounds
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle) where
  bottomBound : Real
  topBound : Real
  leftBound : Real
  bottomBound_nonnegative : 0 <= bottomBound
  topBound_nonnegative : 0 <= topBound
  leftBound_nonnegative : 0 <= leftBound
  bottom_norm_le :
    norm (TS293.Goldbach.perronBottomIntegral x D) <= bottomBound
  top_norm_le :
    norm (TS293.Goldbach.perronTopForwardIntegral x D) <= topBound
  left_norm_le :
    norm (TS293.Goldbach.perronLeftForwardIntegral x D) <= leftBound

/-- Sum of the three raw side envelopes. -/
def PerronNonRightSideBounds.total
    {x : Nat}
    {D : TS293.Goldbach.PerronRectangle}
    (B : PerronNonRightSideBounds x D) :
    Real :=
  B.bottomBound + B.topBound + B.leftBound

theorem PerronNonRightSideBounds.total_nonnegative
    {x : Nat}
    {D : TS293.Goldbach.PerronRectangle}
    (B : PerronNonRightSideBounds x D) :
    0 <= B.total := by
  unfold PerronNonRightSideBounds.total
  linarith [B.bottomBound_nonnegative, B.topBound_nonnegative,
    B.leftBound_nonnegative]

/-- The oriented non-right boundary is controlled by the three side bounds. -/
theorem perronNonRightBoundaryIntegral_norm_le
    {x : Nat}
    {D : TS293.Goldbach.PerronRectangle}
    (B : PerronNonRightSideBounds x D) :
    norm (TS293.Goldbach.perronNonRightBoundaryIntegral x D) <=
      B.total := by
  unfold TS293.Goldbach.perronNonRightBoundaryIntegral
    PerronNonRightSideBounds.total
  calc
    norm
        (TS293.Goldbach.perronBottomIntegral x D -
          TS293.Goldbach.perronTopForwardIntegral x D -
            TS293.Goldbach.perronLeftForwardIntegral x D) <=
        norm
            (TS293.Goldbach.perronBottomIntegral x D -
              TS293.Goldbach.perronTopForwardIntegral x D) +
          norm (TS293.Goldbach.perronLeftForwardIntegral x D) :=
      norm_sub_le _ _
    _ <=
        (norm (TS293.Goldbach.perronBottomIntegral x D) +
          norm (TS293.Goldbach.perronTopForwardIntegral x D)) +
            norm (TS293.Goldbach.perronLeftForwardIntegral x D) := by
      gcongr
      exact norm_sub_le _ _
    _ <= B.bottomBound + B.topBound + B.leftBound := by
      linarith [B.bottom_norm_le, B.top_norm_le, B.left_norm_le]

/-- Normalized envelope for the three non-right sides. -/
noncomputable def PerronNonRightSideBounds.normalizedTotal
    {x : Nat}
    {D : TS293.Goldbach.PerronRectangle}
    (B : PerronNonRightSideBounds x D) :
    Real :=
  B.total / (2 * Real.pi)

theorem PerronNonRightSideBounds.normalizedTotal_nonnegative
    {x : Nat}
    {D : TS293.Goldbach.PerronRectangle}
    (B : PerronNonRightSideBounds x D) :
    0 <= B.normalizedTotal := by
  unfold PerronNonRightSideBounds.normalizedTotal
  exact div_nonneg B.total_nonnegative (by positivity)

/-- The contour normalization contributes exactly the factor `1/(2*pi)`. -/
theorem normalizedNonRightBoundary_norm_le
    {x : Nat}
    {D : TS293.Goldbach.PerronRectangle}
    (B : PerronNonRightSideBounds x D) :
    norm (TS293.Goldbach.normalizedNonRightBoundary x D) <=
      B.normalizedTotal := by
  unfold TS293.Goldbach.normalizedNonRightBoundary
    TS293.Goldbach.normalizeContourIntegral
    PerronNonRightSideBounds.normalizedTotal
  rw [norm_div]
  have hDenominator :
      norm (((2 * Real.pi : Real) : Complex) * I) =
        2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hDenominator]
  exact div_le_div_of_nonneg_right
    (perronNonRightBoundaryIntegral_norm_le B)
    (by positivity)

/--
The three genuinely analytic contour inputs that remain after the spectral
adjustment has been discharged.
-/
structure TriangleSplineContourComponentBounds
    (x T : Nat)
    (D : QuantitativelyCleanPerronContourData T)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory
      x D.toPerronRectangle) where
  exceptionalBound : Real
  rightCutoffBound : Real
  exceptionalBound_nonnegative : 0 <= exceptionalBound
  rightCutoffBound_nonnegative : 0 <= rightCutoffBound
  exceptional_norm_le :
    norm (TS293.Goldbach.exceptionalResidueContribution E) <=
      exceptionalBound
  nonRightSides :
    PerronNonRightSideBounds x D.toPerronRectangle
  rightCutoff_norm_le :
    norm
        (TS293.Goldbach.perronRightLineCutoffAdjustment
          x D.toPerronRectangle) <=
      rightCutoffBound

/-- Closed envelope assembled from the three contour inputs and TS292. -/
noncomputable def triangleSplineContourResidualEnvelope
    {x T : Nat}
    {D : QuantitativelyCleanPerronContourData T}
    {E : TS293.Goldbach.PerronExceptionalResidueInventory
      x D.toPerronRectangle}
    (B : TriangleSplineContourComponentBounds x T D E) :
    Real :=
  B.exceptionalBound +
    B.nonRightSides.normalizedTotal +
      B.rightCutoffBound +
        spectralHeightAdjustmentEnvelope x T

theorem spectralHeightAdjustmentEnvelope_nonnegative
    (x T : Nat) :
    0 <= spectralHeightAdjustmentEnvelope x T := by
  unfold spectralHeightAdjustmentEnvelope
  have hRate :
      0 <= TS292.Goldbach.logarithmicTailRate T := by
    unfold TS292.Goldbach.logarithmicTailRate
    have hLog :
        0 <= Real.log ((T : Real) + 2) := by
      apply Real.log_nonneg
      have hCast : 0 <= (T : Real) := Nat.cast_nonneg T
      linarith
    exact div_nonneg (by linarith) (Nat.cast_nonneg T)
  exact mul_nonneg
    (zero_le_one.trans (le_max_left 1 (x : Real)))
    (mul_nonneg
      TS292.Goldbach.infiniteZeroResidualTailConstant_nonnegative
      hRate)

theorem triangleSplineContourResidualEnvelope_nonnegative
    {x T : Nat}
    {D : QuantitativelyCleanPerronContourData T}
    {E : TS293.Goldbach.PerronExceptionalResidueInventory
      x D.toPerronRectangle}
    (B : TriangleSplineContourComponentBounds x T D E) :
    0 <= triangleSplineContourResidualEnvelope B := by
  unfold triangleSplineContourResidualEnvelope
  exact add_nonneg
    (add_nonneg
      (add_nonneg B.exceptionalBound_nonnegative
        B.nonRightSides.normalizedTotal_nonnegative)
      B.rightCutoffBound_nonnegative)
    (spectralHeightAdjustmentEnvelope_nonnegative x T)

/-- Complex residual bound obtained by exact componentwise assembly. -/
theorem triangleSplineContourResidualComplex_norm_le
    (x T : Nat)
    (hT : 1 <= T)
    (D : QuantitativelyCleanPerronContourData T)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory
      x D.toPerronRectangle)
    (B : TriangleSplineContourComponentBounds x T D E) :
    norm
        (TS293.Goldbach.triangleSplineContourResidualComplex
          x T D.toCleanPerronContourData E) <=
      triangleSplineContourResidualEnvelope B := by
  unfold TS293.Goldbach.triangleSplineContourResidualComplex
    triangleSplineContourResidualEnvelope
  have hSpectral :=
    quantitativeContour_spectralHeightCutoffAdjustment_norm_le x T hT D
  have hNonRight := normalizedNonRightBoundary_norm_le B.nonRightSides
  calc
    norm
        (TS293.Goldbach.exceptionalResidueContribution E -
          TS293.Goldbach.normalizedNonRightBoundary
            x D.toPerronRectangle +
          TS293.Goldbach.perronRightLineCutoffAdjustment
            x D.toPerronRectangle +
          TS293.Goldbach.spectralHeightCutoffAdjustment x T D.tau) <=
        norm
            (TS293.Goldbach.exceptionalResidueContribution E -
              TS293.Goldbach.normalizedNonRightBoundary
                x D.toPerronRectangle +
              TS293.Goldbach.perronRightLineCutoffAdjustment
                x D.toPerronRectangle) +
          norm
            (TS293.Goldbach.spectralHeightCutoffAdjustment x T D.tau) :=
      norm_add_le _ _
    _ <=
        (norm
            (TS293.Goldbach.exceptionalResidueContribution E -
              TS293.Goldbach.normalizedNonRightBoundary
                x D.toPerronRectangle) +
          norm
            (TS293.Goldbach.perronRightLineCutoffAdjustment
              x D.toPerronRectangle)) +
          norm
            (TS293.Goldbach.spectralHeightCutoffAdjustment x T D.tau) := by
      gcongr
      exact norm_add_le _ _
    _ <=
        ((norm (TS293.Goldbach.exceptionalResidueContribution E) +
          norm
            (TS293.Goldbach.normalizedNonRightBoundary
              x D.toPerronRectangle)) +
          norm
            (TS293.Goldbach.perronRightLineCutoffAdjustment
              x D.toPerronRectangle)) +
          norm
            (TS293.Goldbach.spectralHeightCutoffAdjustment x T D.tau) := by
      gcongr
      exact norm_sub_le _ _
    _ <=
        B.exceptionalBound +
          B.nonRightSides.normalizedTotal +
            B.rightCutoffBound +
              spectralHeightAdjustmentEnvelope x T := by
      linarith [B.exceptional_norm_le, hNonRight,
        B.rightCutoff_norm_le, hSpectral]

/-- Real TS293 residual bound obtained from the complex estimate. -/
theorem triangleSplineContourResidual_abs_le
    (x T : Nat)
    (hT : 1 <= T)
    (D : QuantitativelyCleanPerronContourData T)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory
      x D.toPerronRectangle)
    (B : TriangleSplineContourComponentBounds x T D E) :
    _root_.abs
        (TS293.Goldbach.triangleSplineContourResidual
          x T D.toCleanPerronContourData E) <=
      triangleSplineContourResidualEnvelope B := by
  exact
    (abs_re_le_abs
      (TS293.Goldbach.triangleSplineContourResidualComplex
        x T D.toCleanPerronContourData E)).trans
      (triangleSplineContourResidualComplex_norm_le x T hT D E B)

/-- Direct, fail-closed statement for the three unresolved contour bounds. -/
def TriangleSplineContourComponentEstimateStatement : Prop :=
  forall (x T : Nat)
    (_hT : 1 <= T)
    (D : QuantitativelyCleanPerronContourData T)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory
      x D.toPerronRectangle),
      Nonempty (TriangleSplineContourComponentBounds x T D E)

/-- TS294 ledger: exact closure boundary for the effective contour front. -/
structure QuantitativeCleanContourEstimatesLedger where
  ts293_contour_residual :
    TS293.Goldbach.TruncatedPerronContourResidualLedger
  fixed_rectangle_geometry_proved : True
  quantitative_clean_height_interface_defined : True
  right_edge_nonvanishing_proved : True
  non_right_side_assembly_proved : True
  contour_normalization_proved : True
  spectral_height_adjustment_bound_proved : True
  full_componentwise_residual_bound_proved : True
  quantitative_clean_height_existence_not_proved : True
  horizontal_log_derivative_bound_not_proved : True
  left_boundary_bound_not_proved : True
  right_line_cutoff_bound_not_proved : True
  exceptional_inventory_completeness_not_proved : True
  perron_inversion_not_proved : True
  meromorphic_rectangle_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

noncomputable def quantitativeCleanContourEstimatesLedger :
    QuantitativeCleanContourEstimatesLedger where
  ts293_contour_residual :=
    TS293.Goldbach.truncatedPerronContourResidualLedger
  fixed_rectangle_geometry_proved := True.intro
  quantitative_clean_height_interface_defined := True.intro
  right_edge_nonvanishing_proved := True.intro
  non_right_side_assembly_proved := True.intro
  contour_normalization_proved := True.intro
  spectral_height_adjustment_bound_proved := True.intro
  full_componentwise_residual_bound_proved := True.intro
  quantitative_clean_height_existence_not_proved := True.intro
  horizontal_log_derivative_bound_not_proved := True.intro
  left_boundary_bound_not_proved := True.intro
  right_line_cutoff_bound_not_proved := True.intro
  exceptional_inventory_completeness_not_proved := True.intro
  perron_inversion_not_proved := True.intro
  meromorphic_rectangle_residue_theorem_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS294
