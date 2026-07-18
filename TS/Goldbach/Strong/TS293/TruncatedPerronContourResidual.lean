import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Dirichlet
import TS.Goldbach.Strong.TS255.FullyCorrectedExplicitFormulaAnalyticDecomposition
import TS.Goldbach.Strong.TS292.EffectiveInfiniteZeroTailConvergence

/-!
# TS293 - Truncated Perron Contour Residual

TS292 proves effective convergence of the zero series.  It does not control a
contour integral.  This sprint starts the separate contour front.

The module defines the concrete logarithmic-derivative Perron integrand, its
oriented rectangular boundary, exact real-height zero truncations, and a
non-tautological residual assembled from:

* the finite-to-infinite right-line cutoff;
* the three non-right sides of the rectangle;
* certified exceptional local residues;
* the exact spectral adjustment between heights `T` and `tau`.

Mathlib 4.15 supplies the von Mangoldt logarithmic-derivative identity on
`re s > 1` and rectangular Cauchy-Goursat, but no ready global theorem summing
meromorphic residues inside a rectangle.  Perron inversion and that
meromorphic contour shift are therefore explicit named statements.  Assuming
exactly those statements, the truncated explicit identity and its routing to
TS255 are proved.

The residual is never defined as the left side minus the desired right side.
This module does not prove clean-height existence, Perron inversion, the
meromorphic residue theorem, a contour bound, the infinite explicit formula,
Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS293
namespace Goldbach

open Complex Filter MeasureTheory Set
open scoped Interval

/-- The concrete triangle-spline Perron integrand. -/
noncomputable def triangleSplinePerronIntegrand
    (x : Nat)
    (s : Complex) :
    Complex :=
  (-deriv riemannZeta s / riemannZeta s) *
    (x : Complex) ^ s *
      TS257.Goldbach.triangleSplineMellinKernel s

/-- The same integrand written with the von Mangoldt L-series. -/
noncomputable def triangleSplineVonMangoldtLSeriesIntegrand
    (x : Nat)
    (s : Complex) :
    Complex :=
  LSeries
      (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex))
      s *
    (x : Complex) ^ s *
      TS257.Goldbach.triangleSplineMellinKernel s

/-- On the absolute-convergence half-plane, the two concrete integrands agree. -/
theorem triangleSplinePerronIntegrand_eq_vonMangoldtLSeries
    (x : Nat)
    {s : Complex}
    (hs : 1 < s.re) :
    triangleSplinePerronIntegrand x s =
      triangleSplineVonMangoldtLSeriesIntegrand x s := by
  unfold triangleSplinePerronIntegrand
    triangleSplineVonMangoldtLSeriesIntegrand
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]

/-- The zeta denominator is nonzero on every admissible right line. -/
theorem riemannZeta_ne_zero_on_perron_right_line
    {c t : Real}
    (hc : 1 < c) :
    Not (riemannZeta ((c : Complex) + (t : Complex) * I) = 0) := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simpa using hc

/-- Geometric data for a positively oriented truncated Perron rectangle. -/
structure PerronRectangle where
  left : Real
  right : Real
  tau : Real
  left_lt_neg_one : left < -1
  one_lt_right : 1 < right
  tau_pos : 0 < tau

/-- Bottom side, oriented from `left - i*tau` to `right - i*tau`. -/
noncomputable def perronBottomIntegral
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  intervalIntegral
    (fun sigma : Real =>
      triangleSplinePerronIntegrand x
        ((sigma : Complex) - (D.tau : Complex) * I))
    D.left
    D.right
    (volume : Measure Real)

/-- Top side, represented in the forward real direction. -/
noncomputable def perronTopForwardIntegral
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  intervalIntegral
    (fun sigma : Real =>
      triangleSplinePerronIntegrand x
        ((sigma : Complex) + (D.tau : Complex) * I))
    D.left
    D.right
    (volume : Measure Real)

/-- Right side including the differential `ds = i dt`. -/
noncomputable def perronRightIntegral
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  I * intervalIntegral
    (fun t : Real =>
      triangleSplinePerronIntegrand x
        ((D.right : Complex) + (t : Complex) * I))
    (-D.tau)
    D.tau
    (volume : Measure Real)

/-- Left side in the upward direction, before reversing its orientation. -/
noncomputable def perronLeftForwardIntegral
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  I * intervalIntegral
    (fun t : Real =>
      triangleSplinePerronIntegrand x
        ((D.left : Complex) + (t : Complex) * I))
    (-D.tau)
    D.tau
    (volume : Measure Real)

/-- The three non-right sides with their positive boundary orientations. -/
noncomputable def perronNonRightBoundaryIntegral
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  perronBottomIntegral x D -
    perronTopForwardIntegral x D -
      perronLeftForwardIntegral x D

/-- The complete positively oriented rectangular boundary integral. -/
noncomputable def perronRectangleBoundaryIntegral
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  perronRightIntegral x D +
    perronNonRightBoundaryIntegral x D

/-- Normalization by `2*pi*i`. -/
noncomputable def normalizeContourIntegral
    (z : Complex) :
    Complex :=
  z / ((2 * Real.pi : Real) * I)

/-- Normalized finite right-side value. -/
noncomputable def finitePerronRightValue
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  normalizeContourIntegral (perronRightIntegral x D)

/-- Normalized contribution of the other three sides. -/
noncomputable def normalizedNonRightBoundary
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  normalizeContourIntegral (perronNonRightBoundaryIntegral x D)

/-- Normalized complete boundary value. -/
noncomputable def normalizedPerronRectangleBoundary
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  finitePerronRightValue x D +
    normalizedNonRightBoundary x D

/-- The full right-line Perron integral on `Re(s) = c`. -/
noncomputable def fullPerronRightLineValue
    (x : Nat)
    (c : Real) :
    Complex :=
  normalizeContourIntegral
    (I * integral (volume : Measure Real)
      (fun t : Real =>
        triangleSplinePerronIntegrand x
          ((c : Complex) + (t : Complex) * I)))

/-- Concrete finite-height error on the Perron right line. -/
noncomputable def perronRightLineCutoffAdjustment
    (x : Nat)
    (D : PerronRectangle) :
    Complex :=
  fullPerronRightLineValue x D.right -
    finitePerronRightValue x D

/-- Exact zeros with real spectral height at most `tau`. -/
noncomputable def concreteZerosUpToRealHeight
    (tau : Real) :
    Finset TS292.Goldbach.ConcreteNontrivialZero :=
  (TS292.Goldbach.concreteZerosUpToHeightSubtype (Nat.ceil tau)).filter
    (fun rho => _root_.abs rho.1.im <= tau)

/-- Membership in the real-height truncation is exactly the real inequality. -/
theorem mem_concreteZerosUpToRealHeight_iff
    (tau : Real)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Iff
      (Membership.mem (concreteZerosUpToRealHeight tau) rho)
      (_root_.abs rho.1.im <= tau) := by
  classical
  rw [concreteZerosUpToRealHeight, Finset.mem_filter]
  constructor
  next =>
    exact fun h => h.2
  next =>
    intro h
    refine And.intro ?_ h
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (Nat.ceil tau) rho).mpr
    exact h.trans (Nat.le_ceil tau)

/-- At a natural height, the real and historical truncation finsets agree. -/
theorem concreteZerosUpToRealHeight_natCast
    (T : Nat) :
    concreteZerosUpToRealHeight (T : Real) =
      TS292.Goldbach.concreteZerosUpToHeightSubtype T := by
  classical
  ext rho
  rw [mem_concreteZerosUpToRealHeight_iff,
    TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff]

/-- Exact zero contribution cut at a real height. -/
noncomputable def realHeightZeroContribution
    (x : Nat)
    (tau : Real) :
    Complex :=
  Finset.sum (concreteZerosUpToRealHeight tau)
    (TS292.Goldbach.infiniteZeroSpectralTerm x)

/-- Exact adjustment from the natural cutoff `T` to the contour height `tau`. -/
noncomputable def spectralHeightCutoffAdjustment
    (x T : Nat)
    (tau : Real) :
    Complex :=
  TS292.Goldbach.truncatedInfiniteZeroContribution x T -
    realHeightZeroContribution x tau

/-- The spectral adjustment vanishes when the two cutoffs coincide. -/
theorem spectralHeightCutoffAdjustment_natCast
    (x T : Nat) :
    spectralHeightCutoffAdjustment x T (T : Real) = 0 := by
  unfold spectralHeightCutoffAdjustment
    realHeightZeroContribution
    TS292.Goldbach.truncatedInfiniteZeroContribution
  rw [concreteZerosUpToRealHeight_natCast]
  ring

/-- A certified local simple-pole coefficient of the Perron integrand. -/
structure PerronLocalResidueData
    (x : Nat)
    (p : Complex) where
  residue : Complex
  regularPart : Complex -> Complex
  regularPart_analytic : AnalyticAt Complex regularPart p
  principal_part :
    Filter.Eventually
      (fun z =>
        triangleSplinePerronIntegrand x z =
          residue / (z - p) + regularPart z)
      (nhdsWithin p (Set.compl {p}))

/-- Certified exceptional poles not represented by the nontrivial-zero sum. -/
structure PerronExceptionalResidueInventory
    (x : Nat)
    (D : PerronRectangle) where
  poles : Finset Complex
  residueData :
    forall p : {z : Complex // Membership.mem poles z},
      PerronLocalResidueData x p.1
  pole_in_open_rectangle :
    forall p : {z : Complex // Membership.mem poles z},
      D.left < p.1.re /\ p.1.re < D.right /\
        -D.tau < p.1.im /\ p.1.im < D.tau

/-- Concrete sum of all certified exceptional residues. -/
noncomputable def exceptionalResidueContribution
    {x : Nat}
    {D : PerronRectangle}
    (E : PerronExceptionalResidueInventory x D) :
    Complex :=
  Finset.sum E.poles.attach (fun p => (E.residueData p).residue)

/-- A clean height lies in `[T,T+1]` and avoids zeta zeros on non-right sides. -/
structure CleanPerronContourData
    (T : Nat)
    extends PerronRectangle where
  height_ge : (T : Real) <= tau
  height_le : tau <= T + 1
  zeta_nonzero_on_bottom :
    forall sigma : Real, left <= sigma -> sigma <= right ->
      Not (riemannZeta ((sigma : Complex) - (tau : Complex) * I) = 0)
  zeta_nonzero_on_top :
    forall sigma : Real, left <= sigma -> sigma <= right ->
      Not (riemannZeta ((sigma : Complex) + (tau : Complex) * I) = 0)
  zeta_nonzero_on_left :
    forall t : Real, -tau <= t -> t <= tau ->
      Not (riemannZeta ((left : Complex) + (t : Complex) * I) = 0)

/-- The still-open clean-height selection theorem. -/
def CleanPerronContourExistenceStatement : Prop :=
  forall T : Nat, 1 <= T -> Nonempty (CleanPerronContourData T)

/-- Mellin-Perron inversion on an infinite right line. -/
def TriangleSplinePerronInversionStatement : Prop :=
  forall (x : Nat) (c : Real),
    0 < x -> 1 < c ->
      ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
          Real) : Complex) =
        fullPerronRightLineValue x c

/-- Meromorphic rectangle shift with the exact residue inventory. -/
def TriangleSplineRectangleResidueStatement
    (x : Nat)
    (T : Nat)
    (D : CleanPerronContourData T)
    (E : PerronExceptionalResidueInventory x D.toPerronRectangle) :
    Prop :=
  normalizedPerronRectangleBoundary x D.toPerronRectangle =
    (x : Complex) / 2 -
      realHeightZeroContribution x D.tau +
        exceptionalResidueContribution E

/-- The concrete contour residual at scale `x` and natural cutoff `T`. -/
noncomputable def triangleSplineContourResidualComplex
    (x T : Nat)
    (D : CleanPerronContourData T)
    (E : PerronExceptionalResidueInventory x D.toPerronRectangle) :
    Complex :=
  exceptionalResidueContribution E -
    normalizedNonRightBoundary x D.toPerronRectangle +
      perronRightLineCutoffAdjustment x D.toPerronRectangle +
        spectralHeightCutoffAdjustment x T D.tau

/-- Real residual used by the TS206/TS255 explicit-formula convention. -/
noncomputable def triangleSplineContourResidual
    (x T : Nat)
    (D : CleanPerronContourData T)
    (E : PerronExceptionalResidueInventory x D.toPerronRectangle) :
    Real :=
  (triangleSplineContourResidualComplex x T D E).re

/-- The concrete main term produced by the pole at `s = 1`. -/
def triangleSplinePerronMainTerm
    (x : Nat) :
    Real :=
  (x : Real) / 2

/-- The finite right line equals the full line minus its concrete cutoff. -/
theorem fullPerronRightLineValue_eq_finite_add_cutoff
    (x : Nat)
    (D : PerronRectangle) :
    fullPerronRightLineValue x D.right =
      finitePerronRightValue x D +
        perronRightLineCutoffAdjustment x D := by
  unfold perronRightLineCutoffAdjustment
  ring

/-- Algebraic contour assembly from Perron inversion and the residue theorem. -/
theorem truncatedPerronExplicitIdentity_complex
    (x T : Nat)
    (hx : 0 < x)
    (D : CleanPerronContourData T)
    (E : PerronExceptionalResidueInventory x D.toPerronRectangle)
    (hPerron : TriangleSplinePerronInversionStatement)
    (hResidues : TriangleSplineRectangleResidueStatement x T D E) :
    ((TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x :
        Real) : Complex) =
      (x : Complex) / 2 -
        TS292.Goldbach.truncatedInfiniteZeroContribution x T +
          triangleSplineContourResidualComplex x T D E := by
  have hLine :=
    hPerron x D.right hx D.one_lt_right
  have hFinite :
      finitePerronRightValue x D.toPerronRectangle =
        (x : Complex) / 2 -
          realHeightZeroContribution x D.tau +
            exceptionalResidueContribution E -
              normalizedNonRightBoundary x D.toPerronRectangle := by
    unfold TriangleSplineRectangleResidueStatement
      normalizedPerronRectangleBoundary at hResidues
    linear_combination hResidues
  rw [hLine, fullPerronRightLineValue_eq_finite_add_cutoff, hFinite]
  unfold triangleSplineContourResidualComplex
    spectralHeightCutoffAdjustment
  ring

/-- Real truncated explicit identity in the TS206 sign convention. -/
theorem truncatedPerronExplicitIdentity
    (x T : Nat)
    (hx : 0 < x)
    (D : CleanPerronContourData T)
    (E : PerronExceptionalResidueInventory x D.toPerronRectangle)
    (hPerron : TriangleSplinePerronInversionStatement)
    (hResidues : TriangleSplineRectangleResidueStatement x T D E) :
    TS184.Goldbach.triangleSplineMathlibVonMangoldtWeightedSum x =
      triangleSplinePerronMainTerm x -
        (TS292.Goldbach.truncatedInfiniteZeroContribution x T).re +
          triangleSplineContourResidual x T D E := by
  have hComplex :=
    truncatedPerronExplicitIdentity_complex
      x T hx D E hPerron hResidues
  have hReal := congrArg Complex.re hComplex
  simpa [triangleSplinePerronMainTerm, triangleSplineContourResidual] using hReal

/-- A scale-indexed family of clean contours and certified exceptional poles. -/
structure TriangleSplineTruncatedContourFamily where
  height : Nat -> Nat
  contour : forall x : Nat, CleanPerronContourData (height x)
  exceptional :
    forall x : Nat,
      PerronExceptionalResidueInventory
        x
        (contour x).toPerronRectangle
  residue_theorem :
    forall x : Nat, 0 < x ->
      TriangleSplineRectangleResidueStatement
        x
        (height x)
        (contour x)
        (exceptional x)

/-- TS255 zero function from a chosen two-parameter truncation family. -/
noncomputable def truncatedContourZeroFunction
    (F : TriangleSplineTruncatedContourFamily) :
    TS255.Goldbach.ZeroContributionFunction :=
  fun x =>
    (TS292.Goldbach.truncatedInfiniteZeroContribution x (F.height x)).re

/-- TS255 residual function from the same concrete contour family. -/
noncomputable def truncatedContourResidualFunction
    (F : TriangleSplineTruncatedContourFamily) :
    TS255.Goldbach.ResidualTermFunction :=
  fun x =>
    triangleSplineContourResidual
      x
      (F.height x)
      (F.contour x)
      (F.exceptional x)

/-- Main-term compatibility required to route the contour identity into TS255. -/
def TriangleSplineHalfMainTermStatement
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) :
    Prop :=
  forall x : Nat, K.mainTermModel x = triangleSplinePerronMainTerm x

/-- The concrete truncated contour family populates the named TS255 identity. -/
theorem namedExplicitFormulaIdentity_of_truncatedContour
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (F : TriangleSplineTruncatedContourFamily)
    (hMain : TriangleSplineHalfMainTermStatement K)
    (hPerron : TriangleSplinePerronInversionStatement) :
    TS255.Goldbach.NamedExplicitFormulaIdentityStatement
      K
      (truncatedContourZeroFunction F)
      (truncatedContourResidualFunction F) := by
  intro x hx _hScale
  unfold TS206.Goldbach.triangleSplineExplicitFormulaIdentity
    TS206.Goldbach.triangleSplineExplicitFormulaLeftSide
    TS255.Goldbach.decomposedExplicitFormulaData
    truncatedContourZeroFunction
    truncatedContourResidualFunction
  rw [hMain x]
  exact truncatedPerronExplicitIdentity
    x
    (F.height x)
    hx
    (F.contour x)
    (F.exceptional x)
    hPerron
    (F.residue_theorem x hx)

/-- Ledger for the exact TS293 separation boundary. -/
structure TruncatedPerronContourResidualLedger where
  ts292_effective_infinite_tail :
    TS292.Goldbach.EffectiveInfiniteZeroTailConvergenceLedger
  perron_integrand_defined : True
  von_mangoldt_right_half_plane_rewrite :
    forall (x : Nat) (s : Complex), 1 < s.re ->
      triangleSplinePerronIntegrand x s =
        triangleSplineVonMangoldtLSeriesIntegrand x s
  oriented_rectangle_defined : True
  real_height_zero_cutoff_defined : True
  exceptional_residue_certificates_defined : True
  residual_is_non_tautological : True
  conditional_truncated_identity_proved : True
  ts255_routing_proved : True
  clean_height_existence_not_proved : True
  perron_inversion_not_proved : True
  meromorphic_rectangle_residue_theorem_not_proved : True
  contour_residual_bound_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

noncomputable def truncatedPerronContourResidualLedger :
    TruncatedPerronContourResidualLedger where
  ts292_effective_infinite_tail :=
    TS292.Goldbach.effectiveInfiniteZeroTailConvergenceLedger
  perron_integrand_defined := True.intro
  von_mangoldt_right_half_plane_rewrite :=
    triangleSplinePerronIntegrand_eq_vonMangoldtLSeries
  oriented_rectangle_defined := True.intro
  real_height_zero_cutoff_defined := True.intro
  exceptional_residue_certificates_defined := True.intro
  residual_is_non_tautological := True.intro
  conditional_truncated_identity_proved := True.intro
  ts255_routing_proved := True.intro
  clean_height_existence_not_proved := True.intro
  perron_inversion_not_proved := True.intro
  meromorphic_rectangle_residue_theorem_not_proved := True.intro
  contour_residual_bound_not_proved := True.intro
  infinite_explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end Goldbach
end TS293
