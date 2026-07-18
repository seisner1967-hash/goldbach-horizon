import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import TS.Goldbach.Strong.TS294.QuantitativeCleanContourEstimates

/-!
# TS295 - Strong Clean Heights and Log-Derivative Reduction

TS294 records a positive distance from the contour height to nearby zero
heights.  Positivity alone is not an asymptotic rate, and a pointwise distance
alone does not expose the multiplicity-weighted load seen by a logarithmic
derivative.

This module defines the finite reciprocal zero load

`sum m(rho) / |tau - |Im rho||`

through height `T+2`.  It proves that the rational finite-zero
logarithmic-derivative sum is bounded by this load on both horizontal sides
of the fixed TS294 rectangle.  It also isolates the nonvanishing quotient in
a local holomorphic-log Cauchy datum and proves that a sphere bound for the
logarithm controls `g'/g` at the center.

Thus the future horizontal estimate is reduced to two local quantities:

* a finite reciprocal zero load at a strongly clean height;
* a Cauchy bound for the holomorphic logarithm of the finite quotient.

No infinite Hadamard product is introduced.  This module does not construct a
strong clean height with a uniform rate, prove the required logarithm sphere
bound, estimate the left side or right cutoff, prove residue completeness,
Perron inversion, the meromorphic residue theorem, an infinite explicit
formula, Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS295
namespace Goldbach

open Complex Metric Set
open scoped BigOperators

/-- Multiplicity of a concrete nontrivial zero, in the TS264 convention. -/
noncomputable def concreteZeroMultiplicity
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Nat :=
  TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho.1

/-- Symmetric distance from a positive height to a zero ordinate. -/
noncomputable def symmetricZeroHeightGap
    (tau : Real)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Real :=
  _root_.abs (tau - _root_.abs rho.1.im)

/-- Nearby zeros used by the first horizontal contour estimate. -/
noncomputable def nearbyConcreteZeros
    (T : Nat) :
    Finset TS292.Goldbach.ConcreteNontrivialZero :=
  TS292.Goldbach.concreteZerosUpToHeightSubtype (T + 2)

/-- Exact multiplicity mass of the nearby finite zero family. -/
noncomputable def nearbyZeroMultiplicityMass
    (T : Nat) :
    Real :=
  Finset.sum (nearbyConcreteZeros T)
    (fun rho => (concreteZeroMultiplicity rho : Real))

/-- Exact reciprocal zero load at a candidate contour height. -/
noncomputable def reciprocalZeroLoad
    (T : Nat)
    (tau : Real) :
    Real :=
  Finset.sum (nearbyConcreteZeros T)
    (fun rho =>
      (concreteZeroMultiplicity rho : Real) /
        symmetricZeroHeightGap tau rho)

theorem nearbyZeroMultiplicityMass_nonnegative
    (T : Nat) :
    0 <= nearbyZeroMultiplicityMass T := by
  unfold nearbyZeroMultiplicityMass
  exact Finset.sum_nonneg fun rho _ => Nat.cast_nonneg _

theorem reciprocalZeroLoad_nonnegative
    (T : Nat)
    (tau : Real) :
    0 <= reciprocalZeroLoad T tau := by
  unfold reciprocalZeroLoad
  exact Finset.sum_nonneg fun rho _ =>
    div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

/--
A genuinely strong clean-height statement specifies rates depending on `T`,
not merely an unspecified positive number.
-/
def StrongCleanPerronContourExistenceStatement
    (delta loadEnvelope : Nat -> Real) :
    Prop :=
  forall T : Nat, 1 <= T ->
    Exists fun D : TS294.Goldbach.QuantitativelyCleanPerronContourData T =>
      delta T <= D.zeroSeparation /\
        reciprocalZeroLoad T D.tau <= loadEnvelope T

/--
The TS294 separation controls every denominator occurring in the nearby
reciprocal load.
-/
theorem quantitativeClean_separation_le_gap
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {rho : TS292.Goldbach.ConcreteNontrivialZero}
    (hRho : Membership.mem (nearbyConcreteZeros T) rho) :
    D.zeroSeparation <= symmetricZeroHeightGap D.tau rho := by
  apply D.separated_from_nearby_zeros rho
  exact
    (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
      (T + 2) rho).mp hRho |>.trans_eq (by
        push_cast
        ring)

theorem quantitativeClean_gap_positive
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {rho : TS292.Goldbach.ConcreteNontrivialZero}
    (hRho : Membership.mem (nearbyConcreteZeros T) rho) :
    0 < symmetricZeroHeightGap D.tau rho :=
  D.zeroSeparation_pos.trans_le
    (quantitativeClean_separation_le_gap D hRho)

/-- A positive separation yields the elementary mass-over-gap load bound. -/
theorem reciprocalZeroLoad_le_mass_div_separation
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T) :
    reciprocalZeroLoad T D.tau <=
      nearbyZeroMultiplicityMass T / D.zeroSeparation := by
  unfold reciprocalZeroLoad nearbyZeroMultiplicityMass
  calc
    Finset.sum (nearbyConcreteZeros T)
        (fun rho =>
          (concreteZeroMultiplicity rho : Real) /
            symmetricZeroHeightGap D.tau rho) <=
      Finset.sum (nearbyConcreteZeros T)
        (fun rho =>
          (concreteZeroMultiplicity rho : Real) /
            D.zeroSeparation) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact div_le_div_of_nonneg_left
        (Nat.cast_nonneg _)
        D.zeroSeparation_pos
        (quantitativeClean_separation_le_gap D hRho)
    _ =
        Finset.sum (nearbyConcreteZeros T)
          (fun rho => (concreteZeroMultiplicity rho : Real)) /
            D.zeroSeparation := by
      rw [Finset.sum_div]

/-- One rational term of the finite logarithmic derivative. -/
noncomputable def finiteZeroLogDerivativeTerm
    (s : Complex)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    Complex :=
  (concreteZeroMultiplicity rho : Complex) / (s - rho.1)

/-- Finite rational logarithmic-derivative contribution of nearby zeros. -/
noncomputable def finiteZeroLogDerivativeSum
    (T : Nat)
    (s : Complex) :
    Complex :=
  Finset.sum (nearbyConcreteZeros T)
    (finiteZeroLogDerivativeTerm s)

/-- The symmetric height gap is bounded by the top-side denominator. -/
theorem symmetricZeroHeightGap_le_norm_top
    (sigma tau : Real)
    (hTau : 0 <= tau)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    symmetricZeroHeightGap tau rho <=
      norm
        ((sigma : Complex) + (tau : Complex) * I - rho.1) := by
  have hReal :
      _root_.abs (tau - _root_.abs rho.1.im) <=
        _root_.abs (tau - rho.1.im) := by
    simpa [_root_.abs_of_nonneg hTau] using
      (abs_abs_sub_abs_le_abs_sub tau rho.1.im)
  have hImag :
      _root_.abs (tau - rho.1.im) <=
        Complex.abs
          ((sigma : Complex) + (tau : Complex) * I - rho.1) := by
    simpa using
      (abs_im_le_abs
        ((sigma : Complex) + (tau : Complex) * I - rho.1))
  exact hReal.trans hImag

/-- The symmetric height gap is bounded by the bottom-side denominator. -/
theorem symmetricZeroHeightGap_le_norm_bottom
    (sigma tau : Real)
    (hTau : 0 <= tau)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    symmetricZeroHeightGap tau rho <=
      norm
        ((sigma : Complex) - (tau : Complex) * I - rho.1) := by
  have hReal :
      _root_.abs (tau - _root_.abs rho.1.im) <=
        _root_.abs (tau + rho.1.im) := by
    simpa [_root_.abs_of_nonneg hTau, abs_neg] using
      (abs_abs_sub_abs_le_abs_sub tau (-rho.1.im))
  have hImag :
      _root_.abs (tau + rho.1.im) <=
        Complex.abs
          ((sigma : Complex) - (tau : Complex) * I - rho.1) := by
    have h :=
      abs_im_le_abs
        ((sigma : Complex) - (tau : Complex) * I - rho.1)
    have hImaginaryPart :
        (((sigma : Complex) - (tau : Complex) * I - rho.1).im) =
          -tau - rho.1.im := by
      simp
    calc
      _root_.abs (tau + rho.1.im) =
          _root_.abs (-(tau + rho.1.im)) := by
            rw [_root_.abs_neg]
      _ = _root_.abs (-tau - rho.1.im) := by
            congr 1
            ring
      _ <= Complex.abs
          ((sigma : Complex) - (tau : Complex) * I - rho.1) := by
            rw [hImaginaryPart] at h
            exact h
  exact hReal.trans hImag

theorem finiteZeroLogDerivativeTerm_norm_le_gap
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    {rho : TS292.Goldbach.ConcreteNontrivialZero}
    (hRho : Membership.mem (nearbyConcreteZeros T) rho)
    {s : Complex}
    (hGap : symmetricZeroHeightGap D.tau rho <= norm (s - rho.1)) :
    norm (finiteZeroLogDerivativeTerm s rho) <=
      (concreteZeroMultiplicity rho : Real) /
        symmetricZeroHeightGap D.tau rho := by
  unfold finiteZeroLogDerivativeTerm
  rw [norm_div]
  have hNormCast :
      norm (concreteZeroMultiplicity rho : Complex) =
        (concreteZeroMultiplicity rho : Real) := by
    simp
  rw [hNormCast]
  exact div_le_div_of_nonneg_left
    (Nat.cast_nonneg _)
    (quantitativeClean_gap_positive D hRho)
    hGap

/-- The finite-zero rational sum is controlled on the top horizontal side. -/
theorem finiteZeroLogDerivativeSum_norm_le_reciprocalLoad_top
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real) :
    norm
        (finiteZeroLogDerivativeSum T
          ((sigma : Complex) + (D.tau : Complex) * I)) <=
      reciprocalZeroLoad T D.tau := by
  unfold finiteZeroLogDerivativeSum reciprocalZeroLoad
  calc
    norm
        (Finset.sum (nearbyConcreteZeros T)
          (finiteZeroLogDerivativeTerm
            ((sigma : Complex) + (D.tau : Complex) * I))) <=
      Finset.sum (nearbyConcreteZeros T)
        (fun rho =>
          norm
            (finiteZeroLogDerivativeTerm
              ((sigma : Complex) + (D.tau : Complex) * I) rho)) :=
      norm_sum_le _ _
    _ <=
      Finset.sum (nearbyConcreteZeros T)
        (fun rho =>
          (concreteZeroMultiplicity rho : Real) /
            symmetricZeroHeightGap D.tau rho) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact finiteZeroLogDerivativeTerm_norm_le_gap D hRho
        (symmetricZeroHeightGap_le_norm_top
          sigma D.tau D.tau_pos.le rho)

/-- The finite-zero rational sum is controlled on the bottom horizontal side. -/
theorem finiteZeroLogDerivativeSum_norm_le_reciprocalLoad_bottom
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real) :
    norm
        (finiteZeroLogDerivativeSum T
          ((sigma : Complex) - (D.tau : Complex) * I)) <=
      reciprocalZeroLoad T D.tau := by
  unfold finiteZeroLogDerivativeSum reciprocalZeroLoad
  calc
    norm
        (Finset.sum (nearbyConcreteZeros T)
          (finiteZeroLogDerivativeTerm
            ((sigma : Complex) - (D.tau : Complex) * I))) <=
      Finset.sum (nearbyConcreteZeros T)
        (fun rho =>
          norm
            (finiteZeroLogDerivativeTerm
              ((sigma : Complex) - (D.tau : Complex) * I) rho)) :=
      norm_sum_le _ _
    _ <=
      Finset.sum (nearbyConcreteZeros T)
        (fun rho =>
          (concreteZeroMultiplicity rho : Real) /
            symmetricZeroHeightGap D.tau rho) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact finiteZeroLogDerivativeTerm_norm_le_gap D hRho
        (symmetricZeroHeightGap_le_norm_bottom
          sigma D.tau D.tau_pos.le rho)

/--
Local Cauchy data for a holomorphic logarithm of a nonvanishing quotient.
The global equality field is intentionally localizable by choosing `g` to be
the relevant restriction or extension.
-/
structure LocalHolomorphicLogCauchyData
    (g : Complex -> Complex)
    (center : Complex) where
  radius : Real
  radius_pos : 0 < radius
  logarithm : Complex -> Complex
  logarithm_diffContOnCl :
    DiffContOnCl Complex logarithm (ball center radius)
  exp_logarithm_eq :
    forall z : Complex, Membership.mem (ball center radius) z ->
      Complex.exp (logarithm z) = g z
  sphereBound : Real
  logarithm_norm_le :
    forall z : Complex, Membership.mem (sphere center radius) z ->
      norm (logarithm z) <= sphereBound

/-- Cauchy's estimate controls the derivative of the holomorphic logarithm. -/
theorem LocalHolomorphicLogCauchyData.logarithm_deriv_norm_le
    {g : Complex -> Complex}
    {center : Complex}
    (D : LocalHolomorphicLogCauchyData g center) :
    norm (deriv D.logarithm center) <= D.sphereBound / D.radius :=
  norm_deriv_le_of_forall_mem_sphere_norm_le
    D.radius_pos D.logarithm_diffContOnCl D.logarithm_norm_le

/-- The quotient logarithmic derivative is the derivative of its log. -/
theorem LocalHolomorphicLogCauchyData.logDerivative_eq
    {g : Complex -> Complex}
    {center : Complex}
    (D : LocalHolomorphicLogCauchyData g center) :
    deriv g center / g center = deriv D.logarithm center := by
  have hDifferentiable :
      DifferentiableAt Complex D.logarithm center :=
    D.logarithm_diffContOnCl.differentiableAt
      isOpen_ball (mem_ball_self D.radius_pos)
  have hDeriv :
      deriv g center =
        Complex.exp (D.logarithm center) *
          deriv D.logarithm center := by
    have hEventually :
        Filter.EventuallyEq (nhds center) g
          (fun z => Complex.exp (D.logarithm z)) := by
      filter_upwards [Metric.ball_mem_nhds center D.radius_pos] with z hz
      exact (D.exp_logarithm_eq z hz).symm
    exact
      (hDifferentiable.hasDerivAt.cexp.congr_of_eventuallyEq
        hEventually).deriv
  rw [hDeriv, show g center = Complex.exp (D.logarithm center) from
    (D.exp_logarithm_eq center (mem_ball_self D.radius_pos)).symm]
  field_simp [Complex.exp_ne_zero]

/-- Closed local bound for the nonvanishing quotient logarithmic derivative. -/
theorem LocalHolomorphicLogCauchyData.logDerivative_norm_le
    {g : Complex -> Complex}
    {center : Complex}
    (D : LocalHolomorphicLogCauchyData g center) :
    norm (deriv g center / g center) <= D.sphereBound / D.radius := by
  rw [D.logDerivative_eq]
  exact D.logarithm_deriv_norm_le

/--
An exact finite-factor plus quotient decomposition reduces immediately to the
reciprocal load and the local Cauchy quotient bound.
-/
theorem horizontalLogDerivative_norm_le
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real)
    (q : Complex)
    {target : Complex}
    (hTarget :
      target =
        finiteZeroLogDerivativeSum T
          ((sigma : Complex) + (D.tau : Complex) * I) + q) :
    norm target <= reciprocalZeroLoad T D.tau + norm q := by
  rw [hTarget]
  exact (norm_add_le _ _).trans
    (add_le_add
      (finiteZeroLogDerivativeSum_norm_le_reciprocalLoad_top D sigma)
      le_rfl)

/-- Bottom-side version of the exact finite-factor reduction. -/
theorem horizontalLogDerivative_norm_le_bottom
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real)
    (q : Complex)
    {target : Complex}
    (hTarget :
      target =
        finiteZeroLogDerivativeSum T
          ((sigma : Complex) - (D.tau : Complex) * I) + q) :
    norm target <= reciprocalZeroLoad T D.tau + norm q := by
  rw [hTarget]
  exact (norm_add_le _ _).trans
    (add_le_add
      (finiteZeroLogDerivativeSum_norm_le_reciprocalLoad_bottom D sigma)
      le_rfl)

/--
The exact local finite-factor decomposition closes once the nonvanishing
quotient is supplied with a holomorphic logarithm and a sphere bound.
-/
theorem horizontalLogDerivative_norm_le_reciprocalLoad_add_cauchy
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real)
    (g : Complex -> Complex)
    (L : LocalHolomorphicLogCauchyData g
      ((sigma : Complex) + (D.tau : Complex) * I))
    {target : Complex}
    (hTarget :
      target =
        finiteZeroLogDerivativeSum T
          ((sigma : Complex) + (D.tau : Complex) * I) +
            deriv g ((sigma : Complex) + (D.tau : Complex) * I) /
              g ((sigma : Complex) + (D.tau : Complex) * I)) :
    norm target <=
      reciprocalZeroLoad T D.tau + L.sphereBound / L.radius := by
  exact
    (horizontalLogDerivative_norm_le D sigma _ hTarget).trans
      (add_le_add_left L.logDerivative_norm_le _)

/-- Bottom-side finite-factor plus local-Cauchy closure. -/
theorem horizontalLogDerivative_norm_le_reciprocalLoad_add_cauchy_bottom
    {T : Nat}
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real)
    (g : Complex -> Complex)
    (L : LocalHolomorphicLogCauchyData g
      ((sigma : Complex) - (D.tau : Complex) * I))
    {target : Complex}
    (hTarget :
      target =
        finiteZeroLogDerivativeSum T
          ((sigma : Complex) - (D.tau : Complex) * I) +
            deriv g ((sigma : Complex) - (D.tau : Complex) * I) /
              g ((sigma : Complex) - (D.tau : Complex) * I)) :
    norm target <=
      reciprocalZeroLoad T D.tau + L.sphereBound / L.radius := by
  exact
    (horizontalLogDerivative_norm_le_bottom D sigma _ hTarget).trans
      (add_le_add_left L.logDerivative_norm_le _)

/--
Named xi input still needed to identify the exact finite factor and quotient
logarithmic derivatives.  The later passage to `-zeta'/zeta` must add the
explicit elementary completion factors; it is not hidden in this statement.
-/
def XiFiniteFactorLogDerivativeStatement : Prop :=
  forall (T : Nat)
    (D : TS294.Goldbach.QuantitativelyCleanPerronContourData T)
    (sigma : Real),
      D.left <= sigma -> sigma <= D.right ->
        Exists fun q : Complex =>
          deriv TS282.Goldbach.riemannXiCandidate
                ((sigma : Complex) + (D.tau : Complex) * I) /
              TS282.Goldbach.riemannXiCandidate
                ((sigma : Complex) + (D.tau : Complex) * I) =
            finiteZeroLogDerivativeSum T
                ((sigma : Complex) + (D.tau : Complex) * I) + q

/-- TS295 ledger: exact closure boundary for the local log-derivative front. -/
structure StrongCleanHeightLogDerivativeReductionLedger where
  ts294_quantitative_assembly :
    TS294.Goldbach.QuantitativeCleanContourEstimatesLedger
  reciprocal_zero_load_defined : True
  mass_over_separation_bound_proved : True
  top_horizontal_finite_sum_bound_proved : True
  bottom_horizontal_finite_sum_bound_proved : True
  local_holomorphic_log_cauchy_bound_proved : True
  infinite_hadamard_product_not_used : True
  strong_clean_height_rate_not_proved : True
  reciprocal_load_asymptotic_not_proved : True
  finite_factor_log_derivative_identity_not_proved : True
  quotient_logarithm_sphere_bound_not_proved : True
  left_boundary_bound_not_proved : True
  right_line_cutoff_bound_not_proved : True
  exceptional_inventory_completeness_not_proved : True
  perron_inversion_not_proved : True
  meromorphic_rectangle_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

noncomputable def strongCleanHeightLogDerivativeReductionLedger :
    StrongCleanHeightLogDerivativeReductionLedger where
  ts294_quantitative_assembly :=
    TS294.Goldbach.quantitativeCleanContourEstimatesLedger
  reciprocal_zero_load_defined := True.intro
  mass_over_separation_bound_proved := True.intro
  top_horizontal_finite_sum_bound_proved := True.intro
  bottom_horizontal_finite_sum_bound_proved := True.intro
  local_holomorphic_log_cauchy_bound_proved := True.intro
  infinite_hadamard_product_not_used := True.intro
  strong_clean_height_rate_not_proved := True.intro
  reciprocal_load_asymptotic_not_proved := True.intro
  finite_factor_log_derivative_identity_not_proved := True.intro
  quotient_logarithm_sphere_bound_not_proved := True.intro
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
end TS295
