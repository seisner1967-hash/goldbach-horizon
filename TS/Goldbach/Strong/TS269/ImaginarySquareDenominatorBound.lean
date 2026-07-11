import Mathlib.Tactic
import TS.Goldbach.Strong.TS268.NaturalScaleComplexPowerBound

/-!
# TS269 - Imaginary-Square Denominator Bound

TS268 isolated the multiplicity-denominator factor in the triangle-spline
spectral term.  This sprint proves the universal geometric estimate

`abs rho.im ^ 2 <= Complex.abs (rho * (rho + 1))`.

Consequently, in the high zone `1 <= abs rho.im`, the residual factor is at
most the multiplicity divided by `abs rho.im ^ 2`.  The concrete TS265 `Finset`
is partitioned into low and high zones.  The low zone is retained as an exact
finite mass, while the high zone receives the quadratic-decay envelope.

No lower bound for the first zero height, Riemann Hypothesis, multiplicity
estimate, zero-counting theorem, infinite summability, explicit formula,
Gallagher estimate, or Goldbach statement is used or proved.
-/

namespace TS269
namespace Goldbach

/-- Universal imaginary-square lower bound for the Mellin denominator. -/
theorem spectralDenominator_abs_ge_im_sq
    (rho : Complex) :
    abs rho.im ^ 2 <= Complex.abs (rho * (rho + 1)) := by
  have hRho : abs rho.im <= Complex.abs rho :=
    Complex.abs_im_le_abs rho
  have hRhoOne : abs rho.im <= Complex.abs (rho + 1) := by
    simpa using Complex.abs_im_le_abs (rho + 1)
  rw [map_mul]
  simpa only [pow_two] using
    mul_le_mul
      hRho
      hRhoOne
      (abs_nonneg rho.im)
      (Complex.abs.nonneg rho)

/-- Quadratically decaying residual envelope in the high imaginary zone. -/
noncomputable def highImaginaryResidualEnvelope
    (rho : Complex) :
    Real :=
  (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
      Real) /
    (abs rho.im ^ 2)

/-- The high-zone residual envelope is nonnegative. -/
theorem highImaginaryResidualEnvelope_nonnegative
    (rho : Complex) :
    0 <= highImaginaryResidualEnvelope rho :=
  div_nonneg
    (Nat.cast_nonneg _)
    (sq_nonneg (abs rho.im))

/-- In the high zone, the residual factor has quadratic imaginary decay. -/
theorem concreteMultiplicityDenominatorFactor_abs_le_highEnvelope
    (rho : Complex)
    (hHigh : 1 <= abs rho.im) :
    Complex.abs (TS268.Goldbach.concreteMultiplicityDenominatorFactor rho) <=
      highImaginaryResidualEnvelope rho := by
  have hImPos : 0 < abs rho.im := zero_lt_one.trans_le hHigh
  have hImSqPos : 0 < abs rho.im ^ 2 := pow_pos hImPos 2
  unfold TS268.Goldbach.concreteMultiplicityDenominatorFactor
    highImaginaryResidualEnvelope
  change
    norm
        (((TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
            Nat) : Complex) / (rho * (rho + 1))) <=
      (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
        Real) / abs rho.im ^ 2
  have hNormMultiplicity :
      norm
          ((TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
              Nat) : Complex) =
        (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
          Real) := by
    exact Complex.abs_natCast _
  rw [norm_div]
  rw [hNormMultiplicity]
  exact div_le_div_of_nonneg_left
    (Nat.cast_nonneg _)
    hImSqPos
    (spectralDenominator_abs_ge_im_sq rho)

/-- Low selected zeros, where no quadratic envelope is asserted. -/
noncomputable def concreteLowImaginaryZeroSelection
    (X : Nat) :
    Finset Complex :=
  (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X).filter
    (fun rho => abs rho.im < 1)

/-- High selected zeros, where quadratic decay is available. -/
noncomputable def concreteHighImaginaryZeroSelection
    (X : Nat) :
    Finset Complex :=
  (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X).filter
    (fun rho => 1 <= abs rho.im)

/-- Exact membership characterization for the low selection. -/
theorem mem_concreteLowImaginaryZeroSelection_iff
    (X : Nat)
    (rho : Complex) :
    Membership.mem (concreteLowImaginaryZeroSelection X) rho <->
      Membership.mem
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho /\
        abs rho.im < 1 := by
  simp [concreteLowImaginaryZeroSelection]

/-- Exact membership characterization for the high selection. -/
theorem mem_concreteHighImaginaryZeroSelection_iff
    (X : Nat)
    (rho : Complex) :
    Membership.mem (concreteHighImaginaryZeroSelection X) rho <->
      Membership.mem
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho /\
        1 <= abs rho.im := by
  simp [concreteHighImaginaryZeroSelection]

/-- The low and high selections are disjoint. -/
theorem concreteLowHighImaginaryZeroSelection_disjoint
    (X : Nat) :
    Disjoint
      (concreteLowImaginaryZeroSelection X)
      (concreteHighImaginaryZeroSelection X) := by
  apply Finset.disjoint_left.mpr
  intro rho hLow hHigh
  have hLt := (mem_concreteLowImaginaryZeroSelection_iff X rho).mp hLow |>.2
  have hLe := (mem_concreteHighImaginaryZeroSelection_iff X rho).mp hHigh |>.2
  linarith

/-- Membership in the full selection splits exactly into low or high zones. -/
theorem mem_concreteFiniteHeightTruncation_iff_low_or_high
    (X : Nat)
    (rho : Complex) :
    Membership.mem
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho <->
      Membership.mem (concreteLowImaginaryZeroSelection X) rho \/
        Membership.mem (concreteHighImaginaryZeroSelection X) rho := by
  constructor
  case mp =>
    intro hFull
    by_cases hLow : abs rho.im < 1
    case pos =>
      exact Or.inl
        ((mem_concreteLowImaginaryZeroSelection_iff X rho).mpr
          (And.intro hFull hLow))
    case neg =>
      exact Or.inr
        ((mem_concreteHighImaginaryZeroSelection_iff X rho).mpr
          (And.intro hFull (le_of_not_gt hLow)))
  case mpr =>
    intro h
    exact h.elim
      (fun hLow =>
        (mem_concreteLowImaginaryZeroSelection_iff X rho).mp hLow |>.1)
      (fun hHigh =>
        (mem_concreteHighImaginaryZeroSelection_iff X rho).mp hHigh |>.1)

/-- Exact weighted norm mass in the low imaginary zone. -/
noncomputable def concreteLowImaginaryWeightedNormMass
    (X : Nat) :
    Real :=
  Finset.sum
    (concreteLowImaginaryZeroSelection X)
    (fun rho =>
      Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho))

/-- Exact weighted norm mass in the high imaginary zone. -/
noncomputable def concreteHighImaginaryWeightedNormMass
    (X : Nat) :
    Real :=
  Finset.sum
    (concreteHighImaginaryZeroSelection X)
    (fun rho =>
      Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho))

/-- High-zone mass after applying scale and quadratic residual envelopes. -/
noncomputable def concreteHighImaginaryQuadraticEnvelopeMass
    (X : Nat) :
    Real :=
  Finset.sum
    (concreteHighImaginaryZeroSelection X)
    (fun rho => max 1 (X : Real) * highImaginaryResidualEnvelope rho)

/-- The TS266 norm mass splits exactly into low and high components. -/
theorem concreteFiniteHeightZeroNormMass_eq_low_add_high
    (X : Nat) :
    TS266.Goldbach.concreteFiniteHeightZeroNormMass X =
      concreteLowImaginaryWeightedNormMass X +
        concreteHighImaginaryWeightedNormMass X := by
  have hSum := Finset.sum_filter_add_sum_filter_not
    (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
    (fun rho : Complex => abs rho.im < 1)
    (fun rho =>
      Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho))
  simpa [TS266.Goldbach.concreteFiniteHeightZeroNormMass,
    concreteLowImaginaryWeightedNormMass,
    concreteHighImaginaryWeightedNormMass,
    concreteLowImaginaryZeroSelection,
    concreteHighImaginaryZeroSelection, not_lt] using hSum.symm

/-- The exact high-zone mass is bounded by the quadratic envelope mass. -/
theorem concreteHighImaginaryWeightedNormMass_le_quadraticEnvelopeMass
    (X : Nat) :
    concreteHighImaginaryWeightedNormMass X <=
      concreteHighImaginaryQuadraticEnvelopeMass X := by
  unfold concreteHighImaginaryWeightedNormMass
    concreteHighImaginaryQuadraticEnvelopeMass
  apply Finset.sum_le_sum
  intro rho hRho
  have hFull :=
    (mem_concreteHighImaginaryZeroSelection_iff X rho).mp hRho |>.1
  have hHigh :=
    (mem_concreteHighImaginaryZeroSelection_iff X rho).mp hRho |>.2
  have hZero :=
    (TS265.Goldbach.mem_concreteFiniteHeightTruncation_iff X rho).mp hFull |>.1
  rw [TS268.Goldbach.concreteFiniteHeightZeroTerm_abs_eq_scale_mul_factor]
  exact mul_le_mul
    (TS268.Goldbach.naturalScaleComplexPower_abs_le_max_one X rho hZero)
    (concreteMultiplicityDenominatorFactor_abs_le_highEnvelope rho hHigh)
    (Complex.abs.nonneg _)
    (zero_le_one.trans (le_max_left 1 (X : Real)))

/-- The full finite norm mass is bounded by low exact plus high quadratic. -/
theorem concreteFiniteHeightZeroNormMass_le_low_add_highQuadratic
    (X : Nat) :
    TS266.Goldbach.concreteFiniteHeightZeroNormMass X <=
      concreteLowImaginaryWeightedNormMass X +
        concreteHighImaginaryQuadraticEnvelopeMass X := by
  rw [concreteFiniteHeightZeroNormMass_eq_low_add_high X]
  exact add_le_add_left
    (concreteHighImaginaryWeightedNormMass_le_quadraticEnvelopeMass X) _

/-- Real zero contribution bounded by low exact plus high quadratic masses. -/
theorem concreteFiniteHeightZeroContribution_abs_le_low_add_highQuadratic
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      concreteLowImaginaryWeightedNormMass X +
        concreteHighImaginaryQuadraticEnvelopeMass X :=
  (TS266.Goldbach.concreteFiniteHeightZeroContribution_abs_le_normMass X).trans
    (concreteFiniteHeightZeroNormMass_le_low_add_highQuadratic X)

/-- Ledger recording the corrected imaginary-square denominator bound. -/
structure ImaginarySquareDenominatorBoundLedger where
  ts268_natural_scale :
    TS268.Goldbach.NaturalScaleComplexPowerBoundLedger

  universal_geometric_lower_bound :
    forall rho : Complex,
      abs rho.im ^ 2 <= Complex.abs (rho * (rho + 1))

  high_zone_residual_decay :
    forall rho : Complex,
      1 <= abs rho.im ->
        Complex.abs
            (TS268.Goldbach.concreteMultiplicityDenominatorFactor rho) <=
          highImaginaryResidualEnvelope rho

  low_zero_selection :
    Nat -> Finset Complex

  high_zero_selection :
    Nat -> Finset Complex

  low_high_partition :
    forall (X : Nat) (rho : Complex),
      Membership.mem
            (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho <->
        Membership.mem (low_zero_selection X) rho \/
          Membership.mem (high_zero_selection X) rho

  low_high_disjoint :
    forall X : Nat,
      Disjoint (low_zero_selection X) (high_zero_selection X)

  low_exact_high_quadratic_contribution_bound :
    forall X : Nat,
      abs
          (TS257.Goldbach.triangleSplineZeroContributionFunction
            TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
            TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
        concreteLowImaginaryWeightedNormMass X +
          concreteHighImaginaryQuadraticEnvelopeMass X

  low_zone_exclusion_not_proved : True
  effective_multiplicity_count_not_proved : True
  zero_counting_bound_not_proved : True
  zero_density_theorem_not_proved : True
  global_weighted_zero_summability_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS269 imaginary-square denominator ledger. -/
noncomputable def imaginarySquareDenominatorBoundLedger :
    ImaginarySquareDenominatorBoundLedger where
  ts268_natural_scale :=
    TS268.Goldbach.naturalScaleComplexPowerBoundLedger
  universal_geometric_lower_bound :=
    spectralDenominator_abs_ge_im_sq
  high_zone_residual_decay :=
    concreteMultiplicityDenominatorFactor_abs_le_highEnvelope
  low_zero_selection :=
    concreteLowImaginaryZeroSelection
  high_zero_selection :=
    concreteHighImaginaryZeroSelection
  low_high_partition :=
    mem_concreteFiniteHeightTruncation_iff_low_or_high
  low_high_disjoint :=
    concreteLowHighImaginaryZeroSelection_disjoint
  low_exact_high_quadratic_contribution_bound :=
    concreteFiniteHeightZeroContribution_abs_le_low_add_highQuadratic
  low_zone_exclusion_not_proved := True.intro
  effective_multiplicity_count_not_proved := True.intro
  zero_counting_bound_not_proved := True.intro
  zero_density_theorem_not_proved := True.intro
  global_weighted_zero_summability_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS269. -/
def ImaginarySquareDenominatorBoundTarget : Prop :=
  Nonempty ImaginarySquareDenominatorBoundLedger

/-- TS269 target: low exact and high quadratic zones are assembled. -/
theorem imaginarySquareDenominatorBoundTarget :
    ImaginarySquareDenominatorBoundTarget :=
  Nonempty.intro imaginarySquareDenominatorBoundLedger

end Goldbach
end TS269
